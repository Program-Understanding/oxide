"""Optional Phoenix / OpenTelemetry tracing for the native Oxide agentic RE feature.

Mirrors the reference (run_crewai.py): when enabled it emits OpenInference spans so the whole
run is visible in a LOCAL Arize Phoenix UI (http://localhost:6006, no account):

  AGENT  binre.run                      (the whole question)
   ├─ CHAIN planner: decompose          (subtasks)
   ├─ CHAIN worker Sx  ── TOOL spans    (each Oxide tool call: name/input/output)
   │                   ── LLM spans     (litellm auto-instrumented)
   ├─ CHAIN adjudicate ── TOOL/LLM spans
   └─ CHAIN synthesize

Everything here is a NO-OP unless `setup_phoenix()` succeeds, so importing/using it costs
nothing when tracing is off or the optional packages are absent. Enable per-run with the
plugin's --phoenix opt.

Install (already present in this env):
  pip install arize-phoenix openinference-instrumentation-litellm
  phoenix serve     # start the local UI first, then run with --phoenix
"""
from __future__ import annotations

import json
import os
import threading
import time
from contextlib import contextmanager

_ENABLED = False
_tracer = None
try:  # opentelemetry is a transitive dep of phoenix; guard anyway
    from opentelemetry import trace as _otel
except Exception:  # noqa: BLE001
    _otel = None

# --- file-trace sink (independent of the Phoenix server): write every AGENT/CHAIN/TOOL span as
# one JSON line, so a batch run can save a self-contained trace per sample without a live UI. ---
_TRACE_FH = None
_TRACE_LOCK = threading.Lock()
_SEQ = [0]


def set_trace_file(path):
    """Begin/*end* file tracing. path=<file> opens a fresh JSONL trace; path=None closes it.
    Spans are appended regardless of whether Phoenix is enabled."""
    global _TRACE_FH
    with _TRACE_LOCK:
        if _TRACE_FH is not None:
            try:
                _TRACE_FH.close()
            except Exception:  # noqa: BLE001
                pass
            _TRACE_FH = None
        if path:
            _TRACE_FH = open(path, "w")
            _SEQ[0] = 0


def file_tracing() -> bool:
    return _TRACE_FH is not None


def _file_emit(kind, name, inp, out, t0):
    if _TRACE_FH is None:
        return
    rec = {"kind": kind, "name": name,
           "input": str(inp)[:8000], "output": str(out)[:20000],
           "t": round(time.time(), 3), "dur": round(time.time() - t0, 3),
           "thread": threading.current_thread().name}
    with _TRACE_LOCK:
        if _TRACE_FH is None:
            return
        rec["seq"] = _SEQ[0]
        _SEQ[0] += 1
        try:
            _TRACE_FH.write(json.dumps(rec, default=str) + "\n")
            _TRACE_FH.flush()
        except Exception:  # noqa: BLE001
            pass


def record_llm(name, request, response, t0):
    """Append one LLM request/response record to the file trace (no-op if file tracing is off).
    Used by llm.py to capture every model call (messages in, content/tool_calls out)."""
    if _TRACE_FH is None:
        return
    _file_emit("LLM", name, request, response, t0)


def note(tag, data):
    """Append a structured, named event to the file trace (no-op if file tracing is off). Unlike
    span/tool/LLM records (which stringify their output), this stores `data` as a real JSON object
    so plan-level events — the PLAN, each task's assignment, ASSESS, REPLAN, REVISE, the ANSWER —
    are machine-readable and the run can be replayed crystal-clearly."""
    if _TRACE_FH is None:
        return
    rec = {"kind": "NOTE", "name": tag, "data": data,
           "t": round(time.time(), 3), "thread": threading.current_thread().name}
    with _TRACE_LOCK:
        if _TRACE_FH is None:
            return
        rec["seq"] = _SEQ[0]
        _SEQ[0] += 1
        try:
            _TRACE_FH.write(json.dumps(rec, default=str) + "\n")
            _TRACE_FH.flush()
        except Exception:  # noqa: BLE001
            pass


def setup_phoenix(endpoint: str = "http://localhost:6006/v1/traces") -> bool:
    """Register a LOCAL Phoenix OTel exporter and auto-instrument litellm. Returns True on
    success. Safe to call more than once."""
    global _ENABLED, _tracer
    os.environ["OTEL_SDK_DISABLED"] = "false"
    try:
        from phoenix.otel import register
        register(endpoint=endpoint, auto_instrument=True)  # patches installed OpenInference instrumentors
        _tracer = _otel.get_tracer("oxide-agentic-re") if _otel else None
        _ENABLED = _tracer is not None
        print(f"[phoenix] local tracing -> {endpoint}  (open http://localhost:6006)")
        return _ENABLED
    except Exception as e:  # noqa: BLE001
        print(f"[phoenix] disabled — {str(e)[:140]}\n"
              "  install: pip install arize-phoenix openinference-instrumentation-litellm ; "
              "then run `phoenix serve`")
        return False


def enabled() -> bool:
    return _ENABLED and _tracer is not None


@contextmanager
def span(name: str, kind: str = "CHAIN", inp: str = ""):
    """Open an OpenInference span (Phoenix) and/or a file-trace record; yields a setter for the
    span's output.value. No-op only when BOTH Phoenix and file tracing are off."""
    if not enabled() and _TRACE_FH is None:
        yield (lambda _out: None)
        return
    t0 = time.time()
    box = {"out": ""}
    if enabled():
        with _tracer.start_as_current_span(name) as s:
            s.set_attribute("openinference.span.kind", kind)
            if inp:
                s.set_attribute("input.value", str(inp)[:4000])

            def setter(out):
                box["out"] = out
                s.set_attribute("output.value", str(out)[:6000])
            try:
                yield setter
            finally:
                _file_emit(kind, name, inp, box["out"], t0)
    else:
        try:
            yield (lambda out: box.__setitem__("out", out))
        finally:
            _file_emit(kind, name, inp, box["out"], t0)


@contextmanager
def tool_span(name: str, args: dict):
    """TOOL span for one Oxide-backed tool call (Phoenix and/or file trace)."""
    if not enabled() and _TRACE_FH is None:
        yield (lambda _out: None)
        return
    t0 = time.time()
    box = {"out": ""}
    try:
        argstr = json.dumps(args)
    except Exception:  # noqa: BLE001
        argstr = str(args)
    if enabled():
        with _tracer.start_as_current_span(name) as s:
            s.set_attribute("openinference.span.kind", "TOOL")
            s.set_attribute("tool.name", name)
            s.set_attribute("input.value", argstr)
            s.set_attribute("input.mime_type", "application/json")

            def setter(out):
                box["out"] = out
                s.set_attribute("output.value", str(out)[:6000])
            try:
                yield setter
            finally:
                _file_emit("TOOL", name, argstr, box["out"], t0)
    else:
        try:
            yield (lambda out: box.__setitem__("out", out))
        finally:
            _file_emit("TOOL", name, argstr, box["out"], t0)
