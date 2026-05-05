from __future__ import annotations

import asyncio
import atexit
import json
import logging
import os
import re
import shutil
import textwrap
import time
import unicodedata
from typing import Any, Dict, List, Literal, Optional, Set, Tuple, TypedDict

from deepagents import create_deep_agent
from deepagents.backends import StateBackend
from deepagents.backends.protocol import EditResult, WriteResult
from deepagents.backends.utils import create_file_data
from langchain_ollama import ChatOllama
from langchain_core.messages import HumanMessage, SystemMessage
from langgraph.checkpoint.memory import MemorySaver
from langgraph.graph import END, START, StateGraph

from oxide.core import oxide as oxide
from oxide.core.oxide import api, progress
from oxide.plugins import drift

try:
    from pydantic import BaseModel, Field
except ImportError:
    class BaseModel:  # type: ignore[no-redef]
        def __init__(self, **data: Any) -> None:
            for key, value in data.items():
                setattr(self, key, value)

        def model_dump(self) -> Dict[str, Any]:
            return dict(self.__dict__)

    _FIELD_UNSET = object()

    def Field(  # type: ignore[no-redef]
        default: Any = _FIELD_UNSET,
        **_kwargs: Any,
    ) -> Any:
        return ... if default is _FIELD_UNSET else default



logging.getLogger("httpx").setLevel(logging.WARNING)

NAME = "llm_drift_deep_agent"
logger = logging.getLogger(NAME)
_formatter = logging.Formatter(
    "[%(asctime)s] %(levelname)s %(name)s: %(message)s",
    "%H:%M:%S",
)
if not logger.handlers:
    _handler = logging.StreamHandler()
    _handler.setFormatter(_formatter)
    logger.addHandler(_handler)
logger.setLevel(logging.INFO)

_DEFAULT_MODEL = "qwen3-coder-next:ca06e9e4087c"

_DEFAULT_REQUEST_TIMEOUT_S = float(os.getenv("DELT_DEEP_AGENT_REQUEST_TIMEOUT_S", "150"))
_SUPPORTED_ABLATION_AXES = ("diff", "first_pass")
_ANALYST_TOKEN_TIMEOUT_S = 30.0
_ANALYST_TOTAL_TIMEOUT_S = 300.0

LLM: Optional[ChatOllama] = None
ANALYST_LLM: Optional[ChatOllama] = None
_ASYNC_RUNNER: Optional[asyncio.Runner] = None
TRIAGE_GRAPH: Any = None

DEEP_AGENT_SYS = """\
You are a security analyst who is an expert in binary reverse engineering and security.
You are given a unified diff of decompiled code for a single function.

Determine whether this update injects a deliberate backdoor into the changed function.
A backdoor requires both elements to be directly visible in the diff itself:
1. a concrete trigger introduced or changed by the update, and
2. a concrete malicious payoff directly enabled by that trigger.
Label "not_safe" only if both are visible in the diff. Label "safe" otherwise or if you are unsure.

The unified diff is available at /inputs/unified_diff.txt.
Write your provisional analysis to /work/analysis.md.
Keep a final label of not_safe only if you can still identify both a concrete trigger introduced or changed by the update and a concrete malicious payoff directly enabled by that trigger from the diff itself.
Write your final decision to /work/final.md.
Return the final answer using the configured structured response with label, trigger, and why.
"""

ANALYST_SCHEMA = {
    "type": "object",
    "properties": {
        "label":   {"type": "string", "enum": ["safe", "not_safe"]},
        "trigger": {"type": "string"},
        "why":     {"type": "string"},
    },
    "required": ["label", "trigger", "why"],
    "additionalProperties": False,
}

ANALYST_SYS = (
    "You are a security analyst who is an expert in binary reverse engineering and security.\n"
    "You are given a unified diff of decompiled code for a single function.\n\n"
    "Determine whether this update injects a deliberate backdoor into the changed function.\n"
    "A backdoor requires both elements to be directly visible in the diff itself:\n"
    "1. a concrete trigger introduced or changed by the update, and\n"
    "2. a concrete malicious payoff directly enabled by that trigger.\n"
    'Label "not_safe" only if both are visible in the diff.\n'
    'Label "safe" otherwise or if you are unsure.\n\n'
    "Return EXACT JSON ONLY:\n"
    "{\n"
    '  "label": "not_safe" | "safe",\n'
    '  "trigger": "exact conditional expression from the diff, or empty string",\n'
    '  "why": "1-3 sentences describing the trigger and the malicious action it activates"\n'
    "}\n"
)

_ASCII_MAP = {
    ord("–"): "-",
    ord("—"): "-",
    ord("…"): "...",
    ord("“"): '"',
    ord("”"): '"',
    ord("‘"): "'",
    ord("’"): "'",
    ord("\u00a0"): 32,
    ord("\u202f"): 32,
}

_EMPTY_DECOMP_FAILURE_MESSAGES: Dict[str, Dict[str, str]] = {
    "empty_baseline_decomp": {
        "observation": "baseline decompilation was empty. Triage skipped and recorded as failed.",
        "final_why": "The baseline decompilation was empty, so the system could not compute a two-sided function diff. The function was recorded as failed because triage did not run, not because the agent identified a trigger.",
    },
    "empty_target_decomp": {
        "observation": "target decompilation was empty. Triage skipped and recorded as failed.",
        "final_why": "The target decompilation was empty, so the system could not compute a two-sided function diff. The function was recorded as failed because triage did not run, not because the agent identified a trigger.",
    },
    "empty_both_decomp": {
        "observation": "baseline and target decompilations were empty. Triage skipped and recorded as failed.",
        "final_why": "Both baseline and target decompilations were empty, so the system could not compute a two-sided function diff. The function was recorded as failed because triage did not run, not because the agent identified a trigger.",
    },
}


def _progress_label(
    *,
    fp_idx: int = 0,
    fp_total: int = 0,
    func_idx: int = 0,
    func_total: int = 0,
) -> str:
    file_part = f"file {fp_idx}/{fp_total}" if fp_total else f"file {fp_idx}"
    func_part = f"func {func_idx}/{func_total}" if func_total else f"func {func_idx}"
    return f"[{file_part} {func_part}]"


class FinalDecisionSchema(BaseModel):
    label: Literal["safe", "not_safe"] = Field(
        description="Final decision for the diff. Must be safe or not_safe.",
    )
    trigger: str = Field(
        default="",
        description="Exact trigger for the malicious behavior, or an empty string if safe.",
    )
    why: str = Field(
        description="Concise explanation of the decision and supporting security reasoning.",
    )


# ---------------------------------------------------------------------------
# Analyst (quick first-pass) helpers
# ---------------------------------------------------------------------------

def _parse_llm_json(text: str) -> Any:
    text = text.strip()
    for fence in ("```json", "```"):
        if text.startswith(fence):
            text = text[len(fence):].lstrip()
            if text.endswith("```"):
                text = text[:-3].rstrip()
    try:
        return json.loads(text)
    except Exception:
        return _extract_first_balanced_json_object(text)


def _analyst_output_complete(d: Dict[str, Any]) -> bool:
    label = _coerce_label(d.get("label"))
    trigger = _coerce_str(d.get("trigger"))
    why = _coerce_str(d.get("why"))
    if label not in {"safe", "not_safe"}:
        return False
    if not why:
        return False
    if label == "not_safe" and not trigger:
        return False
    return True


def _invoke_analyst_text(sys_text: str, human_text: str) -> Tuple[str, float, Dict[str, int], bool]:
    """Stream ANALYST_LLM with a per-token timeout. Returns (text, elapsed_s, usage_counts, timed_out)."""
    import queue as _queue
    import threading as _threading

    msgs = [SystemMessage(content=sys_text), HumanMessage(content=human_text)]
    t0 = time.perf_counter()
    q: "_queue.Queue[Tuple[str, Any]]" = _queue.Queue()
    stop = _threading.Event()

    def _worker() -> None:
        try:
            gen = ANALYST_LLM.stream(msgs)  # type: ignore[union-attr]
            for chunk in gen:
                if stop.is_set():
                    try:
                        gen.close()
                    except Exception:
                        pass
                    break
                q.put(("chunk", chunk))
            q.put(("done", None))
        except Exception as exc:
            q.put(("error", exc))

    t = _threading.Thread(target=_worker, daemon=True)
    t.start()

    chunks: List[str] = []
    aggregated_chunk = None
    timed_out = False
    while True:
        elapsed = time.perf_counter() - t0
        wait = min(_ANALYST_TOKEN_TIMEOUT_S, _ANALYST_TOTAL_TIMEOUT_S - elapsed)
        if wait <= 0:
            timed_out = True
            break
        try:
            kind, val = q.get(timeout=wait)
        except _queue.Empty:
            timed_out = True
            break
        if kind == "done":
            break
        if kind == "error":
            logger.warning("Analyst LLM stream error: %s", val)
            break
        if aggregated_chunk is None:
            aggregated_chunk = val
        else:
            try:
                aggregated_chunk = aggregated_chunk + val
            except Exception:
                aggregated_chunk = val
        content = getattr(val, "content", "") or ""
        if content:
            chunks.append(content)

    if timed_out:
        stop.set()
        logger.warning("Analyst LLM timed out (no token for %.0fs or total %.0fs exceeded).",
                       _ANALYST_TOKEN_TIMEOUT_S, _ANALYST_TOTAL_TIMEOUT_S)

    text = ascii_sanitize("".join(chunks)).strip()
    usage_counts = _extract_usage_counts_from_message(aggregated_chunk)
    return text, time.perf_counter() - t0, usage_counts, timed_out


def _call_analyst_llm_json(
    diff_text: str, fp_idx: int, func_idx: int, notes: Dict[str, Any]
) -> Tuple[str, Dict[str, Any], Dict[str, Any]]:
    """Run analyst LLM. Returns (raw, result_dict, meta). Invalid JSON fails closed to not_safe. Timeouts are recorded as failed."""
    meta: Dict[str, Any] = {
        "attempts": 0,
        "parsed_ok": False,
        "repaired": False,
        "duration_s": 0.0,
        "input_tokens": 0,
        "output_tokens": 0,
        "total_tokens": 0,
        "failure_reason": "",
        "failure_detail": "",
    }

    meta["attempts"] += 1
    raw1, dt1, usage1, timed_out1 = _invoke_analyst_text(ANALYST_SYS, f"FUNCTION UNIFIED DIFF:\n{diff_text}")
    meta["input_tokens"] += int(usage1.get("input_tokens") or 0)
    meta["output_tokens"] += int(usage1.get("output_tokens") or 0)
    meta["total_tokens"] += int(usage1.get("total_tokens") or 0)
    if timed_out1:
        meta["duration_s"] = dt1
        meta["failure_reason"] = "timeout"
        meta["failure_detail"] = "Analyst timed out before reaching a validated decision."
        notes["observations"].append("Analyst timed out before reaching a validated decision.")
        return raw1, {
            "label": "failed",
            "trigger": "",
            "why": "Analyst timed out before reaching a validated decision.",
        }, meta
    d1 = _parse_llm_json(raw1)
    if isinstance(d1, dict) and _analyst_output_complete(d1):
        meta["parsed_ok"] = True
        meta["duration_s"] = dt1
        return raw1, {"label": _coerce_label(d1.get("label")),
                      "trigger": _coerce_str(d1.get("trigger")),
                      "why": _coerce_str(d1.get("why"))}, meta

    meta["attempts"] += 1
    meta["repaired"] = True
    notes["observations"].append("Analyst output invalid/incomplete; retrying once (repair).")
    repair_sys = (
        ANALYST_SYS
        + "\nConstraints:\n"
          "- Output must be a single JSON object.\n"
          "- Field 'why' must be non-empty.\n"
          "- If label is 'not_safe', field 'trigger' must be a non-empty exact condition copied from the diff.\n"
          "- If you cannot provide a trigger, label must be 'safe'.\n"
    )
    repair_human = (
        "You must produce valid JSON that satisfies the constraints.\n"
        "Return JSON only.\n\n"
        f"FUNCTION UNIFIED DIFF:\n{diff_text}\n\n"
        f"PRIOR (possibly invalid) OUTPUT:\n{raw1}\n"
    )
    raw2, dt2, usage2, timed_out2 = _invoke_analyst_text(repair_sys, repair_human)
    meta["input_tokens"] += int(usage2.get("input_tokens") or 0)
    meta["output_tokens"] += int(usage2.get("output_tokens") or 0)
    meta["total_tokens"] += int(usage2.get("total_tokens") or 0)
    if timed_out2:
        meta["duration_s"] = dt1 + dt2
        meta["failure_reason"] = "timeout"
        meta["failure_detail"] = "Analyst timed out before reaching a validated decision."
        notes["observations"].append("Analyst timed out during repair.")
        return (raw2 or raw1), {
            "label": "failed",
            "trigger": "",
            "why": "Analyst timed out before reaching a validated decision.",
        }, meta
    d2 = _parse_llm_json(raw2)
    if isinstance(d2, dict) and _analyst_output_complete(d2):
        meta["parsed_ok"] = True
        meta["duration_s"] = dt1 + dt2
        return raw2, {"label": _coerce_label(d2.get("label")),
                      "trigger": _coerce_str(d2.get("trigger")),
                      "why": _coerce_str(d2.get("why"))}, meta

    meta["parsed_ok"] = False
    meta["duration_s"] = dt1 + dt2
    notes["observations"].append("Analyst JSON parse/validation failed twice; fail-closed to not_safe.")
    return (raw2 or raw1), {
        "label": "not_safe", "trigger": "",
        "why": "Analyst JSON parse/validation failed; fail-closed to not_safe.",
    }, meta


# ---------------------------------------------------------------------------
# LangGraph triage pipeline
# ---------------------------------------------------------------------------

class TriageState(TypedDict):
    diff: str
    fp_idx: int
    fp_total: int
    func_idx: int
    func_total: int
    notes: Dict[str, Any]
    trace_path: Optional[str]
    analyst_only: bool   # stop after analyst, never escalate to agent
    agent_only: bool     # skip analyst, go straight to agent
    analyst_raw: Optional[str]
    analyst_json: Optional[Dict[str, Any]]   # {label, trigger, why}
    analyst_meta: Optional[Dict[str, Any]]   # {attempts, parsed_ok, duration_s, input_tokens, output_tokens, total_tokens}
    agent_result: Optional[Dict[str, Any]]   # full result from _run_agent_node
    final_json: Optional[Dict[str, Any]]     # resolved {label, trigger, why}


def _analyst_node(state: TriageState) -> Dict[str, Any]:
    if state.get("agent_only"):
        # Pass-through: always escalate without running analyst
        return {"analyst_json": {"label": "not_safe", "trigger": "", "why": ""}}
    raw, result, meta = _call_analyst_llm_json(
        state["diff"], state["fp_idx"], state["func_idx"], state["notes"]
    )
    logger.info(
        "%s analyst: label=%s trigger=%s",
        _progress_label(
            fp_idx=state["fp_idx"],
            fp_total=state.get("fp_total", 0),
            func_idx=state["func_idx"],
            func_total=state.get("func_total", 0),
        ),
        result.get("label"),
        _preview_text(result.get("trigger", ""), limit=60),
    )
    return {"analyst_raw": raw, "analyst_json": result, "analyst_meta": meta}


def _route_after_analyst(state: TriageState) -> str:
    if state.get("analyst_only"):
        return END
    analyst_failure_reason = _coerce_str((state.get("analyst_meta") or {}).get("failure_reason"))
    if analyst_failure_reason == "timeout":
        logger.info(
            "%s analyst timed out, escalating to workspace agent",
            _progress_label(
                fp_idx=state["fp_idx"],
                fp_total=state.get("fp_total", 0),
                func_idx=state["func_idx"],
                func_total=state.get("func_total", 0),
            ),
        )
        return "deep_agent"
    label = (state.get("analyst_json") or {}).get("label", "safe")
    if label == "not_safe":
        return "deep_agent"
    return END


def _deep_agent_node(state: TriageState) -> Dict[str, Any]:
    progress_label = _progress_label(
        fp_idx=state["fp_idx"],
        fp_total=state.get("fp_total", 0),
        func_idx=state["func_idx"],
        func_total=state.get("func_total", 0),
    )
    result = _run_agent_node(
        diff_text=state["diff"],
        notes=state["notes"],
        trace_path=state.get("trace_path"),
        progress_label=progress_label,
    )
    final = {"label": result.get("label", "failed"),
             "trigger": result.get("trigger", ""),
             "why": result.get("why", "")}
    return {"agent_result": result, "final_json": final}


def _build_triage_graph() -> Any:
    g: StateGraph = StateGraph(TriageState)
    g.add_node("analyst", _analyst_node)
    g.add_node("deep_agent", _deep_agent_node)
    g.add_edge(START, "analyst")
    g.add_conditional_edges("analyst", _route_after_analyst,
                             {"deep_agent": "deep_agent", END: END})
    g.add_edge("deep_agent", END)
    return g.compile()


class GuardedStateBackend(StateBackend):
    """Block modifications to seeded input files and mirror writes to local state."""

    def __init__(self, runtime: Any, mirror: Optional[Dict[str, str]] = None) -> None:
        super().__init__(runtime)
        self._mirror = mirror if isinstance(mirror, dict) else None

    def write(self, file_path: str, content: str) -> WriteResult:
        if file_path.startswith("/inputs/"):
            return WriteResult(error="Read-only: /inputs/")
        result = super().write(file_path, content)
        if not getattr(result, "error", None) and self._mirror is not None:
            self._mirror[file_path] = content
        return result

    def edit(self, file_path: str, *args: Any, **kwargs: Any) -> EditResult:
        if file_path.startswith("/inputs/"):
            return EditResult(error="Read-only: /inputs/")
        return super().edit(file_path, *args, **kwargs)


def write_text(path: str, text: str) -> None:
    with open(path, "w", encoding="utf-8") as f:
        f.write(text if text is not None else "")


def write_json(path: str, data: Any) -> None:
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False, default=str)


def _extract_first_balanced_json_object(text: str) -> Optional[dict]:
    start = text.find("{")
    if start == -1:
        return None
    depth = 0
    for index in range(start, len(text)):
        char = text[index]
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                blob = text[start : index + 1]
                try:
                    return json.loads(blob)
                except Exception:
                    return None
    return None


def ensure_decimal_str(addr: Any) -> str:
    return str(addr).strip()


def get_empty_decomp_failure_reason(meta: Dict[str, Any]) -> Optional[str]:
    baseline_empty = bool(meta.get("baseline_decomp_empty"))
    target_empty = bool(meta.get("target_decomp_empty"))
    if baseline_empty and target_empty:
        return "empty_both_decomp"
    if baseline_empty:
        return "empty_baseline_decomp"
    if target_empty:
        return "empty_target_decomp"
    return None


def normalize_function_decomp_diff_response(resp: Any) -> Dict[str, Any]:
    payload = getattr(resp, "content", resp)
    meta: Dict[str, Any] = {}
    tool_error = True
    error = ""
    error_kind = "invalid_payload_type"
    unified = ""

    if isinstance(payload, dict):
        meta_candidate = payload.get("meta")
        if isinstance(meta_candidate, dict):
            meta = dict(meta_candidate)

        if "error" in payload:
            error = str(payload.get("error") or "")
            error_kind = str(payload.get("error_kind") or "tool_error")
        else:
            unified_value = payload.get("unified")
            if isinstance(unified_value, str):
                unified = unified_value
                tool_error = False
                error_kind = ""
            else:
                error = "function_decomp_diff returned a non-string unified diff."
                error_kind = "invalid_unified_payload"
    else:
        error = "function_decomp_diff returned a non-dict payload."

    artifact_meta = dict(meta)
    artifact_meta["tool_error"] = tool_error
    if tool_error:
        artifact_meta["error"] = error
        artifact_meta["error_kind"] = error_kind

    return {
        "unified": unified,
        "meta": meta,
        "artifact_meta": artifact_meta,
        "tool_error": tool_error,
        "error": error,
        "error_kind": error_kind,
        "empty_decomp_reason": get_empty_decomp_failure_reason(meta),
    }


def write_diff_artifacts(func_dir: str, unified: str, diff_meta: Dict[str, Any]) -> None:
    write_text(f"{func_dir}/diff.txt", unified or "")
    write_json(f"{func_dir}/diff_meta.json", diff_meta or {})


def _append_trace_line(path: Optional[str], line: str, *, truncate: bool = False) -> None:
    if not path:
        return
    try:
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
        mode = "w" if truncate else "a"
        with open(path, mode, encoding="utf-8") as f:
            f.write(line.rstrip() + "\n")
    except Exception:
        return


def _trace_source(ns: Any) -> str:
    if not isinstance(ns, tuple) or not ns:
        return "agent"
    if any(isinstance(segment, str) and segment.startswith("tools:") for segment in ns):
        return "subagent"
    return "agent"


def _preview_text(value: Any, limit: int = 160) -> str:
    text = _coerce_str(value).replace("\n", " ").strip()
    if len(text) <= limit:
        return text
    return text[: max(0, limit - 3)] + "..."


def _extract_token_text(content: Any) -> str:
    """Extract raw text from a streaming token content without stripping whitespace."""
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        parts = []
        for block in content:
            if isinstance(block, dict) and block.get("type") == "text":
                parts.append(block.get("text", ""))
        return "".join(parts)
    return ""


def _flush_text_buffer(
    trace_path: Optional[str],
    text_buffers: Dict[str, str],
    source: str,
    elapsed_s: float,
    *,
    force: bool = False,
) -> None:
    text = text_buffers.get(source, "")
    if not text:
        return
    if not force and len(text) < 120 and "\n" not in text:
        return
    line = text.replace("\n", " ").strip()
    if line:
        _append_trace_line(
            trace_path,
            f"[{elapsed_s:7.2f}s] [{source}] text: {line}",
        )
        preview = line[:600] + ("…" if len(line) > 600 else "")
        logger.info("[%6.2fs] [%s] %s", elapsed_s, source, preview)
    text_buffers[source] = ""


def _log_stream_chunk(
    trace_path: Optional[str],
    chunk: Dict[str, Any],
    elapsed_s: float,
    text_buffers: Dict[str, str],
) -> None:
    chunk_type = str(chunk.get("type") or "")
    source = _trace_source(chunk.get("ns"))
    data = chunk.get("data")

    if chunk_type == "updates" and isinstance(data, dict):
        _flush_text_buffer(trace_path, text_buffers, source, elapsed_s, force=True)
        for node_name in data:
            if node_name in {"model_request", "tools"}:
                _append_trace_line(
                    trace_path,
                    f"[{elapsed_s:7.2f}s] [{source}] step: {node_name}",
                )
        return

    if chunk_type == "tasks":
        _flush_text_buffer(trace_path, text_buffers, source, elapsed_s, force=True)
        _append_trace_line(
            trace_path,
            f"[{elapsed_s:7.2f}s] [{source}] task event: {_preview_text(data)}",
        )
        return

    if chunk_type == "messages" and isinstance(data, tuple) and len(data) == 2:
        token, _metadata = data
        tool_call_chunks = getattr(token, "tool_call_chunks", None) or []
        for tool_call in tool_call_chunks:
            name = tool_call.get("name")
            if not name:
                continue
            _flush_text_buffer(trace_path, text_buffers, source, elapsed_s, force=True)
            if source == "agent" and name == "task":
                _append_trace_line(
                    trace_path,
                    f"[{elapsed_s:7.2f}s] [agent] subagent call: task",
                )
                logger.info("[%6.2fs] [agent] → task (subagent)", elapsed_s)
            else:
                _append_trace_line(
                    trace_path,
                    f"[{elapsed_s:7.2f}s] [{source}] tool call: {name}",
                )
                logger.info("[%6.2fs] [%s] → %s", elapsed_s, source, name)
        content = getattr(token, "content", "")
        if getattr(token, "type", "") != "tool" and content and not tool_call_chunks:
            text_buffers[source] = text_buffers.get(source, "") + _extract_token_text(content)
            _flush_text_buffer(trace_path, text_buffers, source, elapsed_s)
        if getattr(token, "type", "") == "tool":
            tool_name = getattr(token, "name", "tool")
            _flush_text_buffer(trace_path, text_buffers, source, elapsed_s, force=True)
            if source == "agent" and tool_name == "task":
                result_preview = _preview_text(getattr(token, "content", ""), limit=300)
                _append_trace_line(
                    trace_path,
                    f"[{elapsed_s:7.2f}s] [subagent] result: {result_preview}",
                )
                logger.info("[%6.2fs] [subagent] ← %s", elapsed_s, result_preview)
            else:
                result_preview = _preview_text(getattr(token, "content", ""), limit=200)
                _append_trace_line(
                    trace_path,
                    f"[{elapsed_s:7.2f}s] [{source}] tool result [{tool_name}]: {result_preview}",
                )
                logger.info("[%6.2fs] [%s] ← %s: %s", elapsed_s, source, tool_name, result_preview)


def _normalize_stream_item(item: Any) -> Dict[str, Any]:
    namespace: Tuple[str, ...] = ()
    mode = "values"
    data = item

    if isinstance(item, dict) and {"type", "data"} <= set(item.keys()):
        namespace = tuple(item.get("ns") or ())
        mode = str(item.get("type") or "values")
        data = item.get("data")
    elif isinstance(item, tuple):
        if len(item) == 3:
            namespace = tuple(item[0] or ())
            mode = str(item[1] or "values")
            data = item[2]
        elif len(item) == 2:
            if isinstance(item[0], tuple):
                namespace = tuple(item[0] or ())
                data = item[1]
            else:
                mode = str(item[0] or "values")
                data = item[1]

    return {
        "ns": namespace,
        "type": mode,
        "data": data,
    }


def _normalize_final_payload(payload: Any) -> Tuple[Optional[Dict[str, Any]], bool]:
    if isinstance(payload, BaseModel):
        payload = payload.model_dump()
    if not isinstance(payload, dict):
        return None, False
    label = _coerce_label(payload.get("label"))
    trigger = _coerce_str(payload.get("trigger"))
    why = _coerce_str(payload.get("why"))
    if label not in {"safe", "not_safe"} or not why:
        return None, False
    return {"label": label, "trigger": trigger, "why": why}, True


def _make_agent_model(
    model: str,
    *,
    request_timeout_s: float,
) -> ChatOllama:
    kwargs: Dict[str, Any] = {
        "model": model,
        "temperature": 0.0,
        "keep_alive": "10m",
    }
    if request_timeout_s > 0:
        kwargs["client_kwargs"] = {"timeout": request_timeout_s}
    return ChatOllama(**kwargs)


def _build_triage_agent(
    *,
    main_model: ChatOllama,
    file_mirror: Dict[str, str],
) -> Any:
    return create_deep_agent(
        model=main_model,
        response_format=FinalDecisionSchema,
        system_prompt=DEEP_AGENT_SYS,
        checkpointer=MemorySaver(),
        subagents=[],
        backend=lambda runtime: GuardedStateBackend(runtime, mirror=file_mirror),
        debug=False,
        name="delt_deep_agent",
    )


def _invoke_agent_with_timeout(
    agent: Any,
    payload: Dict[str, Any],
    *,
    config: Dict[str, Any],
    timeout_s: float,
    trace_path: Optional[str] = None,
) -> Any:
    global _ASYNC_RUNNER

    async def _run() -> Any:
        started_at = time.perf_counter()
        text_buffers: Dict[str, str] = {"agent": "", "subagent": ""}

        async def _stream_then_collect_state() -> Any:
            async for item in agent.astream(
                payload,
                config=config,
                stream_mode=["updates", "messages", "tasks"],
                subgraphs=True,
                version="v2",
            ):
                chunk = _normalize_stream_item(item)
                _log_stream_chunk(
                    trace_path,
                    chunk,
                    time.perf_counter() - started_at,
                    text_buffers,
                )

            elapsed_s = time.perf_counter() - started_at
            _flush_text_buffer(trace_path, text_buffers, "agent", elapsed_s, force=True)
            _flush_text_buffer(trace_path, text_buffers, "subagent", elapsed_s, force=True)

            snapshot = await agent.aget_state(config)
            return getattr(snapshot, "values", snapshot)

        if timeout_s > 0:
            async with asyncio.timeout(timeout_s):
                return await _stream_then_collect_state()
        return await _stream_then_collect_state()

    if _ASYNC_RUNNER is None:
        _ASYNC_RUNNER = asyncio.Runner()
    return _ASYNC_RUNNER.run(_run())


def _close_async_runner() -> None:
    global _ASYNC_RUNNER
    if _ASYNC_RUNNER is not None:
        _ASYNC_RUNNER.close()
        _ASYNC_RUNNER = None


atexit.register(_close_async_runner)


def _build_llms(model: str) -> None:
    global LLM, ANALYST_LLM, TRIAGE_GRAPH
    LLM = _make_agent_model(model, request_timeout_s=_DEFAULT_REQUEST_TIMEOUT_S)
    ANALYST_LLM = ChatOllama(
        model=model,
        temperature=0.0,
        keep_alive="10m",
        request_timeout=180.0,
        format=ANALYST_SCHEMA,
        model_kwargs={"num_predict": 512},
    )
    TRIAGE_GRAPH = _build_triage_graph()


def _coerce_token_count(value: Any) -> int:
    try:
        return max(0, int(value or 0))
    except Exception:
        return 0


def _zero_usage_counts() -> Dict[str, int]:
    return {
        "input_tokens": 0,
        "output_tokens": 0,
        "total_tokens": 0,
    }


def _extract_usage_counts_from_message(message: Any) -> Dict[str, int]:
    input_tokens = 0
    output_tokens = 0
    total_tokens = 0

    usage = getattr(message, "usage_metadata", None)
    if isinstance(usage, dict):
        input_tokens = _coerce_token_count(usage.get("input_tokens"))
        output_tokens = _coerce_token_count(usage.get("output_tokens"))
        total_tokens = _coerce_token_count(usage.get("total_tokens"))

    response_metadata = getattr(message, "response_metadata", None)
    if isinstance(response_metadata, dict):
        if input_tokens <= 0:
            input_tokens = _coerce_token_count(response_metadata.get("prompt_eval_count"))
        if output_tokens <= 0:
            output_tokens = _coerce_token_count(response_metadata.get("eval_count"))

    if total_tokens <= 0:
        total_tokens = input_tokens + output_tokens
    return {
        "input_tokens": input_tokens,
        "output_tokens": output_tokens,
        "total_tokens": total_tokens,
    }


def _extract_usage_from_message(message: Any) -> int:
    return _extract_usage_counts_from_message(message).get("total_tokens", 0)


def _state_field(state: Any, key: str) -> Any:
    if isinstance(state, dict):
        return state.get(key)
    return getattr(state, key, None)


def _collect_llm_usage_counts(messages: Any) -> Dict[str, int]:
    counts = _zero_usage_counts()
    if not isinstance(messages, list):
        return counts
    for message in messages:
        usage = _extract_usage_counts_from_message(message)
        counts["input_tokens"] += usage.get("input_tokens", 0)
        counts["output_tokens"] += usage.get("output_tokens", 0)
        counts["total_tokens"] += usage.get("total_tokens", 0)
    return counts


def _collect_llm_total_tokens(messages: Any) -> int:
    return _collect_llm_usage_counts(messages).get("total_tokens", 0)


def _coerce_str(value: Any) -> str:
    if value is None:
        return ""
    try:
        return str(value).strip()
    except Exception:
        return ""


def _coerce_label(value: Any) -> str:
    return _coerce_str(value).lower().replace("-", "_")


def _normalize_filter_value(value: Any) -> Optional[str]:
    if value is None:
        return None

    value_str = _coerce_str(value)
    if not value_str:
        return None
    value_lower = value_str.lower()
    if value_lower in {"none", "null"}:
        return None
    if value_lower == "and":
        return "Control_Call_Modified"
    if value_lower == "or":
        return "Call_OR_Control_Modified"
    return value_str


def _coerce_result_label(label: Any, failure_reason: Any = None) -> str:
    failure_reason_str = _coerce_str(failure_reason)
    if failure_reason_str and failure_reason_str in _EMPTY_DECOMP_FAILURE_MESSAGES:
        return "skipped"
    if failure_reason_str:
        return "failed"
    label_norm = _coerce_label(label)
    if label_norm == "error":
        return "failed"
    if label_norm in {"safe", "not_safe", "failed"}:
        return label_norm
    return "failed"


def ascii_sanitize(text: str) -> str:
    return unicodedata.normalize("NFKC", text).translate(_ASCII_MAP)


def read_json(path: str) -> Any:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def coerce_json_like(value: Any) -> Optional[dict]:
    if isinstance(value, dict):
        return value
    if isinstance(value, str):
        try:
            return json.loads(value)
        except Exception:
            return _extract_first_balanced_json_object(value)
    return None


def load_ground_truth_file(path: Optional[str]) -> Dict[str, Any]:
    if not path:
        return {}
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception as exc:
        logger.error("Failed to load ground truth file '%s': %s", path, exc)
        return {}


def get_ground_truth_for_target(gt: Dict[str, Any], target_name: str) -> Optional[Dict[str, Any]]:
    if not isinstance(gt, dict) or not target_name:
        return None

    samples = gt.get("samples")
    if not isinstance(samples, dict):
        return None

    entry = samples.get(target_name)
    if not isinstance(entry, dict):
        return None

    backdoor = entry.get("backdoor")
    if not isinstance(backdoor, dict):
        return None

    targets_raw = backdoor.get("targets")
    if not isinstance(targets_raw, list) or not targets_raw:
        return None

    targets: List[Dict[str, Any]] = []
    addr_set: Set[str] = set()
    addr_oid_set: Set[Tuple[str, Optional[str]]] = set()

    for target in targets_raw:
        if not isinstance(target, dict):
            continue
        addr = target.get("target_addr")
        if addr is None:
            continue

        addr_norm = ensure_decimal_str(addr)
        oid = target.get("target_oid", None)
        oid_norm = str(oid) if oid is not None else None

        targets.append({"target_addr": addr_norm, "target_oid": oid_norm})
        addr_set.add(addr_norm)
        addr_oid_set.add((addr_norm, oid_norm))

    if not targets:
        return None

    return {"targets": targets, "addr_set": addr_set, "addr_oid_set": addr_oid_set}


def gt_row_matches_any(row: Dict[str, Any], gt_norm: Dict[str, Any]) -> bool:
    if not gt_norm:
        return False

    row_addr = ensure_decimal_str(row.get("target_addr"))
    if row_addr not in gt_norm["addr_set"]:
        return False

    row_oid = row.get("target_oid", None)
    row_oid_norm = str(row_oid) if row_oid is not None else None

    if (row_addr, row_oid_norm) in gt_norm["addr_oid_set"]:
        return True
    if (row_addr, None) in gt_norm["addr_oid_set"]:
        return True
    return False


def _comparison_dir_name(target_name: str, baseline_name: str) -> str:
    pair_dir_name = f"{target_name}_to_{baseline_name}"
    pair_dir_name = pair_dir_name.replace(os.sep, "_")
    if os.altsep:
        pair_dir_name = pair_dir_name.replace(os.altsep, "_")
    return pair_dir_name


def _prepare_llm_filter_run_opts(opts: Dict[str, Any]) -> Dict[str, Any]:
    run_opts = dict(opts or {})

    model = str(run_opts.get("model") or _DEFAULT_MODEL)

    _build_llms(model)
    run_opts["_model"] = model
    run_opts["_diff_compact"] = False

    gt_path = run_opts.get("ground_truth")
    run_opts["_ground_truth"] = load_ground_truth_file(gt_path)

    logger.info("Configured DeLT deep agent model '%s'", model)
    if gt_path:
        logger.info("Loaded ground truth: %s", gt_path)

    return run_opts


def _aggregate_ablation_rows(rows: List[Dict[str, Any]]) -> Dict[str, Any]:
    gt_compromised_total = sum(int(row.get("gt_compromised_count") or 0) for row in rows)
    tp_final = sum(int(row.get("tp_final") or 0) for row in rows)
    fp_final = sum(int(row.get("fp_final") or 0) for row in rows)
    failure_reason_counts: Dict[str, int] = {}
    for row in rows:
        for reason, count in (row.get("failure_reason_counts") or {}).items():
            key = _coerce_str(reason)
            if not key:
                continue
            failure_reason_counts[key] = failure_reason_counts.get(key, 0) + int(count or 0)

    final_precision = None
    if tp_final + fp_final:
        final_precision = tp_final / float(tp_final + fp_final)

    final_recall = None
    if gt_compromised_total:
        final_recall = tp_final / float(gt_compromised_total)

    return {
        "comparisons": len(rows),
        "gt_compromised_total": gt_compromised_total,
        "hits_final": sum(1 for row in rows if row.get("hit_final") is True),
        "tp_final": tp_final,
        "fp_final": fp_final,
        "final_precision": final_precision,
        "final_recall": final_recall,
        "filtered_functions_total": sum(int(row.get("filtered_functions") or 0) for row in rows),
        "final_not_safe_filtered_total": sum(int(row.get("final_not_safe_filtered") or 0) for row in rows),
        "final_failed_filtered_total": sum(int(row.get("final_failed_filtered") or 0) for row in rows),
        "failure_reason_counts": failure_reason_counts,
        "llm_input_tokens": sum(int(row.get("llm_input_tokens") or 0) for row in rows),
        "llm_output_tokens": sum(int(row.get("llm_output_tokens") or 0) for row in rows),
        "llm_total_tokens": sum(int(row.get("llm_total_tokens") or 0) for row in rows),
        "llm_elapsed_s_total": sum(float(row.get("llm_elapsed_s") or 0.0) for row in rows),
    }


def _pair_name_from_summary_row(row: Dict[str, Any]) -> str:
    pair_dir = row.get("pair_dir")
    if pair_dir:
        name = os.path.basename(str(pair_dir).rstrip("/"))
        if name:
            return name
    target = row.get("target")
    baseline = row.get("baseline")
    return f"{target}_to_{baseline}"


def _parse_ablation_axes(value: Any) -> List[str]:
    if value is None or value is False:
        return []

    if isinstance(value, str):
        raw_items = [part.strip().lower() for part in value.split(",")]
    elif isinstance(value, (list, tuple, set)):
        raw_items = [str(part).strip().lower() for part in value]
    else:
        raw_items = [str(value).strip().lower()]

    seen: Set[str] = set()
    requested: List[str] = []
    for item in raw_items:
        if not item:
            continue
        if item not in _SUPPORTED_ABLATION_AXES:
            raise ValueError(
                f"Unsupported ablation axis '{item}'. Supported axes: {', '.join(_SUPPORTED_ABLATION_AXES)}"
            )
        if item not in seen:
            requested.append(item)
            seen.add(item)

    return [axis for axis in _SUPPORTED_ABLATION_AXES if axis in seen]


def _ablation_axis_value(axis: str, *, diff_raw: bool, agent_only: bool, analyst_only: bool = False) -> str:
    if axis == "diff":
        return "raw" if diff_raw else "processed"
    if axis == "first_pass":
        if agent_only:
            return "agent_only"
        if analyst_only:
            return "analyst_only"
        return "combined"
    raise ValueError(f"Unsupported ablation axis '{axis}'")


def _ablation_run_name(axes: List[str], *, diff_raw: bool, agent_only: bool, analyst_only: bool = False) -> str:
    parts: List[str] = []
    if "diff" in axes:
        parts.append("raw" if diff_raw else "processed")
    if "first_pass" in axes:
        if agent_only:
            parts.append("agent_only")
        elif analyst_only:
            parts.append("analyst_only")
        else:
            parts.append("combined")
    return "_".join(parts) if parts else "default"


# (agent_only, analyst_only) triples for the first_pass ablation axis:
# combined=>(False, False), agent_only=>(True, False), analyst_only=>(False, True)
_FIRST_PASS_ABLATION_VALUES: List[Tuple[bool, bool]] = [
    (False, False),  # combined
    (True, False),   # agent_only
    (False, True),   # analyst_only
]


def _expand_ablation_run_specs(base_opts: Dict[str, Any], axes: List[str]) -> List[Dict[str, Any]]:
    base_diff_raw = bool(base_opts.get("_diff_raw"))
    base_agent_only = bool(base_opts.get("agent_only"))
    base_analyst_only = bool(base_opts.get("analyst_only"))

    diff_values = [False, True] if "diff" in axes else [base_diff_raw]
    first_pass_values = (
        _FIRST_PASS_ABLATION_VALUES if "first_pass" in axes else [(base_agent_only, base_analyst_only)]
    )

    specs: List[Dict[str, Any]] = []
    for agent_only, analyst_only in first_pass_values:
        for diff_raw in diff_values:
            run_opts = dict(base_opts)
            run_opts["_diff_raw"] = diff_raw
            run_opts["agent_only"] = agent_only
            run_opts["analyst_only"] = analyst_only
            specs.append(
                {
                    "name": _ablation_run_name(axes, diff_raw=diff_raw, agent_only=agent_only, analyst_only=analyst_only),
                    "settings": {
                        "diff": _ablation_axis_value("diff", diff_raw=diff_raw, agent_only=agent_only),
                        "first_pass": _ablation_axis_value("first_pass", diff_raw=diff_raw, agent_only=agent_only, analyst_only=analyst_only),
                    },
                    "opts": run_opts,
                }
            )
    return specs


def _compute_ablation_delta(control: Dict[str, Any], variant: Dict[str, Any]) -> Dict[str, Any]:
    delta: Dict[str, Any] = {}
    for key in (
        "comparisons",
        "gt_compromised_total",
        "hits_final",
        "tp_final",
        "fp_final",
        "filtered_functions_total",
        "final_not_safe_filtered_total",
        "final_failed_filtered_total",
        "llm_input_tokens",
        "llm_output_tokens",
        "llm_total_tokens",
        "llm_elapsed_s_total",
    ):
        delta[key] = variant.get(key, 0) - control.get(key, 0)

    for key in ("final_precision", "final_recall"):
        control_val = control.get(key)
        variant_val = variant.get(key)
        delta[key] = None if control_val is None or variant_val is None else (variant_val - control_val)

    return delta


def _build_ablation_summary(run_results: List[Dict[str, Any]], axes: List[str], outdir: str) -> Dict[str, Any]:
    run_order = [run["name"] for run in run_results]
    run_pair_maps: Dict[str, Dict[str, Dict[str, Any]]] = {}

    for run in run_results:
        rows = list((run.get("summary") or {}).get("comparisons") or [])
        run_pair_maps[run["name"]] = {_pair_name_from_summary_row(row): row for row in rows}

    common_overlap_pairs: List[str] = []
    if run_pair_maps:
        pair_name_sets = [set(pair_map) for pair_map in run_pair_maps.values()]
        common_overlap_pairs = sorted(set.intersection(*pair_name_sets)) if pair_name_sets else []

    runs: Dict[str, Any] = {}
    for run in run_results:
        name = run["name"]
        rows = list((run.get("summary") or {}).get("comparisons") or [])
        pair_map = run_pair_maps[name]
        overlap_rows = [pair_map[pair_name] for pair_name in common_overlap_pairs if pair_name in pair_map]
        runs[name] = {
            "name": name,
            "outdir": run.get("outdir"),
            "settings": run.get("settings") or {},
            "completed_comparisons": len(rows),
            "all_pairs_aggregate": _aggregate_ablation_rows(rows),
            "common_overlap_aggregate": _aggregate_ablation_rows(overlap_rows),
            "only_in_run": sorted(set(pair_map) - set(common_overlap_pairs)),
        }

    pair_metrics: List[Dict[str, Any]] = []
    if run_order:
        for pair_name in common_overlap_pairs:
            first_row = run_pair_maps[run_order[0]][pair_name]
            per_run: Dict[str, Any] = {}
            for run_name in run_order:
                row = run_pair_maps[run_name][pair_name]
                per_run[run_name] = {
                    "hit_final": row.get("hit_final"),
                    "tp_final": row.get("tp_final"),
                    "fp_final": row.get("fp_final"),
                    "final_failed_filtered": row.get("final_failed_filtered"),
                    "llm_input_tokens": row.get("llm_input_tokens"),
                    "llm_output_tokens": row.get("llm_output_tokens"),
                    "llm_total_tokens": row.get("llm_total_tokens"),
                    "llm_elapsed_s": row.get("llm_elapsed_s"),
                }
            pair_metrics.append(
                {
                    "pair": pair_name,
                    "gt_compromised_count": first_row.get("gt_compromised_count"),
                    "filtered_functions": first_row.get("filtered_functions"),
                    "runs": per_run,
                }
            )

    _axis_control = {"diff": "processed", "first_pass": "combined"}
    _axis_variants = {"diff": ["raw"], "first_pass": ["agent_only", "analyst_only"]}

    axis_comparisons: Dict[str, List[Dict[str, Any]]] = {}
    for axis in axes:
        control_value = _axis_control.get(axis, "")
        variant_values = _axis_variants.get(axis, [])
        grouped: Dict[Tuple[Tuple[str, str], ...], Dict[str, Dict[str, Any]]] = {}

        for run in run_results:
            settings = run.get("settings") or {}
            context = tuple(
                (other_axis, str(settings.get(other_axis) or ""))
                for other_axis in axes
                if other_axis != axis
            )
            grouped.setdefault(context, {})[str(settings.get(axis) or "")] = run

        comparisons: List[Dict[str, Any]] = []
        for context, variants in grouped.items():
            control_run = variants.get(control_value)
            if not control_run:
                continue
            control_name = control_run["name"]

            for variant_value in variant_values:
                variant_run = variants.get(variant_value)
                if not variant_run:
                    continue

                variant_name = variant_run["name"]
                overlap_pairs = sorted(set(run_pair_maps[control_name]) & set(run_pair_maps[variant_name]))
                control_rows = [run_pair_maps[control_name][pair_name] for pair_name in overlap_pairs]
                variant_rows = [run_pair_maps[variant_name][pair_name] for pair_name in overlap_pairs]
                control_aggregate = _aggregate_ablation_rows(control_rows)
                variant_aggregate = _aggregate_ablation_rows(variant_rows)

                comparisons.append(
                    {
                        "context": {key: value for key, value in context},
                        "overlap_count": len(overlap_pairs),
                        "control_run": control_name,
                        "variant_run": variant_name,
                        "control_aggregate": control_aggregate,
                        "variant_aggregate": variant_aggregate,
                        "delta_variant_minus_control": _compute_ablation_delta(control_aggregate, variant_aggregate),
                    }
                )

        axis_comparisons[axis] = comparisons

    return {
        "outdir": outdir,
        "axes": axes,
        "run_order": run_order,
        "runs": runs,
        "common_overlap_count": len(common_overlap_pairs),
        "common_overlap_pairs": common_overlap_pairs,
        "pair_metrics": pair_metrics,
        "axis_comparisons": axis_comparisons,
    }


def _render_ablation_summary(summary: Dict[str, Any]) -> str:
    def _fmt_ratio(value: Optional[float]) -> str:
        return "n/a" if value is None else f"{value:.4f}"

    lines = [
        "Ablation Summary",
        f"Outdir: {summary.get('outdir')}",
        f"Axes: {', '.join(summary.get('axes') or []) or 'none'}",
        f"Runs: {len(summary.get('run_order') or [])}",
        f"Common overlap across all runs: {summary.get('common_overlap_count', 0)}",
        "",
        "Runs",
    ]

    runs = summary.get("runs") or {}
    for run_name in summary.get("run_order") or []:
        run = runs.get(run_name) or {}
        agg = run.get("common_overlap_aggregate") or {}
        settings = run.get("settings") or {}
        lines.append(
            (
                f"{run_name}:"
                f" diff={settings.get('diff')}"
                f" first_pass={settings.get('first_pass')}"
                f" completed={run.get('completed_comparisons', 0)}"
                f" overlap={agg.get('comparisons', 0)}"
                f" hits={agg.get('hits_final', 0)}"
                f" TP={agg.get('tp_final', 0)}"
                f" FP={agg.get('fp_final', 0)}"
                f" flagged={agg.get('final_not_safe_filtered_total', 0)}"
                f" failed={agg.get('final_failed_filtered_total', 0)}"
                f" precision={_fmt_ratio(agg.get('final_precision'))}"
                f" recall={_fmt_ratio(agg.get('final_recall'))}"
                f" tokens_in={agg.get('llm_input_tokens', 0)}"
                f" tokens_out={agg.get('llm_output_tokens', 0)}"
                f" tokens_total={agg.get('llm_total_tokens', 0)}"
                f" llm_s={float(agg.get('llm_elapsed_s_total') or 0.0):.2f}"
            )
        )

    for axis in summary.get("axes") or []:
        lines.extend(["", f"{axis.title()} Comparisons"])
        comparisons = list((summary.get("axis_comparisons") or {}).get(axis) or [])
        if not comparisons:
            lines.append("None")
            continue

        for comparison in comparisons:
            context = comparison.get("context") or {}
            context_str = ", ".join(f"{key}={value}" for key, value in context.items()) or "all other settings fixed"
            delta = comparison.get("delta_variant_minus_control") or {}
            lines.append(
                f"{comparison.get('control_run')} -> {comparison.get('variant_run')} ({context_str}, overlap={comparison.get('overlap_count', 0)})"
            )
            lines.append(
                (
                    "  delta variant-control:"
                    f" hits={delta.get('hits_final', 0)}"
                    f" TP={delta.get('tp_final', 0)}"
                    f" FP={delta.get('fp_final', 0)}"
                    f" flagged={delta.get('final_not_safe_filtered_total', 0)}"
                    f" failed={delta.get('final_failed_filtered_total', 0)}"
                    f" precision={_fmt_ratio(delta.get('final_precision'))}"
                    f" recall={_fmt_ratio(delta.get('final_recall'))}"
                    f" tokens_in={delta.get('llm_input_tokens', 0)}"
                    f" tokens_out={delta.get('llm_output_tokens', 0)}"
                    f" tokens_total={delta.get('llm_total_tokens', 0)}"
                    f" llm_s={float(delta.get('llm_elapsed_s_total') or 0.0):.2f}"
                )
            )

    return "\n".join(lines)


def _resolve_llm_filter_pairs(args: List[str], opts: Dict[str, Any]) -> List[Tuple[str, str]]:
    pairs: List[Tuple[str, str]]
    series_file: Optional[str] = opts.get("entries")

    if series_file:
        pairs = drift.read_series_file(series_file)
        if len(pairs) < 2:
            raise ValueError("entries file must list at least two versions (one per line)")
    elif len(args) == 2:
        pairs = [(args[0], args[1])]
        logger.info("Single comparison: %s -> %s", args[0], args[1])
    else:
        raise ValueError("Pass either [target, baseline] or --entries with at least two lines.")

    return pairs


def _run_ablation_specs(
    pairs: List[Tuple[str, str]],
    outdir: str,
    axes: List[str],
    run_specs: List[Dict[str, Any]],
) -> Dict[str, Any]:
    os.makedirs(outdir, exist_ok=True)
    run_results: List[Dict[str, Any]] = []

    logger.info(
        "Starting ablation over axes %s with %d run configuration(s).",
        ",".join(axes),
        len(run_specs),
    )

    for spec in run_specs:
        run_outdir = os.path.join(outdir, spec["name"])
        settings = spec["settings"]
        logger.info(
            "Ablation run '%s': diff=%s first_pass=%s outdir='%s'",
            spec["name"],
            settings.get("diff"),
            settings.get("first_pass"),
            run_outdir,
        )
        summary = _run_series(pairs, run_outdir, spec["opts"])
        run_results.append(
            {
                "name": spec["name"],
                "settings": settings,
                "outdir": run_outdir,
                "summary": summary,
            }
        )

    ablation_summary = _build_ablation_summary(run_results, axes, outdir)
    write_json(os.path.join(outdir, "ablation_summary.json"), ablation_summary)
    write_text(
        os.path.join(outdir, "ablation_summary.txt"),
        _render_ablation_summary(ablation_summary),
    )
    logger.info("Wrote ablation summaries under '%s'", outdir)
    return ablation_summary


def _run_series(
    pairs: List[Tuple[str, str]],
    outdir: str,
    opts: Dict[str, Any],
) -> Dict[str, Any]:
    os.makedirs(outdir, exist_ok=True)

    comparison_rows: List[Dict[str, Any]] = []
    per_function_rows: List[Dict[str, Any]] = []

    total_pairs = len(pairs)
    diff_raw = bool(opts.get("_diff_raw"))
    diff_mode = "raw" if diff_raw else "processed"
    agent_only = bool(opts.get("agent_only"))
    analyst_only = bool(opts.get("analyst_only"))
    first_pass = "agent_only" if agent_only else ("analyst_only" if analyst_only else "combined")

    logger.info(
        "Starting %d comparison(s) with %s diffs (first_pass=%s).",
        total_pairs,
        diff_mode,
        first_pass,
    )

    for idx, (target, baseline) in enumerate(pairs, 1):
        try:
            target_name = oxide.api.get_colname_from_oid(target)
        except Exception:
            target_name = str(target)
        try:
            baseline_name = oxide.api.get_colname_from_oid(baseline)
        except Exception:
            baseline_name = str(baseline)

        logger.info("[%d/%d] %s -> %s", idx, total_pairs, target_name, baseline_name)

        pair_dir = os.path.join(outdir, _comparison_dir_name(target_name, baseline_name))
        result = run_one_comparison(target, baseline, pair_dir, opts)
        stats = dict(result.get("stats") or {})

        comparison_rows.append(
            {
                "index": idx,
                "target": target,
                "baseline": baseline,
                "pair_dir": pair_dir,
                **stats,
            }
        )

        rows = _annotate_per_function_rows(
            target,
            baseline,
            idx,
            list(result.get("per_function_results") or []),
        )
        if rows:
            per_function_rows.extend(rows)
        else:
            flagged_lookup = {
                (item["filepair_index"], item["function_index"])
                for item in (result.get("triage_index") or [])
            }
            per_function_rows.extend(
                _build_per_function_rows(
                    target,
                    baseline,
                    idx,
                    list(result.get("file_pairs") or []),
                    flagged_lookup,
                )
            )

    series_summary = {
        "diff_raw": diff_raw,
        "first_pass": first_pass,
        "comparisons": comparison_rows,
    }
    per_function_summary = {
        "diff_raw": diff_raw,
        "first_pass": first_pass,
        "functions": per_function_rows,
    }
    write_json(os.path.join(outdir, "comparisons_summary.json"), series_summary)
    write_json(os.path.join(outdir, "per_function_summary.json"), per_function_summary)

    total_flagged = sum(int(row.get("identified") or 0) for row in comparison_rows)
    total_modified = sum(int(row.get("total_modified_functions") or 0) for row in comparison_rows)
    total_filtered = sum(int(row.get("filtered_functions") or 0) for row in comparison_rows)
    total_input_tokens = sum(int(row.get("llm_input_tokens") or 0) for row in comparison_rows)
    total_output_tokens = sum(int(row.get("llm_output_tokens") or 0) for row in comparison_rows)
    total_tokens = sum(int(row.get("llm_total_tokens") or 0) for row in comparison_rows)

    series_metrics = {
        "diff_raw": diff_raw,
        "first_pass": first_pass,
        "comparisons": total_pairs,
        "total_modified_functions": total_modified,
        "total_filtered_functions": total_filtered,
        "total_flagged": total_flagged,
        "llm_input_tokens": total_input_tokens,
        "llm_output_tokens": total_output_tokens,
        "llm_total_tokens": total_tokens,
        "artifacts": {
            "comparisons_summary": "comparisons_summary.json",
            "per_function_summary": "per_function_summary.json",
            "series_metrics": "series_metrics.json",
            "series_summary": "series_summary.txt",
        },
    }
    write_json(os.path.join(outdir, "series_metrics.json"), series_metrics)
    write_text(
        os.path.join(outdir, "series_summary.txt"),
        "\n".join(
            [
                f"Diff mode: {diff_mode}",
                f"First pass: {first_pass}",
                f"Comparisons: {total_pairs}",
                f"Total modified functions: {total_modified}",
                f"Total filtered functions: {total_filtered}",
                f"Total flagged (final not_safe): {total_flagged}",
                f"LLM input tokens: {total_input_tokens}",
                f"LLM output tokens: {total_output_tokens}",
                f"LLM total tokens: {total_tokens}",
            ]
        ),
    )

    return {
        "outdir": outdir,
        "diff_raw": diff_raw,
        "first_pass": first_pass,
        "comparisons": comparison_rows,
        "functions": per_function_rows,
        "series_metrics": series_metrics,
    }


def _normalize_added_function(raw_item: Any) -> Optional[Dict[str, str]]:
    if isinstance(raw_item, dict):
        raw_addr = raw_item.get("target_func_addr", raw_item.get("address"))
        raw_name = raw_item.get("target_func_name", raw_item.get("name"))
    else:
        raw_addr = raw_item
        raw_name = None

    if raw_addr is None:
        return None

    target_addr = ensure_decimal_str(raw_addr)
    if not target_addr or target_addr.lower() == "none":
        return None

    out = {"target_func_addr": target_addr}
    if raw_name is not None:
        name_s = str(raw_name).strip()
        if name_s:
            out["target_func_name"] = name_s
    return out


def _extract_function_decomp_text(resp: Any, oid: Optional[str] = None) -> str:
    data = getattr(resp, "content", resp)

    if isinstance(data, dict) and oid and oid in data:
        data = data[oid]

    if isinstance(data, dict):
        decomp = data.get("decomp")
        if isinstance(decomp, list):
            return "\n".join(str(line) for line in decomp)
        if isinstance(decomp, str):
            return decomp
        return "" if decomp is None else str(decomp)

    if isinstance(data, list):
        return "\n".join(str(line) for line in data)

    if data is None:
        return ""

    return str(data)


def save_added_function_artifacts(
    target_oid: str,
    added_functions: List[Dict[str, Any]],
    fp_idx: int,
    outdir: str,
) -> None:
    if not added_functions:
        return

    filepair_dir = os.path.join(outdir, f"filepair_{fp_idx:02d}")
    added_dir = os.path.join(filepair_dir, "added_functions")
    os.makedirs(added_dir, exist_ok=True)

    for added_idx, item in enumerate(added_functions, 1):
        normalized = _normalize_added_function(item)
        if not normalized:
            continue
        target_addr = normalized["target_func_addr"]
        func_dir = os.path.join(
            added_dir,
            f"added_func_{added_idx:02d}__t{target_addr}",
        )
        os.makedirs(func_dir, exist_ok=True)

        try:
            resp = api.retrieve(
                "function_decomp",
                [target_oid],
                {"function_addr": target_addr},
            )
            decomp_text = _extract_function_decomp_text(resp, oid=target_oid)
        except Exception as exc:
            logger.warning(
                "function_decomp retrieval failed for added function %s in %s: %s",
                target_addr,
                target_oid,
                exc,
            )
            decomp_text = ""

        write_text(os.path.join(func_dir, "function_decomp.txt"), decomp_text)


def run_drift(target_cid: str, baseline_cid: str, filter_val: Optional[str] = None) -> Dict[str, Any]:
    out: Dict[str, Any] = {"file_pairs": []}
    filter_val = _normalize_filter_value(filter_val)
    try:
        if filter_val:
            filtered = drift.compare_collections([target_cid, baseline_cid], {"filter": filter_val}) or {}
        else:
            filtered = drift.compare_collections([target_cid, baseline_cid], {}) or {}
        raw_drift = drift.full_comparison([target_cid, baseline_cid], {}) or {}
    except Exception as exc:
        logger.error("compare_collections failed: %s", exc)
        return out

    per_file = (filtered.get("FUNCTION_CLASSIFICATION", {}) or {}).get("PER_FILE", {}) or {}
    raw_function_diffs = (raw_drift.get("FUNCTION_DIFFS", {}) or {})

    for file_key, file_entry in per_file.items():
        if not isinstance(file_key, (tuple, list)) or len(file_key) != 2:
            continue
        target_oid, baseline_oid = file_key[0], file_key[1]
        raw_entry = raw_function_diffs.get((target_oid, baseline_oid), {}) or {}
        raw_classification = raw_entry.get("function_classification", {}) or {}
        unmatched_target = raw_classification.get("unmatched_target", []) or []

        all_modified = file_entry.get("modified") or []

        if filter_val:
            search_space = file_entry.get(filter_val) or []
            included_pairs = {
                tuple((item.get("pair") or [None, None])[:2])
                for item in search_space
                if isinstance(item, dict)
            }
            excluded_functions = [
                item
                for item in all_modified
                if tuple((item.get("pair") or [None, None])[:2]) not in included_pairs
            ]
        else:
            search_space = all_modified
            excluded_functions = []

        search_space_out: List[Dict[str, Any]] = []
        added_functions_out: List[Dict[str, Any]] = []

        for item in search_space:
            features = item.get("features", {}) if isinstance(item, dict) else {}
            pair = item.get("pair", [None, None])
            target_addr = ensure_decimal_str(pair[0]) if pair and len(pair) > 0 else None
            baseline_addr = ensure_decimal_str(pair[1]) if pair and len(pair) > 1 else None

            search_space_out.append(
                {
                    "baseline_func_addr": baseline_addr,
                    "target_func_addr": target_addr,
                    "features": features,
                }
            )

        for raw_item in unmatched_target:
            normalized = _normalize_added_function(raw_item)
            if normalized:
                added_functions_out.append(normalized)

        out["file_pairs"].append(
            {
                "baseline_oid": baseline_oid,
                "target_oid": target_oid,
                "modified_functions": search_space_out,
                "added_functions": added_functions_out,
                "excluded_functions": excluded_functions,
            }
        )

    return out


def _get_empty_decomp_failure_messages(reason: str) -> Dict[str, str]:
    return _EMPTY_DECOMP_FAILURE_MESSAGES.get(
        reason,
        {
            "observation": "one side of the decompilation was empty. Triage skipped and recorded as failed.",
            "final_why": "One side of the decompilation was empty, so the system could not compute a two-sided function diff. The function was recorded as failed because triage did not run, not because the agent identified a trigger.",
        },
    )


def _build_per_function_rows(
    target: str,
    baseline: str,
    idx: int,
    file_pairs: List[Dict[str, Any]],
    flagged_lookup: Set[Tuple[int, int]],
) -> List[Dict[str, Any]]:
    rows = []
    for fp_idx, file_pair in enumerate(file_pairs, 1):
        baseline_oid = file_pair.get("baseline_oid")
        target_oid = file_pair.get("target_oid")
        for func_idx, modified in enumerate(file_pair.get("modified_functions", []) or [], 1):
            baseline_addr = ensure_decimal_str(modified.get("baseline_func_addr"))
            target_addr = ensure_decimal_str(modified.get("target_func_addr"))
            rows.append(
                {
                    "key": f"pair{idx}_fp{fp_idx}_func{func_idx}",
                    "comparison_index": idx,
                    "target_version": target,
                    "baseline_version": baseline,
                    "filepair_index": fp_idx,
                    "function_index": func_idx,
                    "target_addr": target_addr,
                    "baseline_addr": baseline_addr,
                    "target_oid": target_oid,
                    "baseline_oid": baseline_oid,
                    "flagged": bool((fp_idx, func_idx) in flagged_lookup),
                }
            )
    return rows


def _annotate_per_function_rows(
    target: str,
    baseline: str,
    idx: int,
    rows: List[Dict[str, Any]],
) -> List[Dict[str, Any]]:
    annotated: List[Dict[str, Any]] = []
    for row in rows or []:
        if not isinstance(row, dict):
            continue
        out = dict(row)
        fp_idx = int(out.get("filepair_index") or 0)
        func_idx = int(out.get("function_index") or 0)
        out["key"] = f"pair{idx}_fp{fp_idx}_func{func_idx}"
        out["comparison_index"] = idx
        out["target_version"] = target
        out["baseline_version"] = baseline
        if "flagged" not in out and "flagged_final" in out:
            out["flagged"] = bool(out.get("flagged_final"))
        if "label" not in out and "final_label" in out:
            out["label"] = out.get("final_label")
        if "input_tokens" not in out and "llm_input_tokens" in out:
            out["input_tokens"] = int(out.get("llm_input_tokens") or 0)
        if "output_tokens" not in out and "llm_output_tokens" in out:
            out["output_tokens"] = int(out.get("llm_output_tokens") or 0)
        if "total_tokens" not in out and "llm_total_tokens" in out:
            out["total_tokens"] = int(out.get("llm_total_tokens") or 0)
        annotated.append(out)
    return annotated


def _make_function_dir(outdir: str, fp_idx: int, func_idx: int, baddr: str, taddr: str) -> str:
    return os.path.join(
        outdir,
        f"filepair_{fp_idx:02d}",
        "modified_functions",
        f"b{baddr}__t{taddr}",
    )


def _reconstruct_res_from_analysis(analysis: Dict[str, Any], func_dir: str) -> Dict[str, Any]:
    timing = analysis.get("timing") or {}
    cost = analysis.get("cost") or {}
    return {
        "label": analysis.get("label", "not_safe"),
        "why": analysis.get("why", ""),
        "flagged": bool(analysis.get("flagged", True)),
        "verdict": analysis.get("verdict", ""),
        "func_dir": func_dir,
        "triage_ran": bool(analysis.get("triage_ran", False)),
        "failure_reason": analysis.get("failure_reason"),
        "failure_detail": analysis.get("failure_detail", ""),
        "diff_elapsed_s": float(timing.get("diff_elapsed_s") or 0.0),
        "llm_elapsed_s": float(timing.get("llm_elapsed_s") or 0.0),
        "llm_input_tokens": int(cost.get("llm_input_tokens") or 0),
        "llm_output_tokens": int(cost.get("llm_output_tokens") or 0),
        "llm_total_tokens": int(cost.get("llm_total_tokens") or 0),
    }


def _error_result(
    why: str,
    *,
    failure_reason: str,
    failure_detail: str = "",
) -> Dict[str, Any]:
    return {
        "label": "failed",
        "trigger": "",
        "why": _coerce_str(why),
        "analysis_md": "",
        "final_md": "",
        "failure_reason": failure_reason,
        "failure_detail": _coerce_str(failure_detail),
        "llm_elapsed_s": 0.0,
        "llm_input_tokens": 0,
        "llm_output_tokens": 0,
        "llm_total_tokens": 0,
    }


def run_triage(
    unified_diff: str,
    notes: Dict[str, Any],
    *,
    analyst_only: bool = False,
    agent_only: bool = False,
    trace_path: Optional[str] = None,
    fp_idx: int = 0,
    fp_total: int = 0,
    func_idx: int = 0,
    func_total: int = 0,
) -> Dict[str, Any]:
    """Run the triage pipeline via TRIAGE_GRAPH and return a combined result dict."""
    if TRIAGE_GRAPH is None or LLM is None:
        msg = "Deep agent triage is not initialized."
        notes["observations"].append(msg)
        return _error_result(msg, failure_reason="deep_agent_uninitialized")

    diff_text = ascii_sanitize(unified_diff)

    log_handler: Optional[logging.FileHandler] = None
    if trace_path:
        log_path = os.path.join(os.path.dirname(os.path.abspath(trace_path)), "triage.log")
        try:
            os.makedirs(os.path.dirname(log_path), exist_ok=True)
            log_handler = logging.FileHandler(log_path, mode="w", encoding="utf-8")
            log_handler.setFormatter(_formatter)
            logger.addHandler(log_handler)
        except Exception:
            log_handler = None

    try:
        initial_state: TriageState = {
            "diff": diff_text,
            "fp_idx": fp_idx,
            "fp_total": fp_total,
            "func_idx": func_idx,
            "func_total": func_total,
            "notes": notes,
            "trace_path": trace_path,
            "analyst_only": analyst_only,
            "agent_only": agent_only,
            "analyst_raw": None,
            "analyst_json": None,
            "analyst_meta": None,
            "agent_result": None,
            "final_json": None,
        }
        final_state = TRIAGE_GRAPH.invoke(initial_state)
    finally:
        if log_handler is not None:
            logger.removeHandler(log_handler)
            log_handler.close()

    analyst_json = final_state.get("analyst_json") or {}
    analyst_meta = final_state.get("analyst_meta") or {}
    agent_result = final_state.get("agent_result") or {}
    final_json = final_state.get("final_json")

    analyst_input_tokens = int(analyst_meta.get("input_tokens") or 0)
    analyst_output_tokens = int(analyst_meta.get("output_tokens") or 0)
    analyst_tokens = int(analyst_meta.get("total_tokens") or 0)
    analyst_elapsed = float(analyst_meta.get("duration_s") or 0.0)
    agent_input_tokens = int(agent_result.get("llm_input_tokens") or 0)
    agent_output_tokens = int(agent_result.get("llm_output_tokens") or 0)
    agent_tokens = int(agent_result.get("llm_total_tokens") or 0)
    agent_elapsed = float(agent_result.get("llm_elapsed_s") or 0.0)

    # If analyst cleared it (no agent ran), use analyst result as final
    if final_json is None:
        final_json = {
            "label": analyst_json.get("label", "safe"),
            "trigger": analyst_json.get("trigger", ""),
            "why": analyst_json.get("why", ""),
        }

    failure_reason = agent_result.get("failure_reason") if agent_result else None

    return {
        "label": final_json.get("label", "failed"),
        "trigger": final_json.get("trigger", ""),
        "why": final_json.get("why", ""),
        "analyst_label": analyst_json.get("label", ""),
        "analyst_trigger": analyst_json.get("trigger", ""),
        "analyst_elapsed_s": analyst_elapsed,
        "analyst_input_tokens": analyst_input_tokens,
        "analyst_output_tokens": analyst_output_tokens,
        "analyst_tokens": analyst_tokens,
        "agent_ran": bool(agent_result),
        "analysis_md": _coerce_str(agent_result.get("analysis_md")),
        "final_md": _coerce_str(agent_result.get("final_md")),
        "failure_reason": failure_reason,
        "failure_detail": _coerce_str(agent_result.get("failure_detail")),
        "llm_elapsed_s": analyst_elapsed + agent_elapsed,
        "llm_input_tokens": analyst_input_tokens + agent_input_tokens,
        "llm_output_tokens": analyst_output_tokens + agent_output_tokens,
        "llm_total_tokens": analyst_tokens + agent_tokens,
    }


def _run_agent_node(
    diff_text: str,
    notes: Dict[str, Any],
    trace_path: Optional[str],
    progress_label: str = "",
) -> Dict[str, Any]:
    """Run the deep agent on a pre-sanitized diff. Returns a result dict."""
    if LLM is None:
        msg = "Deep agent triage is not initialized."
        notes["observations"].append(msg)
        return _error_result(msg, failure_reason="deep_agent_uninitialized")

    file_mirror: Dict[str, str] = {}
    agent = _build_triage_agent(main_model=LLM, file_mirror=file_mirror)

    prompt = (
        "Analyze /inputs/unified_diff.txt.\n"
        "Write a provisional analysis to /work/analysis.md.\n"
        "Write your final decision to /work/final.md.\n"
        "Return the final answer using the configured structured response.\n"
    )

    logger.info("%s agent node start diff=%d chars", progress_label, len(diff_text))
    out: Any = None
    invoke_elapsed_s = 0.0
    invoke_t0 = time.perf_counter()
    try:
        _append_trace_line(trace_path, "[   0.00s] [agent] start", truncate=True)
        _append_trace_line(trace_path, "[   0.00s] [agent] mode: astream (live trace) + aget_state (final output)")
        config = {"configurable": {"thread_id": f"delt_deep_agent_{time.time_ns()}"}}
        payload = {
            "messages": [{"role": "user", "content": prompt}],
            "files": {"/inputs/unified_diff.txt": create_file_data(diff_text)},
        }
        out = _invoke_agent_with_timeout(
            agent, payload, config=config,
            timeout_s=_DEFAULT_REQUEST_TIMEOUT_S, trace_path=trace_path,
        )
        invoke_elapsed_s = time.perf_counter() - invoke_t0
    except TimeoutError as exc:
        msg = f"Deep agent timed out: {exc}."
        notes["observations"].append(msg)
        _append_trace_line(trace_path,
            f"[{time.perf_counter() - invoke_t0:7.2f}s] [agent] error: timeout {exc}")
        return _error_result(
            f"Deep agent timed out after {_DEFAULT_REQUEST_TIMEOUT_S:g}s before reaching a final decision.",
            failure_reason="timeout", failure_detail=str(exc),
        )
    except Exception as exc:
        detail = str(exc)
        failure_reason = "timeout" if "timeout" in detail.lower() else "invoke_failed"
        notes["observations"].append(f"Deep agent invoke failed: {exc}.")
        why = ("Deep agent timed out before reaching a final decision."
               if failure_reason == "timeout"
               else "Deep agent triage pipeline failed before reaching a final decision.")
        _append_trace_line(trace_path,
            f"[{time.perf_counter() - invoke_t0:7.2f}s] [agent] error: {failure_reason} {exc}")
        return _error_result(why, failure_reason=failure_reason, failure_detail=detail)

    analysis_md = _coerce_str(file_mirror.get("/work/analysis.md"))
    final_md = _coerce_str(file_mirror.get("/work/final.md"))
    structured_response = _state_field(out, "structured_response")
    final, ok = _normalize_final_payload(structured_response)
    messages = _state_field(out, "messages")
    llm_usage = _collect_llm_usage_counts(messages)
    llm_input_tokens = int(llm_usage.get("input_tokens") or 0)
    llm_output_tokens = int(llm_usage.get("output_tokens") or 0)
    llm_total_tokens = int(llm_usage.get("total_tokens") or 0)

    if not ok or final is None:
        why = "Deep agent did not produce a valid structured final answer before the run ended."
        notes["observations"].append(why)
        _append_trace_line(trace_path,
            f"[{invoke_elapsed_s:7.2f}s] [agent] error: missing_final_answer")
        result = _error_result(why, failure_reason="missing_final_answer")
        result["analysis_md"] = analysis_md
        result["final_md"] = final_md
        result["llm_elapsed_s"] = invoke_elapsed_s
        result["llm_input_tokens"] = llm_input_tokens
        result["llm_output_tokens"] = llm_output_tokens
        result["llm_total_tokens"] = llm_total_tokens
        return result

    label = _coerce_label(final.get("label"))
    label = label if label in {"safe", "not_safe"} else "failed"
    trigger = _coerce_str(final.get("trigger"))
    why = _coerce_str(final.get("why"))
    _append_trace_line(trace_path,
        f"[{invoke_elapsed_s:7.2f}s] [agent] final: label={label} trigger={_preview_text(trigger, limit=80)}")
    if analysis_md.strip():
        _append_trace_line(trace_path, f"[{invoke_elapsed_s:7.2f}s] [agent] wrote /work/analysis.md")
    if final_md.strip():
        _append_trace_line(trace_path, f"[{invoke_elapsed_s:7.2f}s] [agent] wrote /work/final.md")

    return {
        "label": label,
        "trigger": trigger,
        "why": why,
        "analysis_md": analysis_md,
        "final_md": final_md,
        "failure_reason": None,
        "failure_detail": "",
        "llm_elapsed_s": invoke_elapsed_s,
        "llm_input_tokens": llm_input_tokens,
        "llm_output_tokens": llm_output_tokens,
        "llm_total_tokens": llm_total_tokens,
    }


def _write_trace_view(trace_path: str, out_path: str) -> None:
    """Write a clean human-readable summary of an agent_trace.log to out_path."""
    TS_RE  = re.compile(r'^\[\s*([\d.]+)s\] \[agent\] (.+)$')
    RES_RE = re.compile(r'^tool result \[([^\]]+)\]: (.*)$', re.DOTALL)
    FIN_RE = re.compile(r"label='(\w+)' trigger='([^']*)' why='([^']*)'")
    WF_RE  = re.compile(r'Updated file (/\S+)')

    def trunc(s: str, n: int = 300) -> str:
        s = s.strip()
        return s[:n] + "…" if len(s) > n else s

    def fmt_result(name: str, content: str) -> str:
        if name == "write_file":
            m = WF_RE.search(content)
            return f"  → wrote {m.group(1) if m else '?'}"
        if name == "write_todos":
            items = re.findall(r"'content': '([^']+)', 'status': '([^']+)'", content)
            parts = [f"[{'x' if s=='completed' else '·' if s=='in_progress' else ' '}] {t}" for t, s in items]
            return "  " + "  ".join(parts)
        if name == "FinalDecisionSchema":
            return ""
        return "  " + trunc(content)

    if not os.path.exists(trace_path):
        return

    raw: List[Tuple[float, str]] = []
    for line in open(trace_path).read().splitlines():
        m = TS_RE.match(line)
        if m:
            raw.append((float(m.group(1)), m.group(2)))

    events: List[Tuple[float, str, Any]] = []
    text_buf: List[str] = []
    text_ts: Optional[float] = None

    def flush_text() -> None:
        nonlocal text_buf, text_ts
        if text_buf:
            events.append((text_ts, "TEXT", "".join(text_buf).strip()))  # type: ignore[arg-type]
            text_buf[:] = []
            text_ts = None

    for ts, body in raw:
        if body.startswith("text: "):
            if text_ts is None:
                text_ts = ts
            text_buf.append(body[6:])
            continue
        flush_text()
        if body.startswith("tool call: "):
            events.append((ts, "CALL", body[11:]))
        elif body.startswith("tool result ["):
            m2 = RES_RE.match(body)
            if m2:
                events.append((ts, "RESULT", (m2.group(1), m2.group(2))))
        elif body.startswith("start "):
            events.append((ts, "START", body[6:]))
        elif body.startswith("final: "):
            events.append((ts, "FINAL", body[7:]))
        elif body.startswith("subagent call: "):
            events.append((ts, "SUB_CALL", body[15:]))
        elif body.startswith("subagent result: "):
            events.append((ts, "SUB_DONE", body[17:]))
        elif any(w in body.lower() for w in ("error", "timeout", "failed")):
            events.append((ts, "ERROR", body))
    flush_text()

    ind = " " * 17
    lines_out: List[str] = []
    for ts, kind, data in events:
        ts_str = f"[{ts:7.2f}s]"
        if kind == "START":
            lines_out.append(f"{ts_str}  START     {data}")
        elif kind == "CALL":
            lines_out.append(f"\n{ts_str}  CALL      {data}")
        elif kind == "RESULT":
            name, content = data
            out = fmt_result(name, content)
            if out:
                lines_out.append(f"{ts_str}           {out}")
        elif kind == "TEXT":
            wrapped = textwrap.fill(trunc(data, 800), width=100, subsequent_indent=ind + "  ")
            lines_out.append(f"\n{ts_str}  THINK     {wrapped}")
        elif kind == "SUB_CALL":
            lines_out.append(f"\n{ts_str}  SUBAGENT  {trunc(data, 200)}")
        elif kind == "SUB_DONE":
            lines_out.append(f"{ts_str}  SUB_DONE  {trunc(data, 200)}")
        elif kind == "FINAL":
            m3 = FIN_RE.search(data)
            lines_out.append("")
            if m3:
                lv, tv, wv = m3.group(1), m3.group(2), m3.group(3)
                lines_out.append(f"{ts_str}  FINAL     label={lv}")
                if tv:
                    lines_out.append(f"{ind}  trigger={tv}")
                why_w = textwrap.fill(wv, width=100, initial_indent=ind + "  why=", subsequent_indent=ind + "      ")
                lines_out.append(why_w)
            else:
                lines_out.append(f"{ts_str}  FINAL     {data}")
        elif kind == "ERROR":
            lines_out.append(f"\n{ts_str}  ERROR     {data}")

    write_text(out_path, "\n".join(lines_out) + "\n")


def analyze_function_pair(
    baseline_oid: str,
    target_oid: str,
    baddr: str,
    taddr: str,
    fp_idx: int,
    func_idx: int,
    outdir: str,
    opts: Dict[str, Any],
    fp_total: int = 0,
    func_total: int = 0,
) -> Dict[str, Any]:
    func_dir = _make_function_dir(outdir, fp_idx, func_idx, baddr, taddr)
    diff_raw = bool(opts.get("_diff_raw"))
    diff_compact = bool(opts.get("_diff_compact"))
    analyst_only = bool(opts.get("analyst_only"))
    agent_only = bool(opts.get("agent_only"))

    os.makedirs(func_dir, exist_ok=True)
    notes_path = os.path.join(func_dir, "notes.json")
    notes: Dict[str, Any] = {"observations": [], "artifacts": []}
    analysis_path = os.path.join(func_dir, "analysis.json")
    trace_path = os.path.join(func_dir, "agent_trace.log")

    def _write_analysis(
        *,
        label: str,
        why: str,
        triage_ran: bool,
        failure_reason: Optional[str],
        failure_detail: str,
        diff_elapsed_s: float,
        llm_elapsed_s: float,
        llm_input_tokens: int,
        llm_output_tokens: int,
        llm_total_tokens: int,
        trigger: str = "",
        analysis_md: str = "",
        final_md: str = "",
    ) -> Dict[str, Any]:
        label = _coerce_result_label(label, failure_reason)
        flagged = label == "not_safe"
        verdict_label = "needs further inspection" if flagged else ("safe" if label == "safe" else "failed")
        verdict = f"Label: {verdict_label} - {why or 'model provided no reason'}"

        if analysis_md.strip():
            write_text(os.path.join(func_dir, "analysis.md"), analysis_md)
            notes["artifacts"].append({"kind": "agent_analysis", "path": "analysis.md"})
        if final_md.strip():
            write_text(os.path.join(func_dir, "final.md"), final_md)
            notes["artifacts"].append({"kind": "agent_final", "path": "final.md"})
        if os.path.exists(trace_path) and os.path.getsize(trace_path) > 0:
            notes["artifacts"].append({"kind": "agent_trace", "path": "agent_trace.log"})

        write_json(notes_path, notes)
        write_json(
            analysis_path,
            {
                "label": label,
                "trigger": trigger,
                "why": why,
                "flagged": flagged,
                "verdict": verdict,
                "triage_ran": triage_ran,
                "failure_reason": failure_reason,
                "failure_detail": failure_detail,
                "analyst_only": analyst_only,
                "agent_only": agent_only,
                "artifacts": {
                    "analysis_md": bool(analysis_md.strip()),
                    "final_md": bool(final_md.strip()),
                    "agent_trace": bool(os.path.exists(trace_path) and os.path.getsize(trace_path) > 0),
                },
                "timing": {
                    "diff_elapsed_s": diff_elapsed_s,
                    "llm_elapsed_s": llm_elapsed_s,
                },
                "cost": {
                    "llm_input_tokens": llm_input_tokens,
                    "llm_output_tokens": llm_output_tokens,
                    "llm_total_tokens": llm_total_tokens,
                },
            },
        )
        write_text(os.path.join(func_dir, "verdict.txt"), verdict)
        return {
            "label": label,
            "why": why,
            "flagged": flagged,
            "verdict": verdict,
            "func_dir": func_dir,
            "triage_ran": triage_ran,
            "failure_reason": failure_reason,
            "failure_detail": failure_detail,
            "diff_elapsed_s": diff_elapsed_s,
            "llm_elapsed_s": llm_elapsed_s,
            "llm_input_tokens": llm_input_tokens,
            "llm_output_tokens": llm_output_tokens,
            "llm_total_tokens": llm_total_tokens,
        }

    if opts.get("no_triage"):
        failure_reason = "triage_disabled"

        diff_t0 = time.perf_counter()
        diff = oxide.retrieve(
            "function_decomp_diff",
            [target_oid, baseline_oid],
            {
                "target": taddr,
                "baseline": baddr,
                "raw": diff_raw,
                "compact": (False if diff_raw else diff_compact),
            },
        )
        diff_elapsed_s = time.perf_counter() - diff_t0
        diff_info = normalize_function_decomp_diff_response(diff)
        write_diff_artifacts(func_dir, diff_info["unified"], diff_info["artifact_meta"])
        notes["artifacts"].append({"kind": "diff_meta", "path": "diff_meta.json"})
        return _write_analysis(
            label="failed",
            why="Triage disabled by configuration.",
            triage_ran=False,
            failure_reason=failure_reason,
            failure_detail="",
            diff_elapsed_s=diff_elapsed_s,
            llm_elapsed_s=0.0,
            llm_input_tokens=0,
            llm_output_tokens=0,
            llm_total_tokens=0,
        )

    triage_ran = False
    failure_reason: Optional[str] = None

    diff_t0 = time.perf_counter()
    diff = oxide.retrieve(
        "function_decomp_diff",
        [target_oid, baseline_oid],
        {
            "target": taddr,
            "baseline": baddr,
            "raw": diff_raw,
            "compact": (False if diff_raw else diff_compact),
        },
    )
    diff_elapsed_s = time.perf_counter() - diff_t0
    diff_info = normalize_function_decomp_diff_response(diff)
    write_diff_artifacts(func_dir, diff_info["unified"], diff_info["artifact_meta"])
    notes["artifacts"].append({"kind": "diff_meta", "path": "diff_meta.json"})

    if diff_info["tool_error"]:
        failure_reason = "diff_tool_error"
        notes["observations"].append(f"diff tool failed: {diff_info.get('error')!r}")
        return _write_analysis(
            label="failed",
            why="Diff generation failed before triage could run.",
            triage_ran=False,
            failure_reason=failure_reason,
            failure_detail="",
            diff_elapsed_s=diff_elapsed_s,
            llm_elapsed_s=0.0,
            llm_input_tokens=0,
            llm_output_tokens=0,
            llm_total_tokens=0,
        )

    empty_decomp_reason = diff_info.get("empty_decomp_reason")
    if empty_decomp_reason:
        failure_reason = str(empty_decomp_reason)
        messages = _get_empty_decomp_failure_messages(failure_reason)
        notes["observations"].append(messages["observation"])
        return _write_analysis(
            label="failed",
            why=messages["final_why"],
            triage_ran=False,
            failure_reason=failure_reason,
            failure_detail="",
            diff_elapsed_s=diff_elapsed_s,
            llm_elapsed_s=0.0,
            llm_input_tokens=0,
            llm_output_tokens=0,
            llm_total_tokens=0,
        )

    unified = diff_info["unified"] or ""

    llm_elapsed_s = 0.0
    llm_input_tokens = 0
    llm_output_tokens = 0
    llm_total_tokens = 0
    trigger = ""

    if unified.strip():
        triage_ran = True
        triage = run_triage(
            unified_diff=unified,
            notes=notes,
            analyst_only=analyst_only,
            agent_only=agent_only,
            trace_path=trace_path,
            fp_idx=fp_idx,
            fp_total=fp_total,
            func_idx=func_idx,
            func_total=func_total,
        )
        label = triage.get("label", "failed")
        why = (triage.get("why") or "").strip()
        trigger = (triage.get("trigger") or "").strip()
        failure_reason = triage.get("failure_reason")
        failure_detail = (triage.get("failure_detail") or "").strip()
        llm_elapsed_s = float(triage.get("llm_elapsed_s") or 0.0)
        llm_input_tokens = int(triage.get("llm_input_tokens") or 0)
        llm_output_tokens = int(triage.get("llm_output_tokens") or 0)
        llm_total_tokens = int(triage.get("llm_total_tokens") or 0)
    else:
        failure_reason = "empty_unified_diff"
        failure_detail = ""
        notes["observations"].append("empty unified diff; recorded as failed")
        label = "failed"
        why = "Triage did not run because the unified diff was empty."
        triage = {
            "analysis_md": "",
            "final_md": "",
        }

    label = _coerce_result_label(label, failure_reason)
    if failure_detail and label == "failed":
        why = f"{why} Detail: {failure_detail}".strip()
    return _write_analysis(
        label=label,
        trigger=trigger,
        why=why,
        triage_ran=triage_ran,
        failure_reason=failure_reason,
        failure_detail=failure_detail,
        diff_elapsed_s=diff_elapsed_s,
        llm_elapsed_s=llm_elapsed_s,
        llm_input_tokens=llm_input_tokens,
        llm_output_tokens=llm_output_tokens,
        llm_total_tokens=llm_total_tokens,
        analysis_md=_coerce_str(triage.get("analysis_md")),
        final_md=_coerce_str(triage.get("final_md")),
    )


def run_one_comparison(target: str, baseline: str, outdir: str, opts: Dict[str, Any]) -> Dict[str, Any]:
    os.makedirs(outdir, exist_ok=True)

    if "filter" in opts:
        filter_val = _normalize_filter_value(opts.get("filter"))
    else:
        filter_val = "Call_OR_Control_Modified"
    logger.info(
        "Invoking drift with target='%s', baseline='%s', filter='%s'",
        target,
        baseline,
        filter_val if filter_val is not None else "<none>",
    )

    total_t0 = time.perf_counter()

    drift_t0 = time.perf_counter()
    drift_res = run_drift(target, baseline, filter_val)
    drift_elapsed_s = time.perf_counter() - drift_t0

    drift_json = coerce_json_like(getattr(drift_res, "content", drift_res)) or {}
    write_json(os.path.join(outdir, "drift_raw.json"), drift_json)

    file_pairs: List[Dict[str, Any]] = drift_json.get("file_pairs", []) or []

    report_lines: List[str] = []
    report_lines.append("# Firmware Triage Report (binary suspicion)")
    target_name = str(target)
    baseline_name = str(baseline)

    report_lines.append(f"Target CID:   {target}")
    try:
        target_name = oxide.api.get_colname_from_oid(target)
        report_lines.append(f"Target Name:  {target_name}")
    except Exception:
        report_lines.append("Target Name:  <unavailable>")

    report_lines.append(f"Baseline CID: {baseline}")
    try:
        baseline_name = oxide.api.get_colname_from_oid(baseline)
        report_lines.append(f"Baseline Name:{baseline_name}")
    except Exception:
        report_lines.append("Baseline Name:<unavailable>")

    if filter_val:
        report_lines.append(f"Filter:       {filter_val}")
    report_lines.append("")

    triage_index: List[Dict[str, Any]] = []
    per_function_results: List[Dict[str, Any]] = []

    total_modified_all = 0
    total_modified_filtered = 0

    flagged_filtered = 0
    safe_filtered = 0
    failed_filtered = 0
    skipped_filtered = 0
    failure_reason_counts: Dict[str, int] = {}

    sum_diff_elapsed_s = 0.0
    sum_llm_elapsed_s = 0.0
    sum_llm_input_tokens = 0
    sum_llm_output_tokens = 0
    sum_llm_total_tokens = 0

    if not file_pairs:
        report_lines.append("No file pairs or modifications were reported by drift.")
        logger.info("No file pairs or modifications were reported by drift.")
    else:
        report_lines.append(f"Found {len(file_pairs)} file pair(s).\n")
        logger.info("Processing %d file pair(s).", len(file_pairs))

    for fp_idx, file_pair in enumerate(file_pairs, 1):
        baseline_oid = file_pair.get("baseline_oid")
        target_oid = file_pair.get("target_oid")
        filtered_mods = file_pair.get("modified_functions", []) or []
        added_funcs = file_pair.get("added_functions", []) or []
        excluded_mods = file_pair.get("excluded_functions", []) or []

        try:
            total_modified_all += len(filtered_mods) + len(excluded_mods)
        except Exception:
            total_modified_all += len(filtered_mods)

        total_modified_filtered += len(filtered_mods)

        report_lines.append(f"## File Pair {fp_idx}")
        report_lines.append(f"- target_oid:   {target_oid}")
        report_lines.append(f"- baseline_oid: {baseline_oid}")
        report_lines.append(f"- modified functions (filtered): {len(filtered_mods)}")
        report_lines.append(f"- added functions: {len(added_funcs)}")
        if excluded_mods:
            try:
                report_lines.append(f"- modified functions (excluded by filter): {len(excluded_mods)}")
            except Exception:
                report_lines.append("- modified functions (excluded by filter): <unknown>")
        report_lines.append("")

        logger.info(
            "[file %d/%d] filtered=%d added=%d excluded=%s",
            fp_idx,
            len(file_pairs),
            len(filtered_mods),
            len(added_funcs),
            len(excluded_mods) if hasattr(excluded_mods, "__len__") else "unknown",
        )

        save_added_function_artifacts(
            target_oid=target_oid,
            added_functions=added_funcs,
            fp_idx=fp_idx,
            outdir=outdir,
        )

        prog = progress.Progress(len(filtered_mods))

        for func_idx, modified in enumerate(filtered_mods, 1):
            baseline_addr = ensure_decimal_str(modified.get("baseline_func_addr"))
            target_addr = ensure_decimal_str(modified.get("target_func_addr"))
            progress_label = _progress_label(
                fp_idx=fp_idx,
                fp_total=len(file_pairs),
                func_idx=func_idx,
                func_total=len(filtered_mods),
            )
            logger.info(
                "%s start baseline_addr=%s target_addr=%s",
                progress_label,
                baseline_addr,
                target_addr,
            )

            func_dir = _make_function_dir(outdir, fp_idx, func_idx, baseline_addr, target_addr)
            analysis_path = os.path.join(func_dir, "analysis.json")
            result = None
            if os.path.exists(analysis_path):
                try:
                    analysis_cached = read_json(analysis_path)
                    result = _reconstruct_res_from_analysis(analysis_cached, func_dir)
                except Exception as exc:
                    logger.warning(
                        "%s failed to load cached result: %s. Re-running.",
                        progress_label,
                        exc,
                    )
                else:
                    logger.info("%s using cached result", progress_label)

            if result is None:
                result = analyze_function_pair(
                    baseline_oid=baseline_oid,
                    target_oid=target_oid,
                    baddr=baseline_addr,
                    taddr=target_addr,
                    fp_idx=fp_idx,
                    fp_total=len(file_pairs),
                    func_idx=func_idx,
                    func_total=len(filtered_mods),
                    outdir=outdir,
                    opts=opts,
                )
                _write_trace_view(
                    os.path.join(func_dir, "agent_trace.log"),
                    os.path.join(func_dir, "trace_view.txt"),
                )

            sum_diff_elapsed_s += float(result.get("diff_elapsed_s") or 0.0)
            sum_llm_elapsed_s += float(result.get("llm_elapsed_s") or 0.0)
            sum_llm_input_tokens += int(result.get("llm_input_tokens") or 0)
            sum_llm_output_tokens += int(result.get("llm_output_tokens") or 0)
            sum_llm_total_tokens += int(result.get("llm_total_tokens") or 0)

            final_label = _coerce_result_label(result.get("label"), result.get("failure_reason"))
            flagged_final = bool(final_label == "not_safe")

            per_function_results.append(
                {
                    "filepair_index": fp_idx,
                    "function_index": func_idx,
                    "baseline_oid": baseline_oid,
                    "target_oid": target_oid,
                    "baseline_addr": baseline_addr,
                    "target_addr": target_addr,
                    "final_label": final_label,
                    "flagged_final": flagged_final,
                    "diff_elapsed_s": float(result.get("diff_elapsed_s") or 0.0),
                    "llm_elapsed_s": float(result.get("llm_elapsed_s") or 0.0),
                    "llm_input_tokens": int(result.get("llm_input_tokens") or 0),
                    "llm_output_tokens": int(result.get("llm_output_tokens") or 0),
                    "llm_total_tokens": int(result.get("llm_total_tokens") or 0),
                    "triage_ran": bool(result.get("triage_ran")),
                    "failure_reason": result.get("failure_reason"),
                    "failure_detail": result.get("failure_detail", ""),
                }
            )

            failure_reason = _coerce_str(result.get("failure_reason"))
            if failure_reason and failure_reason not in _EMPTY_DECOMP_FAILURE_MESSAGES:
                failure_reason_counts[failure_reason] = failure_reason_counts.get(failure_reason, 0) + 1

            if flagged_final:
                flagged_filtered += 1
                triage_index.append(
                    {
                        "filepair_index": fp_idx,
                        "function_index": func_idx,
                        "baseline_addr": baseline_addr,
                        "target_addr": target_addr,
                        "label": final_label,
                        "why": result.get("why"),
                        "verdict": result.get("verdict"),
                        "dir": result.get("func_dir"),
                        "baseline_oid": baseline_oid,
                        "target_oid": target_oid,
                    }
                )
            elif final_label == "failed":
                failed_filtered += 1
            elif final_label == "skipped":
                skipped_filtered += 1
            else:
                safe_filtered += 1

            logger.info(
                "%s done label=%s flagged=%s diff=%.2fs llm=%.2fs tokens_in=%d tokens_out=%d tokens_total=%d",
                progress_label,
                final_label,
                flagged_final,
                float(result.get("diff_elapsed_s") or 0.0),
                float(result.get("llm_elapsed_s") or 0.0),
                int(result.get("llm_input_tokens") or 0),
                int(result.get("llm_output_tokens") or 0),
                int(result.get("llm_total_tokens") or 0),
            )

            prog.tick()

    overall_safe = safe_filtered + (total_modified_all - total_modified_filtered)
    elapsed_s = time.perf_counter() - total_t0
    triage_elapsed_s_excluding_drift = max(0.0, elapsed_s - drift_elapsed_s)
    other_elapsed_s = max(0.0, triage_elapsed_s_excluding_drift - (sum_diff_elapsed_s + sum_llm_elapsed_s))

    gt = opts.get("_ground_truth") or {}
    gt_norm = get_ground_truth_for_target(gt, target_name)

    hit_final = None
    gt_in_filtered = None
    gt_targets = None
    gt_compromised_count = None
    tp_final = None
    fp_final = None

    if gt_norm:
        gt_targets = gt_norm.get("targets", [])
        gt_compromised_count = len(gt_targets)

        gt_matched: Set[int] = {
            id(row) for row in per_function_results if gt_row_matches_any(row, gt_norm)
        }

        gt_in_filtered = bool(gt_matched)

        flagged_final_ids: Set[int] = {id(row) for row in per_function_results if row.get("flagged_final")}

        hit_final = bool(flagged_final_ids & gt_matched)
        tp_final = len(flagged_final_ids & gt_matched)
        fp_final = len(flagged_final_ids - gt_matched)

    identified = len(triage_index)
    fp_rate_final = None
    if gt_norm and total_modified_all:
        fp_rate_final = float(fp_final) / float(total_modified_all) if fp_final is not None else None

    stats = {
        "target": target,
        "baseline": baseline,
        "diff_raw": bool(opts.get("_diff_raw")),
        "total_modified_functions": total_modified_all,
        "filtered_functions": total_modified_filtered,
        "safe_overall": overall_safe,
        "identified": identified,
        "final_not_safe_filtered": flagged_filtered,
        "final_safe_filtered": safe_filtered,
        "final_failed_filtered": failed_filtered,
        "final_skipped_filtered": skipped_filtered,
        "failure_reason_counts": failure_reason_counts,
        "elapsed_s": elapsed_s,
        "drift_elapsed_s": drift_elapsed_s,
        "triage_elapsed_s_excluding_drift": triage_elapsed_s_excluding_drift,
        "diff_elapsed_s": sum_diff_elapsed_s,
        "llm_elapsed_s": sum_llm_elapsed_s,
        "other_elapsed_s": other_elapsed_s,
        "llm_input_tokens": sum_llm_input_tokens,
        "llm_output_tokens": sum_llm_output_tokens,
        "llm_total_tokens": sum_llm_total_tokens,
        "gt_compromised_count": gt_compromised_count,
        "gt_targets": gt_targets,
        "gt_in_filtered": gt_in_filtered,
        "hit_final": hit_final,
        "tp_final": tp_final,
        "fp_final": fp_final,
        "fp_rate_final": fp_rate_final,
    }

    write_text(os.path.join(outdir, "final_report.txt"), "\n".join(report_lines))
    write_json(os.path.join(outdir, "triage_index.json"), triage_index)
    write_json(os.path.join(outdir, "per_function_results.json"), per_function_results)
    write_json(os.path.join(outdir, "stats.json"), stats)

    logger.info(
        "Done %s -> %s: modified_all=%d filtered=%d identified=%d hit_final=%s elapsed=%.2fs (drift=%.2fs llm=%.2fs tokens_in=%d tokens_out=%d tokens_total=%d)",
        target_name,
        baseline_name,
        total_modified_all,
        total_modified_filtered,
        identified,
        hit_final,
        elapsed_s,
        drift_elapsed_s,
        sum_llm_elapsed_s,
        sum_llm_input_tokens,
        sum_llm_output_tokens,
        sum_llm_total_tokens,
    )

    return {
        "target": target,
        "baseline": baseline,
        "stats": stats,
        "triage_index": triage_index,
        "per_function_results": per_function_results,
        "file_pairs": file_pairs,
    }


def llm_filter(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    pairs = _resolve_llm_filter_pairs(args, opts)

    outdir: str = opts.get("outdir", "out_delt_deep_agent")
    run_opts = _prepare_llm_filter_run_opts(opts)
    run_opts["_diff_raw"] = bool(opts.get("raw"))
    run_opts["agent_only"] = bool(opts.get("agent_only"))
    run_opts["analyst_only"] = bool(opts.get("analyst_only"))

    ablation_axes = _parse_ablation_axes(opts.get("ablation"))
    if bool(opts.get("raw_ablation")):
        if ablation_axes:
            logger.info(
                "Ignoring deprecated raw_ablation because ablation=%r was provided.",
                opts.get("ablation"),
            )
        else:
            logger.info("raw_ablation is deprecated; using ablation=diff.")
            ablation_axes = ["diff"]

    if ablation_axes:
        if "diff" in ablation_axes and "raw" in opts:
            logger.info(
                "Ablation axis 'diff' enabled. Ignoring raw=%r and running both processed and raw diff modes.",
                opts.get("raw"),
            )
        if "first_pass" in ablation_axes and ("agent_only" in opts or "analyst_only" in opts):
            logger.info(
                "Ablation axis 'first_pass' enabled. Ignoring agent_only=%r/analyst_only=%r and running combined, agent_only, and analyst_only modes.",
                opts.get("agent_only"),
                opts.get("analyst_only"),
            )

        run_specs = _expand_ablation_run_specs(run_opts, ablation_axes)
        return _run_ablation_specs(pairs, outdir, ablation_axes, run_specs)

    return _run_series(pairs, outdir, run_opts)


def llm_filter_targeted_ablation(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Run the mixed diff/workflow ablation without duplicate control runs."""
    pairs = _resolve_llm_filter_pairs(args, opts)

    outdir: str = opts.get("outdir", "out_delt_deep_agent_targeted_ablation")
    run_opts = _prepare_llm_filter_run_opts(opts)

    ignored_keys = [key for key in ("raw", "agent_only", "analyst_only", "ablation", "raw_ablation") if key in opts]
    if ignored_keys:
        logger.info(
            "llm_filter_targeted_ablation ignores user-supplied options %s and runs a fixed 6-run matrix.",
            ",".join(sorted(ignored_keys)),
        )

    axes = ["diff", "first_pass"]
    desired_runs = [
        ("processed", "combined"),
        ("processed", "agent_only"),
        ("processed", "analyst_only"),
        ("raw", "combined"),
        ("raw", "agent_only"),
        ("raw", "analyst_only"),
    ]
    desired_run_set = set(desired_runs)
    run_specs: List[Dict[str, Any]] = []
    for spec in _expand_ablation_run_specs(run_opts, axes):
        settings = spec.get("settings") or {}
        key = (str(settings.get("diff") or ""), str(settings.get("first_pass") or ""))
        if key in desired_run_set:
            run_specs.append(spec)

    run_specs.sort(
        key=lambda spec: desired_runs.index(
            (
                str((spec.get("settings") or {}).get("diff") or ""),
                str((spec.get("settings") or {}).get("first_pass") or ""),
            )
        )
    )

    return _run_ablation_specs(pairs, outdir, axes, run_specs)


_EXPERIMENT_CONFIGS = [
    # name              diff_raw  filter_key                   agent_only  analyst_only
    ("processed_OR_combined",False, "Call_OR_Control_Modified", False, False),
    ("processed_OR_agent",   False, "Call_OR_Control_Modified", True,  False),
    ("processed_OR_analyst", False, "Call_OR_Control_Modified", False, True),
    ("raw_OR_agent",    True,     "Call_OR_Control_Modified",  True,        False),
    ("raw_OR_analyst",  True,     "Call_OR_Control_Modified",  False,       True),
    ("raw_NONE_agent",  True,     None,                        True,        False),
    ("raw_NONE_analyst",True,     None,                        False,       True),
]

# configs that inherit cached results from a narrower filter (source → dest pairs per workflow)
_FILTER_INHERITANCE = [
    # (source_config, dest_config) — copy source sample dirs into dest before running dest
    ("raw_OR_agent",    "raw_NONE_agent"),
    ("raw_OR_analyst",  "raw_NONE_analyst"),
]

# pure filter census: run drift + GT retention check only, no diff generation or LLM calls
_FILTER_CENSUS_CONFIGS = [
    # name          filter_key
    ("filter_AND",  "Control_Call_Modified"),
    ("filter_OR",   "Call_OR_Control_Modified"),
    ("filter_NONE", None),
]


def _sample_is_complete(sample_outdir: str) -> bool:
    return os.path.exists(os.path.join(sample_outdir, "stats.json"))


def _seed_from_prior_filter(
    prior_config_dir: str,
    dest_config_dir: str,
    category: str,
) -> None:
    """Copy completed sample dirs from a narrower-filter config into a wider-filter config dir.

    This reuses drift_raw.json and any function-level analysis.json files with matching
    directory names, avoiding re-running BinDiff for already-processed pairs.
    stats.json is removed from each copied directory so sample-level resume does not skip
    the pair — the wider-filter run will still execute but benefits from cached artifacts.
    """
    src_cat_dir = os.path.join(prior_config_dir, category)
    dst_cat_dir = os.path.join(dest_config_dir, category)

    if not os.path.isdir(src_cat_dir):
        return

    os.makedirs(dst_cat_dir, exist_ok=True)

    for entry in os.listdir(src_cat_dir):
        src_pair_dir = os.path.join(src_cat_dir, entry)
        dst_pair_dir = os.path.join(dst_cat_dir, entry)
        if not os.path.isdir(src_pair_dir):
            continue
        if os.path.exists(dst_pair_dir):
            logger.info("seed: destination already exists, skipping copy for %s", entry)
            continue
        shutil.copytree(src_pair_dir, dst_pair_dir)
        stats_path = os.path.join(dst_pair_dir, "stats.json")
        if os.path.exists(stats_path):
            os.remove(stats_path)
        logger.info("seed: copied %s -> %s (stats.json removed)", src_pair_dir, dst_pair_dir)


def _run_category(
    pairs: List[Tuple[str, str]],
    category_outdir: str,
    run_opts: Dict[str, Any],
) -> List[Dict[str, Any]]:
    """Run one (config, category) series with sample-level resume."""
    os.makedirs(category_outdir, exist_ok=True)

    results: List[Dict[str, Any]] = []
    total = len(pairs)
    skipped = 0

    for idx, (target, baseline) in enumerate(pairs, 1):
        try:
            target_name = oxide.api.get_colname_from_oid(target)
        except Exception:
            target_name = str(target)
        try:
            baseline_name = oxide.api.get_colname_from_oid(baseline)
        except Exception:
            baseline_name = str(baseline)

        pair_dir = os.path.join(category_outdir, _comparison_dir_name(target_name, baseline_name))

        if _sample_is_complete(pair_dir):
            logger.info("[%d/%d] skipping %s (already complete)", idx, total, pair_dir)
            try:
                stats = read_json(os.path.join(pair_dir, "stats.json"))
                stats = _refresh_cached_stats_ground_truth(pair_dir, stats, run_opts, target_name)
            except Exception:
                logger.exception("Failed to load or refresh cached stats for %s", pair_dir)
                stats = {}
            results.append(stats)
            skipped += 1
            continue

        logger.info("[%d/%d] %s -> %s", idx, total, target_name, baseline_name)
        result = run_one_comparison(target, baseline, pair_dir, run_opts)
        stats = dict(result.get("stats") or {})
        results.append(stats)

    logger.info(
        "Category done: %d total, %d skipped (cached), %d run",
        total,
        skipped,
        total - skipped,
    )
    return results


def _refresh_cached_stats_ground_truth(
    pair_dir: str,
    stats: Dict[str, Any],
    run_opts: Dict[str, Any],
    target_name: str,
) -> Dict[str, Any]:
    """Refresh cached stats against the ground truth supplied for this run."""
    gt = run_opts.get("_ground_truth") or {}
    gt_norm = get_ground_truth_for_target(gt, target_name)
    if not gt_norm:
        return stats

    per_function_path = os.path.join(pair_dir, "per_function_results.json")
    if not os.path.exists(per_function_path):
        logger.warning("Cannot refresh ground truth for %s: missing per_function_results.json", pair_dir)
        return stats

    per_function_results = read_json(per_function_path)
    if not isinstance(per_function_results, list):
        logger.warning("Cannot refresh ground truth for %s: per_function_results.json is not a list", pair_dir)
        return stats

    gt_targets = gt_norm.get("targets", [])
    gt_matched: Set[int] = {
        id(row)
        for row in per_function_results
        if isinstance(row, dict) and gt_row_matches_any(row, gt_norm)
    }
    flagged_final_ids: Set[int] = {
        id(row)
        for row in per_function_results
        if isinstance(row, dict) and row.get("flagged_final")
    }

    tp_final = len(flagged_final_ids & gt_matched)
    fp_final = len(flagged_final_ids - gt_matched)
    total_modified_all = int(stats.get("total_modified_functions") or 0)

    refreshed = dict(stats)
    refreshed.update(
        {
            "gt_compromised_count": len(gt_targets),
            "gt_targets": gt_targets,
            "gt_in_filtered": bool(gt_matched),
            "hit_final": bool(flagged_final_ids & gt_matched),
            "tp_final": tp_final,
            "fp_final": fp_final,
            "fp_rate_final": (float(fp_final) / float(total_modified_all)) if total_modified_all else None,
        }
    )
    write_json(os.path.join(pair_dir, "stats.json"), refreshed)
    logger.info("Refreshed cached ground-truth stats for %s", pair_dir)
    return refreshed


def _summarize_category(results: List[Dict[str, Any]], category: str) -> Dict[str, Any]:
    total = len(results)
    total_flagged = sum(int(r.get("final_not_safe_filtered") or 0) for r in results)
    total_filtered = sum(int(r.get("filtered_functions") or 0) for r in results)
    total_tokens = sum(int(r.get("llm_total_tokens") or 0) for r in results)

    summary: Dict[str, Any] = {
        "total_pairs": total,
        "total_flagged": total_flagged,
        "total_filtered": total_filtered,
        "total_llm_tokens": total_tokens,
    }

    if category == "backdoored":
        hits = sum(1 for r in results if r.get("hit_final") is True)
        summary["hits"] = hits
        summary["recall"] = (hits / total) if total else None
    else:
        fp_rate = (total_flagged / total_filtered) if total_filtered else None
        summary["fp_rate"] = fp_rate

    return summary


def _run_filter_census_comparison(
    target: str,
    baseline: str,
    outdir: str,
    filter_key: Optional[str],
    gt: Dict[str, Any],
    target_name: str,
) -> Dict[str, Any]:
    os.makedirs(outdir, exist_ok=True)
    filter_val = _normalize_filter_value(filter_key)

    drift_res = run_drift(target, baseline, filter_val)
    drift_json = coerce_json_like(getattr(drift_res, "content", drift_res)) or {}
    write_json(os.path.join(outdir, "drift_raw.json"), drift_json)

    file_pairs = drift_json.get("file_pairs", []) or []
    total_modified_all = 0
    total_modified_filtered = 0

    gt_norm = get_ground_truth_for_target(gt, target_name)
    gt_in_filtered: Optional[bool] = None

    for fp in file_pairs:
        target_oid = fp.get("target_oid")
        filtered_mods = fp.get("modified_functions", []) or []
        excluded_mods = fp.get("excluded_functions", []) or []
        total_modified_all += len(filtered_mods) + len(excluded_mods)
        total_modified_filtered += len(filtered_mods)

        if gt_norm and gt_in_filtered is not True:
            for func in filtered_mods:
                row = {"target_addr": func.get("target_func_addr"), "target_oid": target_oid}
                if gt_row_matches_any(row, gt_norm):
                    gt_in_filtered = True
                    break

    if gt_norm and gt_in_filtered is None:
        gt_in_filtered = False

    stats = {
        "total_modified_all": total_modified_all,
        "filtered_functions": total_modified_filtered,
        "gt_in_filtered": gt_in_filtered,
    }
    write_json(os.path.join(outdir, "stats.json"), stats)
    return stats


def _run_filter_census_category(
    pairs: List[Tuple[str, str]],
    category_outdir: str,
    filter_key: Optional[str],
    gt: Dict[str, Any],
) -> List[Dict[str, Any]]:
    os.makedirs(category_outdir, exist_ok=True)
    results: List[Dict[str, Any]] = []
    total = len(pairs)
    skipped = 0

    for idx, (target, baseline) in enumerate(pairs, 1):
        try:
            target_name = oxide.api.get_colname_from_oid(target)
        except Exception:
            target_name = str(target)
        try:
            baseline_name = oxide.api.get_colname_from_oid(baseline)
        except Exception:
            baseline_name = str(baseline)

        pair_dir = os.path.join(category_outdir, _comparison_dir_name(target_name, baseline_name))

        if _sample_is_complete(pair_dir):
            logger.info("[%d/%d] skipping %s (already complete)", idx, total, pair_dir)
            try:
                stats = read_json(os.path.join(pair_dir, "stats.json"))
                stats = _refresh_cached_filter_census_ground_truth(pair_dir, stats, gt, target_name)
            except Exception:
                logger.exception("Failed to load or refresh cached filter census stats for %s", pair_dir)
                stats = {}
            results.append(stats)
            skipped += 1
            continue

        logger.info("[%d/%d] %s -> %s", idx, total, target_name, baseline_name)
        stats = _run_filter_census_comparison(target, baseline, pair_dir, filter_key, gt, target_name)
        results.append(stats)

    logger.info(
        "Filter census done: %d total, %d skipped (cached), %d run",
        total, skipped, total - skipped,
    )
    return results


def _refresh_cached_filter_census_ground_truth(
    pair_dir: str,
    stats: Dict[str, Any],
    gt: Dict[str, Any],
    target_name: str,
) -> Dict[str, Any]:
    gt_norm = get_ground_truth_for_target(gt, target_name)
    if not gt_norm:
        return stats

    drift_path = os.path.join(pair_dir, "drift_raw.json")
    if not os.path.exists(drift_path):
        logger.warning("Cannot refresh filter census ground truth for %s: missing drift_raw.json", pair_dir)
        return stats

    drift_json = read_json(drift_path)
    file_pairs = drift_json.get("file_pairs", []) or [] if isinstance(drift_json, dict) else []

    gt_in_filtered = False
    for fp in file_pairs:
        target_oid = fp.get("target_oid") if isinstance(fp, dict) else None
        filtered_mods = fp.get("modified_functions", []) or [] if isinstance(fp, dict) else []
        for func in filtered_mods:
            if not isinstance(func, dict):
                continue
            row = {"target_addr": func.get("target_func_addr"), "target_oid": target_oid}
            if gt_row_matches_any(row, gt_norm):
                gt_in_filtered = True
                break
        if gt_in_filtered:
            break

    refreshed = dict(stats)
    refreshed["gt_in_filtered"] = gt_in_filtered
    write_json(os.path.join(pair_dir, "stats.json"), refreshed)
    logger.info("Refreshed cached filter census ground-truth stats for %s", pair_dir)
    return refreshed


def _summarize_filter_census(results: List[Dict[str, Any]], category: str) -> Dict[str, Any]:
    total = len(results)
    total_modified_all = sum(int(r.get("total_modified_all") or 0) for r in results)
    total_filtered = sum(int(r.get("filtered_functions") or 0) for r in results)

    summary: Dict[str, Any] = {
        "total_pairs": total,
        "total_modified_all": total_modified_all,
        "total_filtered": total_filtered,
    }

    if category == "backdoored":
        gt_in_filter = sum(1 for r in results if r.get("gt_in_filtered") is True)
        summary["gt_in_filter"] = gt_in_filter

    return summary


def run_experiments(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Run all evaluation configurations needed for the paper.

    Required opts:
      backdoored   -- path to entries file of (target, baseline) backdoored pairs
      ground_truth -- path to r-diff-gt.json (used only for backdoored category)

    Optional opts:
      safe         -- path to entries file of safe pairs
      openwrt      -- path to entries file of OpenWrt pairs
      outdir       -- root output directory (default: out_experiments)
      model        -- LLM model tag
      no_triage    -- if true, produce diff evidence but skip LLM calls (dry run)
    """
    backdoored_path: Optional[str] = opts.get("backdoored")
    safe_path: Optional[str] = opts.get("safe")
    openwrt_path: Optional[str] = opts.get("openwrt")
    gt_path: Optional[str] = opts.get("ground_truth")
    outdir: str = opts.get("outdir", "out_experiments")

    if not backdoored_path and not safe_path and not openwrt_path:
        raise ValueError("At least one of --backdoored, --safe, or --openwrt must be provided.")

    # Read entries files up front so errors surface before any LLM work begins.
    backdoored_pairs: List[Tuple[str, str]] = (
        drift.read_series_file(backdoored_path) if backdoored_path else []
    )
    safe_pairs: List[Tuple[str, str]] = (
        drift.read_series_file(safe_path) if safe_path else []
    )
    openwrt_pairs: List[Tuple[str, str]] = (
        drift.read_series_file(openwrt_path) if openwrt_path else []
    )

    os.makedirs(outdir, exist_ok=True)
    experiment_summary: Dict[str, Any] = {}

    # Phase 0: pure filter census — run drift + GT retention check for AND, OR, and NONE
    # with no diff generation or LLM calls.
    gt_for_census = load_ground_truth_file(gt_path) if gt_path else {}
    for census_name, census_filter_key in _FILTER_CENSUS_CONFIGS:
        census_dir = os.path.join(outdir, census_name)
        os.makedirs(census_dir, exist_ok=True)
        census_summary: Dict[str, Any] = {}

        for category, pairs in [("backdoored", backdoored_pairs), ("safe", safe_pairs)]:
            if not pairs:
                continue
            gt = gt_for_census if category == "backdoored" else {}
            results = _run_filter_census_category(
                pairs, os.path.join(census_dir, category), census_filter_key, gt
            )
            cat_summary = _summarize_filter_census(results, category)
            census_summary[category] = cat_summary
            write_json(os.path.join(census_dir, category, "series_metrics.json"), cat_summary)

        write_json(os.path.join(census_dir, "config_summary.json"), census_summary)
        experiment_summary[census_name] = census_summary
        logger.info("Filter census '%s' complete.", census_name)

    # Build a map from config name to (prior_config_name) for filter inheritance.
    inheritance_map: Dict[str, str] = {dest: src for src, dest in _FILTER_INHERITANCE}

    completed_configs: Set[str] = set()

    for config_name, diff_raw, filter_key, agent_only, analyst_only in _EXPERIMENT_CONFIGS:
        config_dir = os.path.join(outdir, config_name)
        os.makedirs(config_dir, exist_ok=True)

        # Seed this config's category dirs from the narrower-filter config, if applicable.
        prior_config = inheritance_map.get(config_name)
        if prior_config and prior_config in completed_configs:
            categories_to_seed = []
            if backdoored_pairs:
                categories_to_seed.append("backdoored")
            if safe_pairs:
                categories_to_seed.append("safe")
            # openwrt only runs processed_OR_combined; raw configs never have openwrt
            for cat in categories_to_seed:
                _seed_from_prior_filter(
                    os.path.join(outdir, prior_config),
                    config_dir,
                    cat,
                )

        # Build base run_opts for this config.
        base_opts: Dict[str, Any] = dict(opts)
        base_opts["_diff_raw"] = diff_raw
        base_opts["filter"] = filter_key
        base_opts["agent_only"] = agent_only
        base_opts["analyst_only"] = analyst_only

        config_summary: Dict[str, Any] = {}

        # Categories for this config.
        categories: List[Tuple[str, List[Tuple[str, str]], Optional[str]]] = []
        if backdoored_pairs:
            categories.append(("backdoored", backdoored_pairs, gt_path))
        if safe_pairs:
            categories.append(("safe", safe_pairs, None))
        if openwrt_pairs and config_name == "processed_OR_combined":
            categories.append(("openwrt", openwrt_pairs, None))

        for category, pairs, cat_gt_path in categories:
            cat_opts = dict(base_opts)
            cat_opts["ground_truth"] = cat_gt_path
            run_opts = _prepare_llm_filter_run_opts(cat_opts)

            category_outdir = os.path.join(config_dir, category)

            logger.info(
                "Config '%s' category '%s': %d pairs, diff_raw=%s filter=%s agent_only=%s analyst_only=%s",
                config_name,
                category,
                len(pairs),
                diff_raw,
                filter_key,
                agent_only,
                analyst_only,
            )

            results = _run_category(pairs, category_outdir, run_opts)
            cat_summary = _summarize_category(results, category)
            config_summary[category] = cat_summary

            # Write per-category series files (mirrors _run_series output).
            comparison_rows = [
                {"index": i + 1, "target": t, "baseline": b, **r}
                for i, ((t, b), r) in enumerate(zip(pairs, results))
            ]
            write_json(
                os.path.join(category_outdir, "comparisons_summary.json"),
                {"config": config_name, "category": category, "comparisons": comparison_rows},
            )
            write_json(os.path.join(category_outdir, "series_metrics.json"), cat_summary)
            write_text(
                os.path.join(category_outdir, "series_summary.txt"),
                "\n".join(
                    [f"{k}: {v}" for k, v in cat_summary.items()]
                    + [f"config: {config_name}", f"category: {category}"]
                ),
            )

        write_json(os.path.join(config_dir, "config_summary.json"), config_summary)
        experiment_summary[config_name] = config_summary
        completed_configs.add(config_name)

        logger.info("Config '%s' complete.", config_name)

    write_json(os.path.join(outdir, "experiment_summary.json"), experiment_summary)
    logger.info("Experiment complete. Summary written to %s/experiment_summary.json", outdir)
    return experiment_summary


exports = [llm_filter, llm_filter_targeted_ablation, run_experiments]
