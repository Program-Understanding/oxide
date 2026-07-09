"""Stage 1: fast, JSON-structured analyst triage on a single modified-function diff."""

import logging
import queue as _queue
import threading as _threading
import time
from typing import Any, Dict, Tuple

from langchain_core.messages import HumanMessage, SystemMessage

from oxide.modules.analyzers.backdoor_triage.config import NAME
from oxide.modules.analyzers.backdoor_triage.pipeline.types import TriageState
from oxide.modules.analyzers.backdoor_triage.pipeline.utils.text_utils import (
    _coerce_label,
    _coerce_str,
    ascii_sanitize,
    parse_llm_json,
    preview_text,
    progress_label as _progress_label_fmt,
)
from oxide.modules.analyzers.backdoor_triage.pipeline.agent.telemetry.token_usage import extract_usage_counts_from_message

logger = logging.getLogger(NAME)


def stage1_output_complete(d: Dict[str, Any]) -> bool:
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


def invoke_stage1_text(stage1_llm: Any, sys_text: str, human_text: str) -> Tuple[str, float, Dict[str, int], bool]:
    """Stream stage1_llm with a per-token timeout. Returns (text, elapsed_s, usage_counts, timed_out)."""
    msgs = [SystemMessage(content=sys_text), HumanMessage(content=human_text)]
    t0 = time.perf_counter()
    q: "_queue.Queue[Tuple[str, Any]]" = _queue.Queue()
    stop = _threading.Event()
    token_timeout_s = float(getattr(stage1_llm, "_oxide_stage1_token_timeout_s", 30.0))
    total_timeout_s = float(getattr(stage1_llm, "_oxide_stage1_total_timeout_s", 300.0))

    def _worker() -> None:
        try:
            gen = stage1_llm.stream(msgs)
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

    chunks = []
    aggregated_chunk = None
    timed_out = False
    while True:
        elapsed = time.perf_counter() - t0
        wait = min(token_timeout_s, total_timeout_s - elapsed)
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
            logger.warning("Stage 1 LLM stream error: %s", val)
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
        logger.warning(
            "Stage 1 LLM timed out (no token for %.0fs or total %.0fs exceeded).",
            token_timeout_s, total_timeout_s,
        )

    text = ascii_sanitize("".join(chunks)).strip()
    usage_counts = extract_usage_counts_from_message(aggregated_chunk)
    return text, time.perf_counter() - t0, usage_counts, timed_out


def call_stage1_llm_json(
    runtime: Any, diff_text: str, notes: Dict[str, Any]
) -> Tuple[str, Dict[str, Any], Dict[str, Any]]:
    """Run the Stage 1 LLM. Returns (raw, result_dict, meta).
       Invalid JSON fails closed to not_safe. Timeouts are recorded as failed.
    """
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
    raw1, dt1, usage1, timed_out1 = invoke_stage1_text(
        runtime.stage1_llm, runtime.stage1_sys, f"FUNCTION UNIFIED DIFF:\n{diff_text}"
    )
    meta["input_tokens"] += int(usage1.get("input_tokens") or 0)
    meta["output_tokens"] += int(usage1.get("output_tokens") or 0)
    meta["total_tokens"] += int(usage1.get("total_tokens") or 0)
    if timed_out1:
        meta["duration_s"] = dt1
        meta["failure_reason"] = "timeout"
        meta["failure_detail"] = "Stage 1 timed out before reaching a validated decision."
        notes["observations"].append("Stage 1 timed out before reaching a validated decision.")
        return raw1, {
            "label": "failed",
            "trigger": "",
            "why": "Stage 1 timed out before reaching a validated decision.",
        }, meta
    d1 = parse_llm_json(raw1)
    if isinstance(d1, dict) and stage1_output_complete(d1):
        meta["parsed_ok"] = True
        meta["duration_s"] = dt1
        return raw1, {"label": _coerce_label(d1.get("label")),
                      "trigger": _coerce_str(d1.get("trigger")),
                      "why": _coerce_str(d1.get("why"))}, meta

    meta["attempts"] += 1
    meta["repaired"] = True
    notes["observations"].append("Stage 1 output invalid/incomplete; retrying once (repair).")
    repair_sys = (
        runtime.stage1_sys
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
    raw2, dt2, usage2, timed_out2 = invoke_stage1_text(runtime.stage1_llm, repair_sys, repair_human)
    meta["input_tokens"] += int(usage2.get("input_tokens") or 0)
    meta["output_tokens"] += int(usage2.get("output_tokens") or 0)
    meta["total_tokens"] += int(usage2.get("total_tokens") or 0)
    if timed_out2:
        meta["duration_s"] = dt1 + dt2
        meta["failure_reason"] = "timeout"
        meta["failure_detail"] = "Stage 1 timed out before reaching a validated decision."
        notes["observations"].append("Stage 1 timed out during repair.")
        return (raw2 or raw1), {
            "label": "failed",
            "trigger": "",
            "why": "Stage 1 timed out before reaching a validated decision.",
        }, meta
    d2 = parse_llm_json(raw2)
    if isinstance(d2, dict) and stage1_output_complete(d2):
        meta["parsed_ok"] = True
        meta["duration_s"] = dt1 + dt2
        return raw2, {"label": _coerce_label(d2.get("label")),
                      "trigger": _coerce_str(d2.get("trigger")),
                      "why": _coerce_str(d2.get("why"))}, meta

    meta["parsed_ok"] = False
    meta["duration_s"] = dt1 + dt2
    notes["observations"].append("Stage 1 JSON parse/validation failed twice; fail-closed to not_safe.")
    return (raw2 or raw1), {
        "label": "not_safe", "trigger": "",
        "why": "Stage 1 JSON parse/validation failed; fail-closed to not_safe.",
    }, meta


def build_stage1_node(runtime: Any):
    def _stage1_node(state: TriageState) -> Dict[str, Any]:
        if state.get("stage2_only"):
            # Pass-through: always escalate without running Stage 1
            return {"stage1_json": {"label": "not_safe", "trigger": "", "why": ""}}
        raw, result, meta = call_stage1_llm_json(runtime, state["diff"], state["notes"])
        logger.info(
            "%s stage1: label=%s trigger=%s",
            _progress_label_fmt(
                fp_idx=state["fp_idx"], fp_total=state.get("fp_total", 0),
                func_idx=state["func_idx"], func_total=state.get("func_total", 0),
            ),
            result.get("label"),
            preview_text(result.get("trigger", ""), limit=60),
        )
        return {"stage1_raw": raw, "stage1_json": result, "stage1_meta": meta}

    return _stage1_node
