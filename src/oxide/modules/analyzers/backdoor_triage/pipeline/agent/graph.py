import logging
import os
import time
from typing import Any, Dict, Optional, Tuple

from langgraph.graph import END, START, StateGraph

from oxide.modules.analyzers.backdoor_triage.config import NAME
from oxide.modules.analyzers.backdoor_triage.pipeline.agent.nodes.stage1 import build_stage1_node
from oxide.modules.analyzers.backdoor_triage.pipeline.agent.nodes.stage2 import build_stage2_node
from oxide.modules.analyzers.backdoor_triage.pipeline.agent.nodes.stage3 import build_stage3_node
from oxide.modules.analyzers.backdoor_triage.pipeline.types import TriageState
from oxide.modules.analyzers.backdoor_triage.pipeline.utils.text_utils import _coerce_str, preview_text, progress_label as _progress_label_fmt

logger = logging.getLogger(NAME)


def _route_after_stage1(state: TriageState) -> str:
    if state.get("stage1_only"):
        return END
    stage1_failure_reason = _coerce_str((state.get("stage1_meta") or {}).get("failure_reason"))
    if stage1_failure_reason == "timeout":
        logger.info(
            "%s stage1 timed out, escalating to stage2",
            _progress_label_fmt(
                fp_idx=state["fp_idx"], fp_total=state.get("fp_total", 0),
                func_idx=state["func_idx"], func_total=state.get("func_total", 0),
            ),
        )
        return "stage2"
    label = (state.get("stage1_json") or {}).get("label", "safe")
    if label == "not_safe":
        return "stage2"
    return END


def _route_after_stage2(state: TriageState) -> str:
    """ Escalate to Stage 3 only when the combined Stage 1+2 verdict is not_safe.
        final_json is always set by stage2's own node output whenever stage2 runs
        (the only path that reaches this conditional edge at all), so it's safe
        to read directly here -- no fallback/synthesis needed at this point.
    """
    label = (state.get("final_json") or {}).get("label", "safe")
    if label == "not_safe":
        return "stage3"
    return END


def build_triage_graph(runtime: Any) -> Any:
    from langgraph.checkpoint.memory import MemorySaver

    g: StateGraph = StateGraph(TriageState)
    g.add_node("stage1", build_stage1_node(runtime))
    g.add_node("stage2", build_stage2_node(runtime))
    g.add_node("stage3", build_stage3_node(runtime))
    g.add_edge(START, "stage1")
    g.add_conditional_edges("stage1", _route_after_stage1, {"stage2": "stage2", END: END})
    g.add_conditional_edges("stage2", _route_after_stage2, {"stage3": "stage3", END: END})
    g.add_edge("stage3", END)
    return g.compile(checkpointer=MemorySaver())


def _derive_why_and_trigger(stage1_json: Dict[str, Any], stage2_result: Dict[str, Any]) -> Tuple[str, str]:
    """ Stage 2's final-answer schema is a single-field submit_stage2_decision(label)
        tool call, so stage2_result doesn't carry a structured trigger/why -- but it
        still writes free-text reasoning to /work/final.md and /work/analysis.md.
    """
    if not stage2_result:
        # Stage 1 decided without escalating; its own why/trigger is already computed.
        return _coerce_str(stage1_json.get("why")), _coerce_str(stage1_json.get("trigger"))

    final_md = _coerce_str(stage2_result.get("final_md"))
    analysis_md = _coerce_str(stage2_result.get("analysis_md"))
    if final_md:
        why = preview_text(final_md, limit=400)
    elif analysis_md:
        why = preview_text(analysis_md, limit=400)
    else:
        why = "Stage 2 completed triage; see analysis.md/final.md for reasoning."
    return why, ""


def run_triage(
    runtime: Any,
    unified_diff: str,
    notes: Dict[str, Any],
    *,
    target_oid: str = "",
    baseline_oid: str = "",
    target_addr: str = "",
    baseline_addr: str = "",
    stage1_only: bool = False,
    stage2_only: bool = False,
    callee_texts: Optional[Dict[str, str]] = None,
    trace_path: Optional[str] = None,
    fp_idx: int = 0,
    fp_total: int = 0,
    func_idx: int = 0,
    func_total: int = 0,
) -> Dict[str, Any]:
    """Run the triage pipeline via runtime.graph and return a combined result dict."""
    from oxide.modules.analyzers.backdoor_triage.pipeline.utils.text_utils import ascii_sanitize

    diff_text = ascii_sanitize(unified_diff)

    log_handler = None
    if trace_path:
        log_path = os.path.join(os.path.dirname(os.path.abspath(trace_path)), "triage.log")
        try:
            import logging as _logging

            os.makedirs(os.path.dirname(log_path), exist_ok=True)
            formatter = _logging.Formatter("[%(asctime)s] %(levelname)s %(name)s: %(message)s", "%H:%M:%S")
            log_handler = _logging.FileHandler(log_path, mode="w", encoding="utf-8")
            log_handler.setFormatter(formatter)
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
            "stage1_only": stage1_only,
            "stage2_only": stage2_only or bool(callee_texts),
            "callee_texts": callee_texts or {},
            "target_oid": target_oid,
            "baseline_oid": baseline_oid,
            "target_addr": target_addr,
            "baseline_addr": baseline_addr,
            "stage1_raw": None,
            "stage1_json": None,
            "stage1_meta": None,
            "stage2_result": None,
            "stage3_result": None,
            "final_json": None,
        }
        triage_config = {"configurable": {"thread_id": f"triage_{time.time_ns()}"}}
        final_state = runtime.graph.invoke(initial_state, config=triage_config)
    finally:
        if log_handler is not None:
            logger.removeHandler(log_handler)
            log_handler.close()

    stage1_json = final_state.get("stage1_json") or {}
    stage1_meta = final_state.get("stage1_meta") or {}
    stage2_result = final_state.get("stage2_result") or {}
    stage3_result = final_state.get("stage3_result") or {}
    final_json = final_state.get("final_json")

    stage1_input_tokens = int(stage1_meta.get("input_tokens") or 0)
    stage1_output_tokens = int(stage1_meta.get("output_tokens") or 0)
    stage1_tokens = int(stage1_meta.get("total_tokens") or 0)
    stage1_elapsed = float(stage1_meta.get("duration_s") or 0.0)
    stage2_input_tokens = int(stage2_result.get("llm_input_tokens") or 0)
    stage2_output_tokens = int(stage2_result.get("llm_output_tokens") or 0)
    stage2_tokens = int(stage2_result.get("llm_total_tokens") or 0)
    stage2_elapsed = float(stage2_result.get("llm_elapsed_s") or 0.0)

    # If Stage 1 cleared it (no Stage 2 ran), use Stage 1's result as final
    if final_json is None:
        final_json = {"label": stage1_json.get("label", "safe")}

    failure_reason = stage2_result.get("failure_reason") if stage2_result else None
    why, trigger = _derive_why_and_trigger(stage1_json, stage2_result)

    return {
        "label": final_json.get("label", "failed"),
        "why": why,
        "trigger": trigger,
        "stage1_label": stage1_json.get("label", ""),
        "stage1_why": _coerce_str(stage1_json.get("why")),
        "stage1_trigger": _coerce_str(stage1_json.get("trigger")),
        "stage1_elapsed_s": stage1_elapsed,
        "stage1_input_tokens": stage1_input_tokens,
        "stage1_output_tokens": stage1_output_tokens,
        "stage1_tokens": stage1_tokens,
        "stage2_ran": bool(stage2_result),
        "analysis_md": _coerce_str(stage2_result.get("analysis_md")),
        "final_md": _coerce_str(stage2_result.get("final_md")),
        "failure_reason": failure_reason,
        "failure_detail": _coerce_str(stage2_result.get("failure_detail")),
        "llm_elapsed_s": stage1_elapsed + stage2_elapsed,
        "llm_input_tokens": stage1_input_tokens + stage2_input_tokens,
        "llm_output_tokens": stage1_output_tokens + stage2_output_tokens,
        "llm_total_tokens": stage1_tokens + stage2_tokens,
        "stage3_ran": bool(stage3_result),
        "stage3_overall": stage3_result.get("overall") if stage3_result else None,
        "stage3_confirmed_functions": stage3_result.get("confirmed_functions") or [],
        "stage3_why": _coerce_str(stage3_result.get("why")),
        "stage3_analysis_md": _coerce_str(stage3_result.get("analysis_md")),
        "stage3_final_md": _coerce_str(stage3_result.get("final_md")),
        "stage3_failure_reason": stage3_result.get("failure_reason") if stage3_result else None,
        "stage3_failure_detail": _coerce_str(stage3_result.get("failure_detail")),
        "stage3_elapsed_s": float(stage3_result.get("elapsed_s") or 0.0),
        "stage3_input_tokens": int(stage3_result.get("llm_input_tokens") or 0),
        "stage3_output_tokens": int(stage3_result.get("llm_output_tokens") or 0),
        "stage3_total_tokens": int(stage3_result.get("llm_total_tokens") or 0),
    }
