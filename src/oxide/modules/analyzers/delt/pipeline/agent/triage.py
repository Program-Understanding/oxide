import logging
import os
from typing import Any, Dict, Optional

from oxide.modules.analyzers.delt.config import NAME
from oxide.modules.analyzers.delt.pipeline.agent.nodes.agent import run_agent
from oxide.modules.analyzers.delt.pipeline.utils.text_utils import _coerce_str, preview_text

logger = logging.getLogger(NAME)


def _derive_why(agent_result: Dict[str, Any]) -> str:
    """ The agent's final-answer schema is a single-field submit_decision(label) tool
        call, so agent_result doesn't carry structured reasoning -- but it still writes
        free-text reasoning to /work/final.md.
    """
    final_md = _coerce_str(agent_result.get("final_md"))
    if final_md:
        return preview_text(final_md, limit=400)
    return "Agent completed triage; see final.md for reasoning."


def run_triage(
    runtime: Any,
    unified_diff: str,
    notes: Dict[str, Any],
    *,
    callee_texts: Optional[Dict[str, str]] = None,
    trace_path: Optional[str] = None,
) -> Dict[str, Any]:
    """Run the triage agent over one modified-function diff and return its result dict."""
    from oxide.modules.analyzers.delt.pipeline.utils.text_utils import ascii_sanitize

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
        result = run_agent(
            runtime,
            diff_text=diff_text,
            notes=notes,
            trace_path=trace_path,
            callee_texts=callee_texts or {},
        )
    finally:
        if log_handler is not None:
            logger.removeHandler(log_handler)
            log_handler.close()

    return {
        "label": result.get("label", "failed"),
        "why": _derive_why(result),
        "final_md": _coerce_str(result.get("final_md")),
        "failure_reason": result.get("failure_reason"),
        "failure_detail": _coerce_str(result.get("failure_detail")),
        "llm_elapsed_s": float(result.get("llm_elapsed_s") or 0.0),
        "llm_input_tokens": int(result.get("llm_input_tokens") or 0),
        "llm_output_tokens": int(result.get("llm_output_tokens") or 0),
        "llm_total_tokens": int(result.get("llm_total_tokens") or 0),
    }
