"""Binary-context generation for one file pair."""

import os
from typing import Any, Dict

from oxide.modules.analyzers.delt_verification.pipeline.agents.nodes.binary_context_agent import (
    run_binary_context_agent,
)
from oxide.modules.analyzers.delt_verification.pipeline.utils.text_utils import (
    _coerce_str,
    write_json,
    write_text,
)


def run_binary_context_analysis(
    *,
    runtime: Any,
    fp_idx: int,
    baseline_oid: Any,
    target_oid: Any,
    outdir: str,
) -> Dict[str, Any]:
    filepair_dir = os.path.join(outdir, f"filepair_{fp_idx:02d}")
    stage_dir = os.path.join(filepair_dir, "binary_context")
    os.makedirs(stage_dir, exist_ok=True)
    trace_path = os.path.join(stage_dir, "agent_trace.log")

    agent_result = run_binary_context_agent(
        runtime,
        binary_oid=_coerce_str(baseline_oid),
        trace_path=trace_path,
    )
    context_md = _coerce_str(agent_result.get("binary_context_md"))
    result = {
        "filepair_index": fp_idx,
        "baseline_oid": _coerce_str(baseline_oid),
        "target_oid": _coerce_str(target_oid),
        "status": _coerce_str(agent_result.get("status")) or "failed",
        "failure_reason": agent_result.get("failure_reason"),
        "failure_detail": _coerce_str(agent_result.get("failure_detail")),
        "llm_elapsed_s": float(agent_result.get("llm_elapsed_s") or 0.0),
        "llm_input_tokens": int(agent_result.get("llm_input_tokens") or 0),
        "llm_output_tokens": int(agent_result.get("llm_output_tokens") or 0),
        "llm_total_tokens": int(agent_result.get("llm_total_tokens") or 0),
        "outdir": stage_dir,
        "binary_context_md": context_md,
    }
    if context_md:
        write_text(os.path.join(stage_dir, "binary_context.md"), context_md)
    write_json(os.path.join(stage_dir, "result.json"), result)
    return result
