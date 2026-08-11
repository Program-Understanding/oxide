"""Verification driver: run one whole-binary investigation per escalated triage candidate."""

import os
from typing import Any, Dict, Optional

from oxide.modules.analyzers.delt_verification.pipeline.agents.nodes.verification_agent import (
    run_verification_agent,
)
from oxide.modules.analyzers.delt_verification.pipeline.utils.text_utils import (
    _coerce_label,
    _coerce_str,
    write_json,
    write_text,
)


def _read_file(path: str) -> str:
    if not path or not os.path.isfile(path):
        return ""
    try:
        with open(path, "r", encoding="utf-8") as handle:
            return handle.read()
    except OSError:
        return ""


def _render_claim(local_report: Dict[str, Any]) -> str:
    """Render triage findings as the claim verification investigates.

    The triage label, and any mention of triage itself, are deliberately left out.
    Triage writes final.md only when it decides not_safe, so the label carries
    nothing verification does not already have from being handed the candidate, and
    naming the source invites verification to ratify rather than re-investigate.
    """
    final_md = _coerce_str(local_report.get("final_md"))
    if not final_md.strip():
        return ""
    return "\n".join(
        [
            f"Baseline addr: {_coerce_str(local_report.get('baseline_addr')) or '<unknown>'}",
            f"Target addr: {_coerce_str(local_report.get('target_addr')) or '<unknown>'}",
            "",
            final_md,
        ]
    )


def run_verification(
    *,
    runtime: Any,
    fp_idx: int,
    baseline_oid: Any,
    target_oid: Any,
    local_report: Dict[str, Any],
    binary_context: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    """Investigate one escalated candidate and write its verification artifacts."""
    func_dir = _coerce_str(local_report.get("func_dir"))
    if not func_dir:
        raise ValueError("run_verification requires local_report['func_dir']")
    stage_dir = os.path.join(func_dir, "verification")
    os.makedirs(stage_dir, exist_ok=True)

    func_idx = int(local_report.get("function_index") or 0)
    claim = _render_claim(local_report)
    diff_text = _coerce_str(local_report.get("diff_text")) or _read_file(
        _coerce_str(local_report.get("diff_path"))
    )
    candidate = {
        "target_oid": _coerce_str(target_oid),
        "baseline_oid": _coerce_str(baseline_oid),
        "target_addr": local_report.get("target_addr"),
        "baseline_addr": local_report.get("baseline_addr"),
    }

    agent_result = run_verification_agent(
        runtime,
        claim,
        candidate=candidate,
        binary_context_md=_coerce_str((binary_context or {}).get("binary_context_md")),
        diff_text=diff_text,
        trace_path=os.path.join(stage_dir, "agent_trace.log"),
    )
    final_md = _coerce_str(agent_result.get("final_md"))

    result = {
        "filepair_index": fp_idx,
        "function_index": func_idx,
        "target_oid": _coerce_str(target_oid),
        "baseline_oid": _coerce_str(baseline_oid),
        "baseline_addr": local_report.get("baseline_addr"),
        "target_addr": local_report.get("target_addr"),
        "triage_label": _coerce_str(local_report.get("label")),
        "label": _coerce_label(agent_result.get("label")),
        "summary": _coerce_str(agent_result.get("summary")),
        "failure_reason": agent_result.get("failure_reason"),
        "failure_detail": _coerce_str(agent_result.get("failure_detail")),
        "had_triage_report": bool(claim.strip()),
        # The phase result dict is truthy even when the phase failed, so test the report
        # itself: a failed binary-context run hands the agent an empty string.
        "used_binary_context": bool(_coerce_str((binary_context or {}).get("binary_context_md")).strip()),
        "llm_elapsed_s": float(agent_result.get("llm_elapsed_s") or 0.0),
        "llm_input_tokens": int(agent_result.get("llm_input_tokens") or 0),
        "llm_output_tokens": int(agent_result.get("llm_output_tokens") or 0),
        "llm_total_tokens": int(agent_result.get("llm_total_tokens") or 0),
        "outdir": stage_dir,
        "final_md": final_md,
    }

    if final_md:
        final_md_path = os.path.join(stage_dir, "final.md")
        write_text(final_md_path, final_md)
        result["final_md_path"] = final_md_path
    write_json(os.path.join(stage_dir, "result.json"), result)
    write_json(
        os.path.join(stage_dir, "inputs.json"),
        {
            "triage_function_report": {
                "function_index": func_idx,
                "target_oid": _coerce_str(target_oid),
                "baseline_oid": _coerce_str(baseline_oid),
                "baseline_addr": local_report.get("baseline_addr"),
                "target_addr": local_report.get("target_addr"),
                "label": local_report.get("label"),
                "final_md_path": local_report.get("final_md_path"),
                "diff_path": local_report.get("diff_path"),
                "binary_context_path": (
                    os.path.join((binary_context or {}).get("outdir") or "", "binary_context.md")
                    if binary_context else ""
                ),
            },
        },
    )
    return result
