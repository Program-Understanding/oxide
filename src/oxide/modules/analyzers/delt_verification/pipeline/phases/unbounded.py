"""Unbounded driver: run one whole-binary investigation per escalated bounded candidate."""

import os
from typing import Any, Dict

from oxide.modules.analyzers.delt_verification.pipeline.agents.nodes.unbounded_agent import (
    run_unbounded_agent,
)
from oxide.modules.analyzers.delt_verification.pipeline.utils.text_utils import (
    _coerce_label,
    _coerce_str,
    ascii_sanitize,
    write_json,
    write_text,
    read_text,
)


def _render_claim(local_report: Dict[str, Any]) -> str:
    """Render bounded findings as the claim unbounded investigates.

    The bounded label, and any mention of bounded itself, are deliberately left out.
    Bounded writes final.md only when it decides not_safe, so the label carries
    nothing unbounded does not already have from being handed the candidate, and
    naming the source invites unbounded to ratify rather than re-investigate.
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


def run_unbounded(
    *,
    runtime: Any,
    fp_idx: int,
    baseline_oid: Any,
    target_oid: Any,
    local_report: Dict[str, Any],
) -> Dict[str, Any]:
    """Investigate one escalated candidate and write its unbounded artifacts."""
    func_dir = _coerce_str(local_report.get("func_dir"))
    if not func_dir:
        raise ValueError("run_unbounded requires local_report['func_dir']")
    stage_dir = os.path.join(func_dir, "unbounded")
    os.makedirs(stage_dir, exist_ok=True)

    func_idx = int(local_report.get("function_index") or 0)
    claim = _render_claim(local_report)
    diff_text = ascii_sanitize(
        _coerce_str(local_report.get("diff_text"))
        or read_text(_coerce_str(local_report.get("diff_path")))
    )
    candidate = {
        "target_oid": _coerce_str(target_oid),
        "baseline_oid": _coerce_str(baseline_oid),
        "target_addr": local_report.get("target_addr"),
        "baseline_addr": local_report.get("baseline_addr"),
    }

    agent_result = run_unbounded_agent(
        runtime,
        claim,
        candidate=candidate,
        diff_text=diff_text,
        callee_texts=local_report.get("callee_texts") or {},
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
        "bounded_label": _coerce_str(local_report.get("label")),
        "label": _coerce_label(agent_result.get("label")),
        "summary": _coerce_str(agent_result.get("summary")),
        "failure_reason": agent_result.get("failure_reason"),
        "failure_detail": _coerce_str(agent_result.get("failure_detail")),
        "had_bounded_report": bool(claim.strip()),
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
            "bounded_function_report": {
                "function_index": func_idx,
                "target_oid": _coerce_str(target_oid),
                "baseline_oid": _coerce_str(baseline_oid),
                "baseline_addr": local_report.get("baseline_addr"),
                "target_addr": local_report.get("target_addr"),
                "label": local_report.get("label"),
                "final_md_path": local_report.get("final_md_path"),
                "diff_path": local_report.get("diff_path"),
            },
        },
    )
    return result
