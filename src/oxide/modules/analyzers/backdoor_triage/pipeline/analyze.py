import logging
import os
import time
from typing import Any, Dict, List, Optional, Set

from oxide.core import api, progress

from oxide.modules.analyzers.backdoor_triage.config import NAME
from oxide.modules.analyzers.backdoor_triage.pipeline.agent.graph import run_triage
from oxide.modules.analyzers.backdoor_triage.pipeline.agent.telemetry.agent_trace import write_trace_view
from oxide.modules.analyzers.backdoor_triage.pipeline.agent.runtime import get_or_build_runtime
from oxide.modules.analyzers.backdoor_triage.pipeline.types import AnalyzeFunctionResult, ComparisonStats
from oxide.modules.analyzers.backdoor_triage.pipeline.utils import cache, ground_truth
from oxide.modules.analyzers.backdoor_triage.pipeline.utils.callees import (
    callee_added_funcs,
    fetch_added_func_decomps,
    save_added_function_artifacts,
)
from oxide.modules.analyzers.backdoor_triage.pipeline.utils.drift_adapter import build_drift_file_pairs
from oxide.modules.analyzers.backdoor_triage.pipeline.utils.llm import load_prompt_bundle
from oxide.modules.analyzers.backdoor_triage.pipeline.utils.text_utils import (
    _EMPTY_DECOMP_FAILURE_MESSAGES,
    _coerce_result_label,
    _coerce_str,
    ensure_decimal_str,
    normalize_filter_value,
    progress_label as _progress_label_fmt,
    read_json,
    write_json,
    write_text,
)

logger = logging.getLogger(NAME)


def _make_function_dir(outdir: str, fp_idx: int, func_idx: int, baddr: str, taddr: str) -> str:
    return os.path.join(outdir, f"filepair_{fp_idx:02d}", "modified_functions", f"b{baddr}__t{taddr}")


def _reconstruct_res_from_analysis(analysis: Dict[str, Any], func_dir: str) -> Dict[str, Any]:
    timing = analysis.get("timing") or {}
    cost = analysis.get("cost") or {}
    stage3 = analysis.get("stage3") or {}
    return {
        "label": analysis.get("label", "not_safe"),
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
        "stage1_label": str(analysis.get("stage1_label") or cost.get("stage1_label") or ""),
        "stage1_why": str(analysis.get("stage1_why") or ""),
        "stage1_trigger": str(analysis.get("stage1_trigger") or ""),
        "stage1_input_tokens": int(cost.get("stage1_input_tokens") or 0),
        "stage1_output_tokens": int(cost.get("stage1_output_tokens") or 0),
        "stage1_tokens": int(cost.get("stage1_tokens") or 0),
        "stage2_ran": bool(cost.get("stage2_ran")),
        "stage3_ran": bool(stage3.get("ran")),
        "stage3_overall": stage3.get("overall"),
        "stage3_confirmed_functions": stage3.get("confirmed_functions") or [],
        "stage3_failure_reason": stage3.get("failure_reason"),
        "stage3_elapsed_s": float(stage3.get("elapsed_s") or 0.0),
        "stage3_input_tokens": int(stage3.get("input_tokens") or 0),
        "stage3_output_tokens": int(stage3.get("output_tokens") or 0),
        "stage3_total_tokens": int(stage3.get("total_tokens") or 0),
    }


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


def _get_empty_decomp_failure_messages(reason: str) -> Dict[str, str]:
    return _EMPTY_DECOMP_FAILURE_MESSAGES.get(
        reason,
        {
            "observation": "one side of the decompilation was empty. Triage skipped and recorded as failed.",
            "final_why": "One side of the decompilation was empty, so the system could not compute a two-sided function diff. The function was recorded as failed because triage did not run, not because the agent identified a trigger.",
        },
    )


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


def _resolve_bool_override(opts: Dict[str, Any], public_key: str, private_key: str) -> bool:
    """ Internal-override convention: a "_<key>" opt (set by the plugin layer, e.g. to
        force an ablation-axis value across a series run) takes priority over the
        public "<key>" opt when both are present.
    """
    return bool(opts[private_key]) if private_key in opts else bool(opts.get(public_key))


def analyze_function_pair(
    baseline_oid: str,
    target_oid: str,
    baddr: str,
    taddr: str,
    fp_idx: int,
    func_idx: int,
    outdir: str,
    opts: Dict[str, Any],
    runtime: Any,
    fingerprint: str,
    fp_total: int = 0,
    func_total: int = 0,
    added_func_decomp: Optional[Dict[str, str]] = None,
) -> AnalyzeFunctionResult:
    func_dir = _make_function_dir(outdir, fp_idx, func_idx, baddr, taddr)
    diff_raw = _resolve_bool_override(opts, "raw", "_diff_raw")
    diff_compact = bool(opts.get("_diff_compact"))
    stage1_only = bool(opts.get("stage1_only"))
    stage2_only = bool(opts.get("stage2_only"))

    os.makedirs(func_dir, exist_ok=True)
    notes_path = os.path.join(func_dir, "notes.json")
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
        notes: Dict[str, Any],
        analysis_md: str = "",
        final_md: str = "",
        trigger: str = "",
        stage1_label: str = "",
        stage1_why: str = "",
        stage1_trigger: str = "",
        stage1_input_tokens: int = 0,
        stage1_output_tokens: int = 0,
        stage1_tokens: int = 0,
        stage2_ran: bool = False,
        stage3_ran: bool = False,
        stage3_overall: Optional[str] = None,
        stage3_confirmed_functions: Optional[List[str]] = None,
        stage3_failure_reason: Optional[str] = None,
        stage3_analysis_md: str = "",
        stage3_final_md: str = "",
        stage3_elapsed_s: float = 0.0,
        stage3_input_tokens: int = 0,
        stage3_output_tokens: int = 0,
        stage3_total_tokens: int = 0,
    ) -> Dict[str, Any]:
        label = _coerce_result_label(label, failure_reason)
        flagged = label == "not_safe"
        verdict_label = "needs further inspection" if flagged else ("safe" if label == "safe" else "failed")
        verdict = f"Label: {verdict_label} - {why or 'model provided no reason'}"

        if analysis_md.strip():
            write_text(os.path.join(func_dir, "analysis.md"), analysis_md)
            notes["artifacts"].append({"kind": "stage2_analysis", "path": "analysis.md"})
        if final_md.strip():
            write_text(os.path.join(func_dir, "final.md"), final_md)
            notes["artifacts"].append({"kind": "stage2_final", "path": "final.md"})
        if os.path.exists(trace_path) and os.path.getsize(trace_path) > 0:
            notes["artifacts"].append({"kind": "stage_trace", "path": "agent_trace.log"})

        if stage3_ran:
            stage3_dir = os.path.join(func_dir, "stage3")
            os.makedirs(stage3_dir, exist_ok=True)
            if stage3_analysis_md.strip():
                write_text(os.path.join(stage3_dir, "analysis.md"), stage3_analysis_md)
                notes["artifacts"].append({"kind": "stage3_analysis", "path": "stage3/analysis.md"})
            if stage3_final_md.strip():
                write_text(os.path.join(stage3_dir, "final.md"), stage3_final_md)
                notes["artifacts"].append({"kind": "stage3_final", "path": "stage3/final.md"})
            write_json(
                os.path.join(stage3_dir, "result.json"),
                {
                    "overall": stage3_overall,
                    "confirmed_functions": stage3_confirmed_functions or [],
                    "failure_reason": stage3_failure_reason,
                    "elapsed_s": stage3_elapsed_s,
                    "llm_input_tokens": stage3_input_tokens,
                    "llm_output_tokens": stage3_output_tokens,
                    "llm_total_tokens": stage3_total_tokens,
                },
            )

        write_json(notes_path, notes)
        write_json(
            analysis_path,
            {
                "label": label,
                "stage1_label": stage1_label,
                "why": why,
                "trigger": trigger,
                "stage1_why": stage1_why,
                "stage1_trigger": stage1_trigger,
                "flagged": flagged,
                "verdict": verdict,
                "triage_ran": triage_ran,
                "failure_reason": failure_reason,
                "failure_detail": failure_detail,
                "stage1_only": stage1_only,
                "stage2_only": stage2_only,
                "artifacts": {
                    "analysis_md": bool(analysis_md.strip()),
                    "final_md": bool(final_md.strip()),
                    "agent_trace": bool(os.path.exists(trace_path) and os.path.getsize(trace_path) > 0),
                },
                "timing": {"diff_elapsed_s": diff_elapsed_s, "llm_elapsed_s": llm_elapsed_s},
                "cost": {
                    "llm_input_tokens": llm_input_tokens,
                    "llm_output_tokens": llm_output_tokens,
                    "llm_total_tokens": llm_total_tokens,
                    "stage1_input_tokens": stage1_input_tokens,
                    "stage1_output_tokens": stage1_output_tokens,
                    "stage1_tokens": stage1_tokens,
                    "stage2_ran": stage2_ran,
                },
                "stage3": {
                    "ran": stage3_ran,
                    "overall": stage3_overall,
                    "confirmed_functions": stage3_confirmed_functions or [],
                    "failure_reason": stage3_failure_reason,
                    "elapsed_s": stage3_elapsed_s,
                    "input_tokens": stage3_input_tokens,
                    "output_tokens": stage3_output_tokens,
                    "total_tokens": stage3_total_tokens,
                },
            },
        )
        write_text(os.path.join(func_dir, "verdict.txt"), verdict)
        return {
            "label": label,
            "why": why,
            "trigger": trigger,
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
            "stage1_label": stage1_label,
            "stage1_why": stage1_why,
            "stage1_trigger": stage1_trigger,
            "stage1_input_tokens": stage1_input_tokens,
            "stage1_output_tokens": stage1_output_tokens,
            "stage1_tokens": stage1_tokens,
            "stage2_ran": stage2_ran,
            "stage3_ran": stage3_ran,
            "stage3_overall": stage3_overall,
            "stage3_confirmed_functions": stage3_confirmed_functions or [],
            "stage3_failure_reason": stage3_failure_reason,
            "stage3_elapsed_s": stage3_elapsed_s,
            "stage3_input_tokens": stage3_input_tokens,
            "stage3_output_tokens": stage3_output_tokens,
            "stage3_total_tokens": stage3_total_tokens,
        }

    def _run_fresh() -> Dict[str, Any]:
        notes: Dict[str, Any] = {"observations": [], "artifacts": []}

        def _fetch_and_write_diff() -> Any:
            diff_t0 = time.perf_counter()
            diff = api.retrieve(
                "function_decomp_diff", [target_oid, baseline_oid],
                {"target": taddr, "baseline": baddr, "raw": diff_raw, "compact": (False if diff_raw else diff_compact)},
            )
            diff_elapsed_s = time.perf_counter() - diff_t0
            diff_info = normalize_function_decomp_diff_response(diff)
            write_diff_artifacts(func_dir, diff_info["unified"], diff_info["artifact_meta"])
            notes["artifacts"].append({"kind": "diff_meta", "path": "diff_meta.json"})
            return diff_info, diff_elapsed_s

        diff_info, diff_elapsed_s = _fetch_and_write_diff()

        if opts.get("no_triage"):
            return _write_analysis(
                label="failed", why="Triage disabled by configuration.", triage_ran=False,
                failure_reason="triage_disabled", failure_detail="", diff_elapsed_s=diff_elapsed_s,
                llm_elapsed_s=0.0, llm_input_tokens=0, llm_output_tokens=0, llm_total_tokens=0, notes=notes,
            )

        triage_ran = False
        failure_reason: Optional[str] = None

        if diff_info["tool_error"]:
            notes["observations"].append(f"diff tool failed: {diff_info.get('error')!r}")
            return _write_analysis(
                label="failed", why="Diff generation failed before triage could run.", triage_ran=False,
                failure_reason="diff_tool_error", failure_detail="", diff_elapsed_s=diff_elapsed_s,
                llm_elapsed_s=0.0, llm_input_tokens=0, llm_output_tokens=0, llm_total_tokens=0, notes=notes,
            )

        empty_decomp_reason = diff_info.get("empty_decomp_reason")
        if empty_decomp_reason:
            failure_reason = str(empty_decomp_reason)
            messages = _get_empty_decomp_failure_messages(failure_reason)
            notes["observations"].append(messages["observation"])
            return _write_analysis(
                label="failed", why=messages["final_why"], triage_ran=False,
                failure_reason=failure_reason, failure_detail="", diff_elapsed_s=diff_elapsed_s,
                llm_elapsed_s=0.0, llm_input_tokens=0, llm_output_tokens=0, llm_total_tokens=0, notes=notes,
            )

        unified = diff_info["unified"] or ""

        callee_texts: Dict[str, str] = {}
        if unified.strip() and added_func_decomp:
            callee_texts = callee_added_funcs(unified, added_func_decomp, target_oid)
            if callee_texts:
                logger.info(
                    "%s found %d newly-added callee(s) referenced in diff; routing to agent",
                    func_dir, len(callee_texts),
                )

        llm_elapsed_s = 0.0
        llm_input_tokens = 0
        llm_output_tokens = 0
        llm_total_tokens = 0
        stage1_label = ""
        stage1_input_tokens = 0
        stage1_output_tokens = 0
        stage1_tokens = 0
        stage2_ran = False

        if unified.strip():
            triage_ran = True
            triage = run_triage(
                runtime,
                unified_diff=unified,
                notes=notes,
                target_oid=target_oid, baseline_oid=baseline_oid,
                target_addr=taddr, baseline_addr=baddr,
                stage1_only=stage1_only,
                stage2_only=stage2_only,
                callee_texts=callee_texts,
                trace_path=trace_path,
                fp_idx=fp_idx, fp_total=fp_total, func_idx=func_idx, func_total=func_total,
            )
            label = triage.get("label", "failed")
            why = (triage.get("why") or "").strip()
            trigger = (triage.get("trigger") or "").strip()
            stage1_why = (triage.get("stage1_why") or "").strip()
            stage1_trigger = (triage.get("stage1_trigger") or "").strip()
            failure_reason = triage.get("failure_reason")
            failure_detail = (triage.get("failure_detail") or "").strip()
            llm_elapsed_s = float(triage.get("llm_elapsed_s") or 0.0)
            llm_input_tokens = int(triage.get("llm_input_tokens") or 0)
            llm_output_tokens = int(triage.get("llm_output_tokens") or 0)
            llm_total_tokens = int(triage.get("llm_total_tokens") or 0)
            stage1_label = str(triage.get("stage1_label") or "")
            stage1_input_tokens = int(triage.get("stage1_input_tokens") or 0)
            stage1_output_tokens = int(triage.get("stage1_output_tokens") or 0)
            stage1_tokens = int(triage.get("stage1_tokens") or 0)
            stage2_ran = bool(triage.get("stage2_ran"))
        else:
            failure_reason = "empty_unified_diff"
            failure_detail = ""
            notes["observations"].append("empty unified diff; recorded as failed")
            label = "failed"
            why = "Triage did not run because the unified diff was empty."
            trigger = stage1_why = stage1_trigger = ""
            triage = {"analysis_md": "", "final_md": ""}

        label = _coerce_result_label(label, failure_reason)
        if failure_detail and label == "failed":
            why = f"{why} Detail: {failure_detail}".strip()
        result = _write_analysis(
            label=label, why=why, triage_ran=triage_ran, failure_reason=failure_reason,
            failure_detail=failure_detail, diff_elapsed_s=diff_elapsed_s, llm_elapsed_s=llm_elapsed_s,
            llm_input_tokens=llm_input_tokens, llm_output_tokens=llm_output_tokens,
            llm_total_tokens=llm_total_tokens, notes=notes,
            analysis_md=_coerce_str(triage.get("analysis_md")), final_md=_coerce_str(triage.get("final_md")),
            trigger=trigger, stage1_label=stage1_label, stage1_why=stage1_why, stage1_trigger=stage1_trigger,
            stage1_input_tokens=stage1_input_tokens,
            stage1_output_tokens=stage1_output_tokens, stage1_tokens=stage1_tokens, stage2_ran=stage2_ran,
            stage3_ran=bool(triage.get("stage3_ran")),
            stage3_overall=triage.get("stage3_overall"),
            stage3_confirmed_functions=triage.get("stage3_confirmed_functions") or [],
            stage3_failure_reason=triage.get("stage3_failure_reason"),
            stage3_analysis_md=_coerce_str(triage.get("stage3_analysis_md")),
            stage3_final_md=_coerce_str(triage.get("stage3_final_md")),
            stage3_elapsed_s=float(triage.get("stage3_elapsed_s") or 0.0),
            stage3_input_tokens=int(triage.get("stage3_input_tokens") or 0),
            stage3_output_tokens=int(triage.get("stage3_output_tokens") or 0),
            stage3_total_tokens=int(triage.get("stage3_total_tokens") or 0),
        )
        if os.path.exists(trace_path):
            write_trace_view(trace_path, os.path.join(func_dir, "trace_view.txt"))
        return result

    def _compute() -> Dict[str, Any]:
        if os.path.exists(analysis_path):
            try:
                analysis_cached = read_json(analysis_path)
                return _reconstruct_res_from_analysis(analysis_cached, func_dir)
            except Exception as exc:
                logger.warning("failed to load cached analysis at %s: %s. Re-running.", analysis_path, exc)
        return _run_fresh()

    cache_key = cache.function_triage_cache_key(target_oid, baseline_oid, baddr, taddr, fingerprint)
    return cache.get_or_compute(NAME, cache_key, _compute)


def run_comparison(target: str, baseline: str, outdir: str, opts: Dict[str, Any]) -> Dict[str, Any]:
    os.makedirs(outdir, exist_ok=True)

    runtime = get_or_build_runtime(opts)
    fingerprint = cache.opts_fingerprint(opts, load_prompt_bundle(opts))
    include_added_callees = bool(opts.get("include_added_callees", True))
    diff_raw_for_stats = _resolve_bool_override(opts, "raw", "_diff_raw")

    filter_val = normalize_filter_value(opts.get("filter"))
    logger.info(
        "Invoking drift with target='%s', baseline='%s', filter='%s'",
        target, baseline, filter_val if filter_val is not None else "<none>",
    )

    total_t0 = time.perf_counter()

    drift_t0 = time.perf_counter()
    drift_json = build_drift_file_pairs(target, baseline, filter_val) or {}
    drift_elapsed_s = time.perf_counter() - drift_t0
    write_json(os.path.join(outdir, "drift_raw.json"), drift_json)

    file_pairs: List[Dict[str, Any]] = drift_json.get("file_pairs", []) or []

    report_lines: List[str] = ["# Firmware Triage Report (binary suspicion)"]
    target_name = str(target)
    baseline_name = str(baseline)

    report_lines.append(f"Target CID:   {target}")
    try:
        target_name = api.get_colname_from_oid(target)
        report_lines.append(f"Target Name:  {target_name}")
    except Exception:
        report_lines.append("Target Name:  <unavailable>")

    report_lines.append(f"Baseline CID: {baseline}")
    try:
        baseline_name = api.get_colname_from_oid(baseline)
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
    sum_stage1_input_tokens = 0
    sum_stage1_output_tokens = 0
    sum_stage1_tokens = 0
    sum_stage2_input_tokens = 0
    sum_stage2_output_tokens = 0
    sum_stage2_tokens = 0
    sum_stage3_input_tokens = 0
    sum_stage3_output_tokens = 0
    sum_stage3_tokens = 0
    stage1_flagged_count = 0
    stage2_ran_count = 0
    stage3_ran_count = 0
    stage3_confirmed_count = 0

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
            fp_idx, len(file_pairs), len(filtered_mods), len(added_funcs),
            len(excluded_mods) if hasattr(excluded_mods, "__len__") else "unknown",
        )

        added_func_decomp: Dict[str, str] = {}
        if include_added_callees and added_funcs:
            added_func_decomp = fetch_added_func_decomps(target_oid, added_funcs)
            save_added_function_artifacts(
                target_oid=target_oid, added_functions=added_funcs, fp_idx=fp_idx,
                outdir=outdir, decomp_map=added_func_decomp,
            )

        prog = progress.Progress(len(filtered_mods))

        for func_idx, modified in enumerate(filtered_mods, 1):
            baseline_addr = ensure_decimal_str(modified.get("baseline_func_addr"))
            target_addr = ensure_decimal_str(modified.get("target_func_addr"))
            progress_label = _progress_label_fmt(
                fp_idx=fp_idx, fp_total=len(file_pairs), func_idx=func_idx, func_total=len(filtered_mods),
            )
            logger.info("%s start baseline_addr=%s target_addr=%s", progress_label, baseline_addr, target_addr)

            result = analyze_function_pair(
                baseline_oid=baseline_oid, target_oid=target_oid, baddr=baseline_addr, taddr=target_addr,
                fp_idx=fp_idx, fp_total=len(file_pairs), func_idx=func_idx, func_total=len(filtered_mods),
                outdir=outdir, opts=opts, runtime=runtime, fingerprint=fingerprint,
                added_func_decomp=added_func_decomp,
            )

            _llm_in = int(result.get("llm_input_tokens") or 0)
            _llm_out = int(result.get("llm_output_tokens") or 0)
            _llm_tot = int(result.get("llm_total_tokens") or 0)
            _s1_in = int(result.get("stage1_input_tokens") or 0)
            _s1_out = int(result.get("stage1_output_tokens") or 0)
            _s1_tot = int(result.get("stage1_tokens") or 0)
            _s2_in = _llm_in - _s1_in
            _s2_out = _llm_out - _s1_out
            _s2_tot = _llm_tot - _s1_tot
            _s3_in = int(result.get("stage3_input_tokens") or 0)
            _s3_out = int(result.get("stage3_output_tokens") or 0)
            _s3_tot = int(result.get("stage3_total_tokens") or 0)

            sum_diff_elapsed_s += float(result.get("diff_elapsed_s") or 0.0)
            sum_llm_elapsed_s += float(result.get("llm_elapsed_s") or 0.0)
            sum_llm_input_tokens += _llm_in
            sum_llm_output_tokens += _llm_out
            sum_llm_total_tokens += _llm_tot
            sum_stage1_input_tokens += _s1_in
            sum_stage1_output_tokens += _s1_out
            sum_stage1_tokens += _s1_tot
            sum_stage2_input_tokens += _s2_in
            sum_stage2_output_tokens += _s2_out
            sum_stage2_tokens += _s2_tot
            sum_stage3_input_tokens += _s3_in
            sum_stage3_output_tokens += _s3_out
            sum_stage3_tokens += _s3_tot
            if result.get("stage1_label") == "not_safe":
                stage1_flagged_count += 1
            if result.get("stage2_ran"):
                stage2_ran_count += 1
            if result.get("stage3_ran"):
                stage3_ran_count += 1
                if result.get("stage3_overall") == "backdoor":
                    stage3_confirmed_count += 1

            final_label = _coerce_result_label(result.get("label"), result.get("failure_reason"))
            flagged_final = bool(final_label == "not_safe")

            per_function_results.append({
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
                "llm_input_tokens": _llm_in,
                "llm_output_tokens": _llm_out,
                "llm_total_tokens": _llm_tot,
                "triage_ran": bool(result.get("triage_ran")),
                "failure_reason": result.get("failure_reason"),
                "failure_detail": result.get("failure_detail", ""),
                "stage1_label": result.get("stage1_label", ""),
                "stage1_flagged": result.get("stage1_label") == "not_safe",
                "stage1_input_tokens": _s1_in,
                "stage1_output_tokens": _s1_out,
                "stage1_tokens": _s1_tot,
                "stage2_ran": bool(result.get("stage2_ran")),
                "stage2_input_tokens": _s2_in,
                "stage2_output_tokens": _s2_out,
                "stage2_tokens": _s2_tot,
                "stage3_ran": bool(result.get("stage3_ran")),
                "stage3_overall": result.get("stage3_overall"),
                "stage3_confirmed_functions": result.get("stage3_confirmed_functions") or [],
                "stage3_failure_reason": result.get("stage3_failure_reason"),
                "stage3_input_tokens": _s3_in,
                "stage3_output_tokens": _s3_out,
                "stage3_tokens": _s3_tot,
            })

            failure_reason = _coerce_str(result.get("failure_reason"))
            if failure_reason and failure_reason not in _EMPTY_DECOMP_FAILURE_MESSAGES:
                failure_reason_counts[failure_reason] = failure_reason_counts.get(failure_reason, 0) + 1

            if flagged_final:
                flagged_filtered += 1
                triage_index.append({
                    "filepair_index": fp_idx,
                    "function_index": func_idx,
                    "baseline_addr": baseline_addr,
                    "target_addr": target_addr,
                    "label": final_label,
                    "verdict": result.get("verdict"),
                    "dir": result.get("func_dir"),
                    "baseline_oid": baseline_oid,
                    "target_oid": target_oid,
                    "stage3_ran": bool(result.get("stage3_ran")),
                    "stage3_overall": result.get("stage3_overall"),
                })
            elif final_label == "failed":
                failed_filtered += 1
            elif final_label == "skipped":
                skipped_filtered += 1
            else:
                safe_filtered += 1

            logger.info(
                "%s done label=%s flagged=%s diff=%.2fs llm=%.2fs tokens_in=%d tokens_out=%d tokens_total=%d",
                progress_label, final_label, flagged_final,
                float(result.get("diff_elapsed_s") or 0.0), float(result.get("llm_elapsed_s") or 0.0),
                int(result.get("llm_input_tokens") or 0), int(result.get("llm_output_tokens") or 0),
                int(result.get("llm_total_tokens") or 0),
            )
            prog.tick()

    overall_safe = safe_filtered + (total_modified_all - total_modified_filtered)
    elapsed_s = time.perf_counter() - total_t0
    triage_elapsed_s_excluding_drift = max(0.0, elapsed_s - drift_elapsed_s)
    other_elapsed_s = max(0.0, triage_elapsed_s_excluding_drift - (sum_diff_elapsed_s + sum_llm_elapsed_s))

    gt = opts["_ground_truth"] if "_ground_truth" in opts else ground_truth.load_ground_truth_file(opts.get("ground_truth"))
    gt_norm = ground_truth.get_ground_truth_for_target(gt or {}, target_name)

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
            id(row) for row in per_function_results if ground_truth.gt_row_matches_any(row, gt_norm)
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

    stats: ComparisonStats = {
        "target": target,
        "baseline": baseline,
        "diff_raw": diff_raw_for_stats,
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
        "stage1_flagged_count": stage1_flagged_count,
        "stage1_input_tokens": sum_stage1_input_tokens,
        "stage1_output_tokens": sum_stage1_output_tokens,
        "stage1_tokens": sum_stage1_tokens,
        "stage2_ran_count": stage2_ran_count,
        "stage2_input_tokens": sum_stage2_input_tokens,
        "stage2_output_tokens": sum_stage2_output_tokens,
        "stage2_tokens": sum_stage2_tokens,
        "stage3_ran_count": stage3_ran_count,
        "stage3_confirmed_count": stage3_confirmed_count,
        "stage3_input_tokens": sum_stage3_input_tokens,
        "stage3_output_tokens": sum_stage3_output_tokens,
        "stage3_tokens": sum_stage3_tokens,
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
        "Done %s -> %s: modified_all=%d filtered=%d identified=%d hit_final=%s elapsed=%.2fs "
        "(drift=%.2fs llm=%.2fs tokens_in=%d tokens_out=%d tokens_total=%d)",
        target_name, baseline_name, total_modified_all, total_modified_filtered, identified, hit_final,
        elapsed_s, drift_elapsed_s, sum_llm_elapsed_s, sum_llm_input_tokens, sum_llm_output_tokens, sum_llm_total_tokens,
    )

    return {
        "target": target,
        "baseline": baseline,
        "stats": stats,
        "triage_index": triage_index,
        "per_function_results": per_function_results,
        "file_pairs": file_pairs,
    }
