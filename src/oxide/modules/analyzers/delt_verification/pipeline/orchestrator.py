import logging
import os
import time
from typing import Any, Dict, List, Optional, Set, Tuple

from oxide.core import api

from oxide.modules.analyzers.delt_verification.config import NAME
from oxide.modules.analyzers.delt_verification.pipeline.agents.runtime import (
    get_or_build_runtime,
)
from oxide.modules.analyzers.delt_verification.pipeline.agents.telemetry.agent_trace import (
    write_trace_view,
)
from oxide.modules.analyzers.delt_verification.pipeline.cache import keys as cache_keys
from oxide.modules.analyzers.delt_verification.pipeline.cache.artifacts import (
    restore_cached_binary_context_artifacts,
    restore_cached_triage_artifacts,
    restore_cached_verification_artifacts,
)
from oxide.modules.analyzers.delt_verification.pipeline.cache.store import (
    load_cached_stage_result,
    stage_cache_opts,
    store_cached_stage_result,
)
from oxide.modules.analyzers.delt_verification.pipeline.phases.binary_context import (
    run_binary_context_analysis,
)
from oxide.modules.analyzers.delt_verification.pipeline.phases.triage import run_triage
from oxide.modules.analyzers.delt_verification.pipeline.phases.verification import (
    run_verification,
)
from oxide.modules.analyzers.delt_verification.pipeline.reporting.results import (
    build_analyzer_result,
    write_comparison_outputs,
)
from oxide.modules.analyzers.delt_verification.pipeline.types import AnalyzeFunctionResult, ComparisonStats
from oxide.modules.analyzers.delt_verification.pipeline.utils import ground_truth
from oxide.modules.analyzers.delt_verification.pipeline.utils.callees import (
    AddedCalleeIndex,
    build_added_callee_index,
    callee_added_funcs,
    fetch_added_func_decomps,
    save_added_function_artifacts,
)
from oxide.modules.analyzers.delt_verification.pipeline.utils.drift_adapter import build_drift_file_pairs
from oxide.modules.analyzers.delt_verification.pipeline.utils.llm import load_prompt_bundle
from oxide.modules.analyzers.delt_verification.pipeline.utils.prewarm import prewarm_filepair_artifacts
from oxide.modules.analyzers.delt_verification.pipeline.utils.text_utils import (
    _EMPTY_DECOMP_FAILURE_MESSAGES,
    _coerce_result_label,
    _coerce_str,
    ascii_sanitize,
    ensure_decimal_str,
    normalize_filter_value,
    write_json,
    write_text,
)

logger = logging.getLogger(NAME)


def _normalize_run_opts(opts: Dict[str, Any]) -> Dict[str, Any]:
    run_opts = dict(opts)
    diff_mode = _coerce_str(run_opts.get("diff_mode")).lower()
    if diff_mode:
        if diff_mode not in {"raw", "processed"}:
            raise ValueError("diff_mode must be one of: raw, processed")
        run_opts["raw"] = diff_mode == "raw"
    else:
        diff_mode = "raw" if _resolve_bool_override(run_opts, "raw", "_diff_raw") else "processed"

    run_opts["diff_mode"] = diff_mode
    return run_opts


def _display_filter_mode(filter_val: Optional[str]) -> str:
    if not filter_val:
        return "NONE"
    mapping = {
        "Call_OR_Control_Modified": "OR",
        "Control_Call_Modified": "AND",
    }
    return mapping.get(filter_val, str(filter_val))


def _make_function_dir(outdir: str, fp_idx: int, func_idx: int, baddr: str, taddr: str) -> str:
    return os.path.join(outdir, f"filepair_{fp_idx:02d}", "modified_functions", f"b{baddr}__t{taddr}")


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


def _read_text_file(path: str) -> str:
    if not path or not os.path.isfile(path):
        return ""
    try:
        with open(path, "r", encoding="utf-8") as handle:
            return handle.read()
    except OSError:
        return ""


def write_diff_artifacts(triage_dir: str, unified: str, diff_meta: Dict[str, Any]) -> None:
    write_text(f"{triage_dir}/diff.txt", unified or "")
    write_json(f"{triage_dir}/diff_meta.json", diff_meta or {})


def write_agent_inputs(triage_dir: str, unified: str, callee_texts: Dict[str, str]) -> None:
    """Mirror the exact files the triage agent would see under /inputs/ to
    triage_dir/agent_inputs/, so a dry run produces the full evidence set the agent
    receives without running it. Layout matches agent_runtime.build_agent_payload:
    unified_diff.txt plus one added_functions/<addr>.c per reachable added callee."""
    inputs_dir = os.path.join(triage_dir, "agent_inputs")
    os.makedirs(inputs_dir, exist_ok=True)
    write_text(os.path.join(inputs_dir, "unified_diff.txt"), ascii_sanitize(unified or ""))
    added_dir = os.path.join(inputs_dir, "added_functions")
    for addr, text in (callee_texts or {}).items():
        if text.strip():
            os.makedirs(added_dir, exist_ok=True)
            write_text(os.path.join(added_dir, f"{addr}.c"), text)


def _resolve_bool_override(opts: Dict[str, Any], public_key: str, private_key: str) -> bool:
    """ Internal-override convention: a "_<key>" opt (set by the plugin layer, e.g. to
        force an ablation-axis value across a series run) takes priority over the
        public "<key>" opt when both are present.
    """
    return bool(opts[private_key]) if private_key in opts else bool(opts.get(public_key))


def _set_pipeline_outcome(row: Dict[str, Any], label: str) -> None:
    """ Record a candidate's end-to-end verdict on its per-function row.

        pipeline_* and final_* are the same verdict under both names, so a reader of
        either agrees. What triage decided before any escalation stays available
        separately as triage_label/triage_flagged.
    """
    flagged = label == "not_safe"
    row["pipeline_label"] = label
    row["pipeline_flagged"] = flagged
    row["final_label"] = label
    row["flagged_final"] = flagged
    row["dismissed_final"] = label == "safe"
    row["failed_final"] = label == "failed"
    row["skipped_final"] = label == "skipped"


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
    triage_fingerprint: str,
    fp_total: int = 0,
    func_total: int = 0,
    added_callee_index: Optional[AddedCalleeIndex] = None,
) -> AnalyzeFunctionResult:
    func_dir = _make_function_dir(outdir, fp_idx, func_idx, baddr, taddr)
    triage_dir = os.path.join(func_dir, "triage")
    diff_raw = _resolve_bool_override(opts, "raw", "_diff_raw")
    triage_cache_key = cache_keys.triage_result_cache_key(
        target_oid, baseline_oid, baddr, taddr, triage_fingerprint
    )
    triage_cache_opts = stage_cache_opts("triage_result", triage_fingerprint)

    os.makedirs(func_dir, exist_ok=True)
    os.makedirs(triage_dir, exist_ok=True)
    notes_path = os.path.join(triage_dir, "notes.json")
    analysis_path = os.path.join(triage_dir, "analysis.json")
    trace_path = os.path.join(triage_dir, "agent_trace.log")

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
        final_md: str = "",
        callee_augmented: bool = False,
        diff_text: str = "",
        diff_meta: Optional[Dict[str, Any]] = None,
    ) -> Dict[str, Any]:
        label = _coerce_result_label(label, failure_reason)
        flagged = label == "not_safe"
        verdict_label = "needs further inspection" if flagged else ("safe" if label == "safe" else "failed")
        verdict = f"Label: {verdict_label} - {why or 'model provided no reason'}"

        if final_md.strip():
            write_text(os.path.join(triage_dir, "final.md"), final_md)
            notes["artifacts"].append({"kind": "agent_final", "path": "triage/final.md"})
        if os.path.exists(trace_path) and os.path.getsize(trace_path) > 0:
            notes["artifacts"].append({"kind": "agent_trace", "path": "triage/agent_trace.log"})

        write_json(notes_path, notes)
        write_json(
            analysis_path,
            {
                "label": label,
                "why": why,
                "flagged": flagged,
                "verdict": verdict,
                "triage_ran": triage_ran,
                "failure_reason": failure_reason,
                "failure_detail": failure_detail,
                "callee_augmented": callee_augmented,
                "artifacts": {
                    "final_md": bool(final_md.strip()),
                    "agent_trace": bool(os.path.exists(trace_path) and os.path.getsize(trace_path) > 0),
                },
                "timing": {"diff_elapsed_s": diff_elapsed_s, "llm_elapsed_s": llm_elapsed_s},
                "cost": {
                    "llm_input_tokens": llm_input_tokens,
                    "llm_output_tokens": llm_output_tokens,
                    "llm_total_tokens": llm_total_tokens,
                },
            },
        )
        write_text(os.path.join(triage_dir, "verdict.txt"), verdict)
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
            "callee_augmented": callee_augmented,
            "triage_final_md": final_md,
            "triage_diff_text": diff_text,
            "triage_diff_meta": diff_meta or {},
        }

    cached_triage = load_cached_stage_result(target_oid, triage_cache_opts, triage_cache_key)
    if cached_triage is not None:
        restore_cached_triage_artifacts(triage_dir, cached_triage)
        return cached_triage

    def _run_fresh() -> Dict[str, Any]:
        notes: Dict[str, Any] = {"observations": [], "artifacts": []}

        def _fetch_and_write_diff() -> Any:
            diff_t0 = time.perf_counter()
            diff = api.retrieve(
                "function_decomp_diff", [target_oid, baseline_oid],
                {"target": taddr, "baseline": baddr, "raw": diff_raw},
            )
            diff_elapsed_s = time.perf_counter() - diff_t0
            diff_info = normalize_function_decomp_diff_response(diff)
            write_diff_artifacts(triage_dir, diff_info["unified"], diff_info["artifact_meta"])
            notes["artifacts"].append({"kind": "diff_meta", "path": "triage/diff_meta.json"})
            return diff_info, diff_elapsed_s

        diff_info, diff_elapsed_s = _fetch_and_write_diff()

        if opts.get("no_triage"):
            # Dry run: produce everything the triage agent would receive (the unified diff
            # plus the reachable added-callee decomps) on disk, but don't run the agent.
            unified = diff_info.get("unified") or ""
            callee_texts: Dict[str, str] = {}
            if unified.strip() and not diff_info["tool_error"]:
                callee_texts = callee_added_funcs(taddr, added_callee_index)
            write_agent_inputs(triage_dir, unified, callee_texts)
            return _write_analysis(
                label="skipped", why="Dry run: triage inputs produced, agent not run.", triage_ran=False,
                failure_reason="dry_run", failure_detail="", diff_elapsed_s=diff_elapsed_s,
                llm_elapsed_s=0.0, llm_input_tokens=0, llm_output_tokens=0, llm_total_tokens=0, notes=notes,
                callee_augmented=bool(callee_texts), diff_text=unified,
                diff_meta=diff_info.get("artifact_meta") or {},
            )

        triage_ran = False
        failure_reason: Optional[str] = None

        if diff_info["tool_error"]:
            notes["observations"].append(f"diff tool failed: {diff_info.get('error')!r}")
            return _write_analysis(
                label="failed", why="Diff generation failed before triage could run.", triage_ran=False,
                failure_reason="diff_tool_error", failure_detail="", diff_elapsed_s=diff_elapsed_s,
                llm_elapsed_s=0.0, llm_input_tokens=0, llm_output_tokens=0, llm_total_tokens=0, notes=notes,
                diff_text=diff_info.get("unified") or "", diff_meta=diff_info.get("artifact_meta") or {},
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
                diff_text=diff_info.get("unified") or "", diff_meta=diff_info.get("artifact_meta") or {},
            )

        unified = diff_info["unified"] or ""

        callee_texts: Dict[str, str] = {}
        if unified.strip():
            callee_texts = callee_added_funcs(taddr, added_callee_index)

        llm_elapsed_s = 0.0
        llm_input_tokens = 0
        llm_output_tokens = 0
        llm_total_tokens = 0

        if unified.strip():
            triage_ran = True
            triage = run_triage(
                runtime,
                unified_diff=unified,
                notes=notes,
                callee_texts=callee_texts,
                trace_path=trace_path,
            )
            label = triage.get("label", "failed")
            why = (triage.get("why") or "").strip()
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
            triage = {"final_md": ""}

        label = _coerce_result_label(label, failure_reason)
        if failure_detail and label == "failed":
            why = f"{why} Detail: {failure_detail}".strip()
        result = _write_analysis(
            label=label, why=why, triage_ran=triage_ran, failure_reason=failure_reason,
            failure_detail=failure_detail, diff_elapsed_s=diff_elapsed_s, llm_elapsed_s=llm_elapsed_s,
            llm_input_tokens=llm_input_tokens, llm_output_tokens=llm_output_tokens,
            llm_total_tokens=llm_total_tokens, notes=notes,
            final_md=_coerce_str(triage.get("final_md")),
            callee_augmented=bool(callee_texts), diff_text=unified,
            diff_meta=diff_info.get("artifact_meta") or {},
        )
        if os.path.exists(trace_path):
            write_trace_view(trace_path, os.path.join(triage_dir, "trace_view.txt"))
        store_cached_stage_result(target_oid, triage_cache_opts, triage_cache_key, result)
        return result

    return _run_fresh()


def _run_function_pairs(
    filtered_mods: List[Dict[str, Any]],
    *,
    baseline_oid: Any,
    target_oid: Any,
    fp_idx: int,
    fp_total: int,
    outdir: str,
    opts: Dict[str, Any],
    runtime: Any,
    triage_fingerprint: str,
    added_callee_index: Optional[AddedCalleeIndex],
    label: str,
) -> List[Tuple[int, Dict[str, Any], Any]]:
    """Triage every modified function in a file pair, returning results in function order.

    Sequential by design: one comparison owns one model endpoint. Concurrency is the
    caller's job, run one whole comparison per endpoint (see delt_verification_experiment),
    which parallelizes triage, binary context, and verification rather than triage alone.

    Progress is logged rather than drawn as a bar. Several comparisons run at once and a
    Progress bar redraws one stderr line with a carriage return, so concurrent bars
    overwrite each other. Each line carries `label` so it can be attributed to a sample."""
    func_total = len(filtered_mods)
    # Cap reporting at roughly 20 lines per file pair, so a 1,000-candidate sample does
    # not log 1,000 times and a small one still reports every function.
    step = max(1, func_total // 20)
    t0 = time.perf_counter()
    ordered: List[Tuple[int, Dict[str, Any], Any]] = []
    for func_idx, modified in enumerate(filtered_mods, 1):
        baseline_addr = ensure_decimal_str(modified.get("baseline_func_addr"))
        target_addr = ensure_decimal_str(modified.get("target_func_addr"))
        result = analyze_function_pair(
            baseline_oid=baseline_oid, target_oid=target_oid, baddr=baseline_addr, taddr=target_addr,
            fp_idx=fp_idx, fp_total=fp_total, func_idx=func_idx, func_total=func_total,
            outdir=outdir, opts=opts, runtime=runtime, triage_fingerprint=triage_fingerprint,
            added_callee_index=added_callee_index,
        )
        ordered.append((func_idx, modified, result))
        if func_idx % step == 0 or func_idx == func_total:
            elapsed = time.perf_counter() - t0
            rate = func_idx / elapsed if elapsed > 0 else 0.0
            logger.info(
                "%s: triage %d/%d (%.0f%%) elapsed %.1fm eta %.1fm",
                label, func_idx, func_total, 100.0 * func_idx / func_total,
                elapsed / 60.0,
                ((func_total - func_idx) / rate / 60.0) if rate > 0 else 0.0,
            )
    return ordered


def run_comparison(target: str, baseline: str, outdir: str, opts: Dict[str, Any]) -> Dict[str, Any]:
    opts = _normalize_run_opts(opts)
    os.makedirs(outdir, exist_ok=True)

    # Dry run (no_triage): no model is needed, so skip building the Ollama runtime and run
    # single-threaded -- the per-function loop only fetches diffs and writes agent inputs.
    no_triage = bool(opts.get("no_triage"))
    runtime = None if no_triage else get_or_build_runtime(opts)
    prompt_bundle = load_prompt_bundle(opts)
    triage_fingerprint = cache_keys.triage_opts_fingerprint(opts, prompt_bundle)
    binary_context_fingerprint = cache_keys.binary_context_opts_fingerprint(opts, prompt_bundle)
    verification_fingerprint = cache_keys.verification_opts_fingerprint(opts, prompt_bundle)
    include_added_callees = bool(opts.get("include_added_callees", True))
    diff_raw_for_stats = _resolve_bool_override(opts, "raw", "_diff_raw")

    filter_val = normalize_filter_value(opts.get("filter"))
    diff_mode = _coerce_str(opts.get("diff_mode")) or ("raw" if diff_raw_for_stats else "processed")
    filter_mode = _display_filter_mode(filter_val)
    total_t0 = time.perf_counter()

    drift_t0 = time.perf_counter()
    drift_json = build_drift_file_pairs(target, baseline, filter_val) or {}
    drift_elapsed_s = time.perf_counter() - drift_t0
    write_json(os.path.join(outdir, "drift_raw.json"), drift_json)

    file_pairs: List[Dict[str, Any]] = drift_json.get("file_pairs", []) or []

    report_lines: List[str] = ["# Firmware Two-Stage Report (binary suspicion)"]
    target_name = str(target)
    baseline_name = str(baseline)

    report_lines.append(f"Target CID:   {target}")
    try:
        target_name = api.get_colname_from_oid(target)
        report_lines.append(f"Target Name:  {target_name}")
    except Exception:
        report_lines.append("Target Name:  <unavailable>")
    if not target_name:
        target_name = str(target)

    report_lines.append(f"Baseline CID: {baseline}")
    try:
        baseline_name = api.get_colname_from_oid(baseline)
        report_lines.append(f"Baseline Name:{baseline_name}")
    except Exception:
        report_lines.append("Baseline Name:<unavailable>")
    if not baseline_name:
        baseline_name = str(baseline)

    report_lines.append(f"Diff Mode:    {diff_mode}")
    report_lines.append(f"Filter:       {filter_mode}")
    report_lines.append("")

    # gt_only: restrict triage to the ground-truth insertion function(s) so a
    # backdoor-recall check spends LLM budget only on the GT candidate. The full
    # filtered set is still counted/reported; only the triaged subset shrinks.
    # Pairs with no ground truth (e.g. safe variants) triage nothing under gt_only.
    gt_only = bool(opts.get("gt_only"))
    gt_only_norm: Optional[Dict[str, Any]] = None
    if gt_only:
        gt_all = (
            opts["_ground_truth"]
            if "_ground_truth" in opts
            else ground_truth.load_ground_truth_file(opts.get("ground_truth"))
        )
        gt_only_norm = ground_truth.get_ground_truth_for_target(
            gt_all or {}, target_name, pair_dir=outdir, target_oid=target,
        )
        if gt_only_norm:
            logger.info(
                "gt_only: triaging only the %d ground-truth function(s) for %s",
                len(gt_only_norm.get("targets", []) or []), target_name,
            )
        else:
            logger.info("gt_only: no ground truth for %s; triaging no functions", target_name)

    triage_index: List[Dict[str, Any]] = []
    per_function_results: List[Dict[str, Any]] = []
    binary_context_results: List[Dict[str, Any]] = []
    verification_results: List[Dict[str, Any]] = []

    total_modified_all = 0
    total_modified_filtered = 0
    total_excluded_functions = 0
    flagged_filtered = 0
    safe_filtered = 0
    failed_filtered = 0
    skipped_filtered = 0

    sum_llm_input_tokens = 0
    sum_llm_output_tokens = 0
    sum_llm_total_tokens = 0
    callee_augmented_count = 0
    binary_context_run_count = 0
    binary_context_input_tokens = 0
    binary_context_output_tokens = 0
    binary_context_total_tokens = 0
    verification_ran_count = 0
    verification_flagged_functions = 0
    verification_cleared_functions = 0
    verification_failed_functions = 0
    verification_input_tokens = 0
    verification_output_tokens = 0
    verification_total_tokens = 0

    if not file_pairs:
        report_lines.append("No file pairs or modifications were reported by drift.")
        logger.info("No file pairs or modifications were reported by drift.")
    else:
        report_lines.append(f"Found {len(file_pairs)} file pair(s).\n")

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
        total_excluded_functions += len(excluded_mods)

        report_lines.append(f"## File Pair {fp_idx}")
        report_lines.append(f"- target_oid:   {target_oid}")
        report_lines.append(f"- baseline_oid: {baseline_oid}")
        report_lines.append(f"- Triage candidate functions (filtered): {len(filtered_mods)}")
        report_lines.append(f"- added functions: {len(added_funcs)}")
        if excluded_mods:
            try:
                report_lines.append(f"- modified functions (excluded by filter): {len(excluded_mods)}")
            except Exception:
                report_lines.append("- modified functions (excluded by filter): <unknown>")
        report_lines.append("")

        # Under gt_only, triage only the ground-truth candidate(s); otherwise the whole
        # filtered set. filtered_mods stays intact above so the filter counts are unchanged.
        if gt_only:
            triage_mods = [
                m for m in filtered_mods
                if gt_only_norm
                and ground_truth.gt_row_matches_any(
                    {
                        "target_addr": ensure_decimal_str(m.get("target_func_addr")),
                        "target_oid": target_oid,
                    },
                    gt_only_norm,
                )
            ]
            report_lines.append(
                f"- gt_only: triaging {len(triage_mods)} of {len(filtered_mods)} filtered function(s)"
            )
            report_lines.append("")
        else:
            triage_mods = filtered_mods

        # Build the CFG and BinDiff artifacts the Verification tools sit on before any agent
        # starts, so a cold miss costs wall clock here instead of eating a run budget.
        prewarm_summary = prewarm_filepair_artifacts(
            baseline_oid=baseline_oid,
            target_oid=target_oid,
            label=f"{target_name} fp{fp_idx}/{len(file_pairs)}",
        )
        filepair_dir = os.path.join(outdir, f"filepair_{fp_idx:02d}")
        os.makedirs(filepair_dir, exist_ok=True)
        write_json(os.path.join(filepair_dir, "prewarm.json"), prewarm_summary)
        report_lines.append(
            f"- prewarm: {prewarm_summary['warmed']} artifact(s) in "
            f"{prewarm_summary['elapsed_s']:.1f}s"
            + (f", {prewarm_summary['failed']} failed" if prewarm_summary["failed"] else "")
        )
        report_lines.append("")

        added_callee_index: Optional[AddedCalleeIndex] = None
        if include_added_callees and added_funcs and triage_mods:
            added_func_decomp = fetch_added_func_decomps(target_oid, added_funcs)
            save_added_function_artifacts(
                target_oid=target_oid, added_functions=added_funcs, fp_idx=fp_idx,
                outdir=outdir, decomp_map=added_func_decomp,
            )
            # Built once here: the call map covers the whole binary and every candidate in
            # this file pair walks the same added-only edges.
            added_callee_index = build_added_callee_index(target_oid, added_func_decomp)

        fp_label = f"{target_name} fp{fp_idx}/{len(file_pairs)}"

        function_results = _run_function_pairs(
            triage_mods,
            baseline_oid=baseline_oid, target_oid=target_oid,
            fp_idx=fp_idx, fp_total=len(file_pairs),
            outdir=outdir, opts=opts, runtime=runtime, triage_fingerprint=triage_fingerprint,
            added_callee_index=added_callee_index,
            label=fp_label,
        )

        filepair_verification_results: List[Dict[str, Any]] = []
        binary_context_result: Optional[Dict[str, Any]] = None
        for func_idx, modified, result in function_results:
            baseline_addr = ensure_decimal_str(modified.get("baseline_func_addr"))
            target_addr = ensure_decimal_str(modified.get("target_func_addr"))
            _llm_in = int(result.get("llm_input_tokens") or 0)
            _llm_out = int(result.get("llm_output_tokens") or 0)
            _llm_tot = int(result.get("llm_total_tokens") or 0)
            sum_llm_input_tokens += _llm_in
            sum_llm_output_tokens += _llm_out
            sum_llm_total_tokens += _llm_tot

            triage_label = _coerce_result_label(result.get("label"), result.get("failure_reason"))
            triage_flagged = bool(triage_label == "not_safe")
            callee_augmented = bool(result.get("callee_augmented"))
            if callee_augmented:
                callee_augmented_count += 1

            per_function_results.append({
                "filepair_index": fp_idx,
                "function_index": func_idx,
                "baseline_oid": baseline_oid,
                "target_oid": target_oid,
                "baseline_addr": baseline_addr,
                "target_addr": target_addr,
                "triage_label": triage_label,
                "triage_flagged": triage_flagged,
                "diff_elapsed_s": float(result.get("diff_elapsed_s") or 0.0),
                "llm_elapsed_s": float(result.get("llm_elapsed_s") or 0.0),
                "llm_input_tokens": _llm_in,
                "llm_output_tokens": _llm_out,
                "llm_total_tokens": _llm_tot,
                "triage_ran": bool(result.get("triage_ran")),
                "failure_reason": result.get("failure_reason"),
                "failure_detail": result.get("failure_detail", ""),
                "callee_augmented": callee_augmented,
            })
            if triage_flagged:
                flagged_filtered += 1
                triage_index.append({
                    "filepair_index": fp_idx,
                    "function_index": func_idx,
                    "baseline_addr": baseline_addr,
                    "target_addr": target_addr,
                    "label": triage_label,
                    "verdict": result.get("verdict"),
                    "dir": result.get("func_dir"),
                    "baseline_oid": baseline_oid,
                    "target_oid": target_oid,
                })
            elif triage_label == "failed":
                failed_filtered += 1
            elif triage_label == "skipped":
                skipped_filtered += 1
            else:
                safe_filtered += 1

            # Verification escalation. Candidates Triage retained go on to a binary-wide
            # investigation: flagged ones to confirm, and Triage failures because the
            # fail-closed policy retains those as alert burden, so Verification is the only
            # place they can be cleared. Triage writes final.md only when it decides
            # not_safe, so a failure escalates with the diff alone.
            row = per_function_results[-1]
            escalate = runtime is not None and triage_label in {"not_safe", "failed"}
            row["verification_ran"] = escalate
            if not escalate:
                row["verification_label"] = ""
                _set_pipeline_outcome(row, triage_label)
                continue

            if binary_context_result is None:
                # Cached against the baseline only, since the report describes just that
                # binary. Every target compared against the same baseline reuses it.
                binary_context_cache_key = cache_keys.binary_context_cache_key(
                    baseline_oid, binary_context_fingerprint
                )
                binary_context_cache_opts = stage_cache_opts(
                    "binary_context_result", binary_context_fingerprint
                )
                binary_context_result = load_cached_stage_result(
                    baseline_oid, binary_context_cache_opts, binary_context_cache_key
                )
                binary_context_dir = os.path.join(outdir, f"filepair_{fp_idx:02d}", "binary_context")
                if binary_context_result is None:
                    binary_context_result = run_binary_context_analysis(
                        runtime=runtime,
                        fp_idx=fp_idx,
                        baseline_oid=baseline_oid,
                        target_oid=target_oid,
                        outdir=outdir,
                    )
                    # Only a complete report is cacheable. A timeout or a salvaged partial
                    # says nothing about the binary, and since the key is the baseline
                    # alone one such run would otherwise deny context to every pair sharing
                    # that baseline, for every later run at this fingerprint.
                    if _coerce_str(binary_context_result.get("status")) == "complete":
                        store_cached_stage_result(
                            baseline_oid,
                            binary_context_cache_opts,
                            binary_context_cache_key,
                            binary_context_result,
                        )
                    else:
                        logger.warning(
                            "%s: binary context for baseline %s not cached (status=%s, reason=%s)",
                            fp_label,
                            baseline_oid,
                            _coerce_str(binary_context_result.get("status")) or "failed",
                            _coerce_str(binary_context_result.get("failure_reason")) or "unknown",
                        )
                else:
                    # The cached record was written for whichever pair ran it first, so
                    # re-stamp the fields that belong to this comparison before the
                    # artifacts land in this pair's directory.
                    binary_context_result = dict(binary_context_result)
                    binary_context_result["target_oid"] = _coerce_str(target_oid)
                    binary_context_result["filepair_index"] = fp_idx
                    binary_context_result["outdir"] = binary_context_dir
                    restore_cached_binary_context_artifacts(
                        binary_context_dir,
                        binary_context_result,
                    )
                binary_context_results.append(binary_context_result)
                binary_context_run_count += 1
                binary_context_input_tokens += int(
                    binary_context_result.get("llm_input_tokens") or 0
                )
                binary_context_output_tokens += int(
                    binary_context_result.get("llm_output_tokens") or 0
                )
                binary_context_total_tokens += int(
                    binary_context_result.get("llm_total_tokens") or 0
                )
                report_lines.append(
                    f"- Binary context: {_coerce_str(binary_context_result.get('status')) or 'failed'}"
                )

            triage_dir = os.path.join(result.get("func_dir") or "", "triage")
            final_md_path = os.path.join(triage_dir, "final.md")
            local_report = {
                "function_index": func_idx,
                "func_dir": result.get("func_dir"),
                "baseline_addr": baseline_addr,
                "target_addr": target_addr,
                "label": triage_label,
                "final_md": _coerce_str(result.get("triage_final_md")) or _read_text_file(final_md_path),
                "final_md_path": final_md_path,
                "diff_path": os.path.join(triage_dir, "diff.txt"),
                "diff_text": _coerce_str(result.get("triage_diff_text")),
            }
            verification_cache_key = cache_keys.verification_result_cache_key(
                target_oid,
                baseline_oid,
                baseline_addr,
                target_addr,
                verification_fingerprint,
                cache_keys.verification_inputs_digest(
                    _coerce_str(local_report.get("final_md")),
                    _coerce_str((binary_context_result or {}).get("binary_context_md")),
                ),
            )
            verification_cache_opts = stage_cache_opts("verification_result", verification_fingerprint)
            verification_result = load_cached_stage_result(target_oid, verification_cache_opts, verification_cache_key)
            if verification_result is None:
                # Verification is the long pole, minutes per investigation against the
                # whole binary. Log each one starting, or a running comparison looks hung.
                logger.info(
                    "%s: verification %d starting (function %d, triage=%s)",
                    fp_label, verification_ran_count + 1, func_idx, triage_label,
                )
                verify_t0 = time.perf_counter()
                verification_result = run_verification(
                    runtime=runtime,
                    fp_idx=fp_idx,
                    baseline_oid=baseline_oid,
                    target_oid=target_oid,
                    local_report=local_report,
                    binary_context=binary_context_result,
                )
                store_cached_stage_result(target_oid, verification_cache_opts, verification_cache_key, verification_result)
                logger.info(
                    "%s: verification %d done in %.1fm -> %s%s",
                    fp_label, verification_ran_count + 1,
                    (time.perf_counter() - verify_t0) / 60.0,
                    _coerce_str(verification_result.get("label")) or "failed",
                    f" ({_coerce_str(verification_result.get('failure_reason'))})"
                    if verification_result.get("failure_reason") else "",
                )
            else:
                restore_cached_verification_artifacts(
                    os.path.join(result.get("func_dir") or "", "verification"),
                    verification_result,
                )
            filepair_verification_results.append(verification_result)
            verification_results.append(verification_result)
            verification_ran_count += 1
            verification_input_tokens += int(verification_result.get("llm_input_tokens") or 0)
            verification_output_tokens += int(verification_result.get("llm_output_tokens") or 0)
            verification_total_tokens += int(verification_result.get("llm_total_tokens") or 0)

            # Verification is authoritative over the candidates it reaches: it can clear a
            # Triage flag but never raise a new one. A Verification failure is not a verdict,
            # so the candidate keeps its Triage label and stays retained.
            verification_label = _coerce_str(verification_result.get("label"))
            if verification_label == "not_safe":
                verification_flagged_functions += 1
                pipeline_label = "not_safe"
            elif verification_label == "safe":
                verification_cleared_functions += 1
                pipeline_label = "safe"
            else:
                verification_failed_functions += 1
                pipeline_label = triage_label
            row["verification_label"] = verification_label
            row["binary_context_status"] = (
                _coerce_str(binary_context_result.get("status")) if binary_context_result else ""
            )
            row["verification_failure_reason"] = verification_result.get("failure_reason")
            row["verification_llm_elapsed_s"] = float(verification_result.get("llm_elapsed_s") or 0.0)
            row["verification_llm_input_tokens"] = int(verification_result.get("llm_input_tokens") or 0)
            row["verification_llm_output_tokens"] = int(verification_result.get("llm_output_tokens") or 0)
            row["verification_llm_total_tokens"] = int(verification_result.get("llm_total_tokens") or 0)
            _set_pipeline_outcome(row, pipeline_label)

        if filepair_verification_results:
            report_lines.append(f"- Verification investigations: {len(filepair_verification_results)}")
            for verification_result in filepair_verification_results:
                fn = int(verification_result.get("function_index") or 0)
                report_lines.append(
                    f"  - function {fn:02d}: {_coerce_str(verification_result.get('label')) or 'failed'}"
                    f" - {_coerce_str(verification_result.get('summary'))}"
                )
            report_lines.append("")

    elapsed_s = time.perf_counter() - total_t0

    gt = opts["_ground_truth"] if "_ground_truth" in opts else ground_truth.load_ground_truth_file(opts.get("ground_truth"))
    gt_norm = ground_truth.get_ground_truth_for_target(
        gt or {},
        target_name,
        pair_dir=outdir,
        target_oid=target,
    )

    gt_target_count = 0
    gt_retained = 0
    # Ground-truth outcomes as the tool reports them, after both stages.
    hit_count = 0
    dismissed_count = 0
    failed_gt_count = 0
    # The same outcomes scored on Triage's label alone, kept for the per-stage file so a
    # two-stage run stays comparable to a single-stage one.
    triage_hit_count = 0
    triage_dismissed_count = 0
    triage_failed_count = 0

    def _outcome(label: str, flagged: bool) -> str:
        if flagged:
            return "hit"
        return "failed" if label in {"failed", "skipped"} else "dismissed"

    if gt_norm:
        gt_target_count = len(gt_norm.get("targets", []) or [])
        for row in per_function_results:
            gt_match = ground_truth.gt_row_matches_any(row, gt_norm)
            row["gt_match"] = gt_match
            if not gt_match:
                continue
            gt_retained += 1
            # The tool's outcome: the label the candidate carries once both stages are done.
            outcome = _outcome(
                _coerce_str(row.get("pipeline_label")), bool(row.get("pipeline_flagged"))
            )
            row["gt_outcome"] = outcome
            hit_count += outcome == "hit"
            dismissed_count += outcome == "dismissed"
            failed_gt_count += outcome == "failed"
            # Triage's own outcome, for the per-stage breakdown.
            triage_outcome = _outcome(
                _coerce_str(row.get("triage_label")), bool(row.get("triage_flagged"))
            )
            row["gt_outcome_triage"] = triage_outcome
            triage_hit_count += triage_outcome == "hit"
            triage_dismissed_count += triage_outcome == "dismissed"
            triage_failed_count += triage_outcome == "failed"
    else:
        for row in per_function_results:
            row["gt_match"] = False

    # What the analyst is left holding once the tool is done.
    final_flagged_functions = sum(1 for row in per_function_results if row.get("pipeline_flagged"))
    # Fail-closed burden: a candidate no stage could clear is still retained.
    final_failed_functions = sum(
        1 for row in per_function_results if _coerce_str(row.get("pipeline_label")) == "failed"
    )
    final_flagged_files = len(
        {row.get("filepair_index") for row in per_function_results if row.get("pipeline_flagged")}
    )
    verification_with_report = sum(1 for r in verification_results if r.get("had_triage_report"))

    total_input_tokens = sum_llm_input_tokens + binary_context_input_tokens + verification_input_tokens
    total_output_tokens = sum_llm_output_tokens + binary_context_output_tokens + verification_output_tokens
    total_tokens = sum_llm_total_tokens + binary_context_total_tokens + verification_total_tokens

    # The tool's own results. Every count here describes what the analyst is handed once
    # both stages are done -- no stage appears in this file. Per-stage detail, including
    # how each stage scored on its own, lives in stage_metrics.json.
    stats: ComparisonStats = {
        "target": target,
        "baseline": baseline,
        "target_name": target_name,
        "baseline_name": baseline_name,
        "diff_mode": diff_mode,
        "filter_mode": filter_mode,
        # Scope: what the update changed and how much of it was reviewed.
        "modified_files": len(file_pairs),
        "modified_functions": total_modified_all,
        "filtered_functions": total_modified_filtered,
        "excluded_functions": total_excluded_functions,
        "binary_context_runs": binary_context_run_count,
        "investigated_functions": verification_ran_count,
        "callee_augmented_count": callee_augmented_count,
        # Result: the alert burden left on the analyst.
        "flagged_files": final_flagged_files,
        "flagged_functions": final_flagged_functions,
        "failed_functions": final_failed_functions,
        # Result against ground truth.
        "gt_sample_key": gt_norm.get("sample_key") if gt_norm else None,
        "gt_target_count": gt_target_count,
        "gt_retained": gt_retained,
        "hit": hit_count,
        "dismissed": dismissed_count,
        "failed": failed_gt_count,
        # Cost, averaged over the candidates the tool screened.
        "input_tokens": total_input_tokens,
        "output_tokens": total_output_tokens,
        "total_tokens": total_tokens,
        "avg_input_tokens": (
            total_input_tokens / float(total_modified_filtered)
        ) if total_modified_filtered else 0.0,
        "avg_output_tokens": (
            total_output_tokens / float(total_modified_filtered)
        ) if total_modified_filtered else 0.0,
        "avg_total_tokens": (
            total_tokens / float(total_modified_filtered)
        ) if total_modified_filtered else 0.0,
    }

    # Per-stage breakdown. Triage's counts are what a single-stage run of this
    # configuration would have reported, so the two are directly comparable.
    stage_metrics: Dict[str, Any] = {
        "triage": {
            "reviewed_functions": len(per_function_results),
            "flagged_functions": flagged_filtered,
            "dismissed_functions": safe_filtered,
            "failed_functions": failed_filtered,
            "skipped_functions": skipped_filtered,
            "hit": triage_hit_count,
            "dismissed": triage_dismissed_count,
            "failed": triage_failed_count,
            "input_tokens": sum_llm_input_tokens,
            "output_tokens": sum_llm_output_tokens,
            "total_tokens": sum_llm_total_tokens,
            "avg_total_tokens_per_function": (
                sum_llm_total_tokens / float(total_modified_filtered)
            ) if total_modified_filtered else 0.0,
        },
        "verification": {
            "binary_context_runs": binary_context_run_count,
            "binary_context_input_tokens": binary_context_input_tokens,
            "binary_context_output_tokens": binary_context_output_tokens,
            "binary_context_total_tokens": binary_context_total_tokens,
            "investigations": verification_ran_count,
            "with_report": verification_with_report,
            "without_report": verification_ran_count - verification_with_report,
            "flagged_functions": verification_flagged_functions,
            "cleared_functions": verification_cleared_functions,
            "failed_functions": verification_failed_functions,
            "input_tokens": verification_input_tokens,
            "output_tokens": verification_output_tokens,
            "total_tokens": verification_total_tokens,
            "avg_total_tokens_per_investigation": (
                verification_total_tokens / float(verification_ran_count)
            ) if verification_ran_count else 0.0,
        },
    }

    write_comparison_outputs(
        outdir=outdir,
        per_function_results=per_function_results,
        verification_results=verification_results,
        stage_metrics=stage_metrics,
        stats=stats,
    )

    return build_analyzer_result(
        target=target,
        baseline=baseline,
        stats=stats,
        stage_metrics=stage_metrics,
        per_function_results=per_function_results,
        verification_results=verification_results,
        file_pairs=file_pairs,
    )
