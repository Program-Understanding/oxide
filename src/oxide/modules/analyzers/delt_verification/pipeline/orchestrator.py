import logging
import os
import re
import time
from typing import Any, Dict, List, Optional, Tuple

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
    restore_cached_bounded_artifacts,
    restore_cached_unbounded_artifacts,
)
from oxide.modules.analyzers.delt_verification.pipeline.cache.store import (
    is_cacheable,
    load_cached_stage_result,
    stage_cache_opts,
    store_cached_stage_result,
)
from oxide.modules.analyzers.delt_verification.pipeline.phases.bounded import run_bounded
from oxide.modules.analyzers.delt_verification.pipeline.phases.unbounded import (
    run_unbounded,
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
    read_json,
    write_json,
    write_text,
    read_text,
)

logger = logging.getLogger(NAME)


_TOOL_CALL_RE = re.compile(r"\[agent\] tool args: (\w+)\(")


def _count_tool_calls(trace_path: str) -> Optional[Dict[str, Any]]:
    if not trace_path or not os.path.exists(trace_path):
        return None
    counts: Dict[str, int] = {}
    with open(trace_path, "r", encoding="utf-8", errors="replace") as handle:
        for match in _TOOL_CALL_RE.finditer(handle.read()):
            counts[match.group(1)] = counts.get(match.group(1), 0) + 1
    return {"total": sum(counts.values()), "by_tool": dict(sorted(counts.items()))}


def _write_tool_calls(json_path: str, tool_calls: Dict[str, Any]) -> None:
    record = read_json(json_path) if os.path.exists(json_path) else {}
    if not isinstance(record, dict):
        record = {}
    record["tool_calls"] = tool_calls
    write_json(json_path, record)


def _with_tool_calls(
    cached: Optional[Dict[str, Any]],
    trace_path: str,
    target_oid: str,
    cache_opts: Dict[str, Any],
    cache_key: str,
) -> Optional[Dict[str, Any]]:
    if cached is None or "tool_calls" in cached:
        return cached
    counts = _count_tool_calls(trace_path)
    if counts is None:
        return None
    cached = dict(cached, tool_calls=counts)
    store_cached_stage_result(target_oid, cache_opts, cache_key, cached)
    return cached


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
            "observation": "one side of the decompilation was empty. Bounded skipped and recorded as failed.",
            "final_why": "One side of the decompilation was empty, so the system could not compute a two-sided function diff. The function was recorded as failed because bounded did not run, not because the agent identified a trigger.",
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


def write_diff_artifacts(bounded_dir: str, unified: str, diff_meta: Dict[str, Any]) -> None:
    write_text(f"{bounded_dir}/diff.txt", unified or "")
    write_json(f"{bounded_dir}/diff_meta.json", diff_meta or {})


def write_agent_inputs(bounded_dir: str, unified: str, callee_texts: Dict[str, str]) -> None:
    """Mirror the exact files the bounded agent would see under /inputs/ to
    bounded_dir/agent_inputs/, so a dry run produces the full evidence set the agent
    receives without running it. Layout matches agent_runtime.build_agent_payload:
    diff.txt plus one added_functions/<addr>.c per reachable added callee."""
    inputs_dir = os.path.join(bounded_dir, "agent_inputs")
    os.makedirs(inputs_dir, exist_ok=True)
    write_text(os.path.join(inputs_dir, "diff.txt"), ascii_sanitize(unified or ""))
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
        either agrees. What bounded decided before any escalation stays available
        separately as bounded_label/bounded_flagged.
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
    bounded_fingerprint: str,
    added_callee_index: Optional[AddedCalleeIndex] = None,
) -> AnalyzeFunctionResult:
    func_dir = _make_function_dir(outdir, fp_idx, func_idx, baddr, taddr)
    bounded_dir = os.path.join(func_dir, "bounded")
    diff_raw = _resolve_bool_override(opts, "raw", "_diff_raw")
    bounded_cache_key = cache_keys.bounded_result_cache_key(
        target_oid, baseline_oid, baddr, taddr, bounded_fingerprint
    )
    bounded_cache_opts = stage_cache_opts("bounded_result", bounded_fingerprint)

    os.makedirs(func_dir, exist_ok=True)
    os.makedirs(bounded_dir, exist_ok=True)
    notes_path = os.path.join(bounded_dir, "notes.json")
    analysis_path = os.path.join(bounded_dir, "analysis.json")
    trace_path = os.path.join(bounded_dir, "agent_trace.log")

    def _write_analysis(
        *,
        label: str,
        why: str,
        bounded_ran: bool,
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
        callee_texts: Optional[Dict[str, str]] = None,
    ) -> Dict[str, Any]:
        label = _coerce_result_label(label, failure_reason)
        flagged = label == "not_safe"
        verdict_label = "needs further inspection" if flagged else label
        verdict = f"Label: {verdict_label} - {why or 'model provided no reason'}"

        if final_md.strip():
            write_text(os.path.join(bounded_dir, "final.md"), final_md)
            notes["artifacts"].append({"kind": "agent_final", "path": "bounded/final.md"})
        if os.path.exists(trace_path) and os.path.getsize(trace_path) > 0:
            notes["artifacts"].append({"kind": "agent_trace", "path": "bounded/agent_trace.log"})

        write_json(notes_path, notes)
        write_json(
            analysis_path,
            {
                "label": label,
                "why": why,
                "flagged": flagged,
                "verdict": verdict,
                "bounded_ran": bounded_ran,
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
        write_text(os.path.join(bounded_dir, "verdict.txt"), verdict)
        return {
            "label": label,
            "why": why,
            "flagged": flagged,
            "verdict": verdict,
            "func_dir": func_dir,
            "bounded_ran": bounded_ran,
            "failure_reason": failure_reason,
            "failure_detail": failure_detail,
            "diff_elapsed_s": diff_elapsed_s,
            "llm_elapsed_s": llm_elapsed_s,
            "llm_input_tokens": llm_input_tokens,
            "llm_output_tokens": llm_output_tokens,
            "llm_total_tokens": llm_total_tokens,
            "callee_augmented": callee_augmented,
            "bounded_final_md": final_md,
            "bounded_diff_text": diff_text,
            "bounded_diff_meta": diff_meta or {},
            "callee_texts": callee_texts or {},
        }

    skip_bounded = bool(opts.get("skip_bounded"))
    cached_bounded = (
        None if skip_bounded
        else load_cached_stage_result(target_oid, bounded_cache_opts, bounded_cache_key)
    )
    cached_bounded = _with_tool_calls(
        cached_bounded, trace_path, target_oid, bounded_cache_opts, bounded_cache_key
    )
    if cached_bounded is not None:
        restore_cached_bounded_artifacts(bounded_dir, cached_bounded)
        # The cached record holds the func_dir of whichever run first produced it. Later
        # stages build their output paths from this field, so a replay under a different
        # output root has to be re-stamped with its own directory or it writes its
        # artifacts back over the run that populated the cache.
        cached_bounded = dict(cached_bounded, func_dir=func_dir)
        if not os.path.exists(analysis_path):
            write_json(analysis_path, {
                "label": cached_bounded.get("label"),
                "why": cached_bounded.get("why"),
                "flagged": cached_bounded.get("flagged"),
                "verdict": cached_bounded.get("verdict"),
                "bounded_ran": cached_bounded.get("bounded_ran"),
                "failure_reason": cached_bounded.get("failure_reason"),
                "failure_detail": cached_bounded.get("failure_detail"),
                "callee_augmented": cached_bounded.get("callee_augmented"),
                "cached": True,
                "cost": {
                    "llm_input_tokens": cached_bounded.get("llm_input_tokens"),
                    "llm_output_tokens": cached_bounded.get("llm_output_tokens"),
                    "llm_total_tokens": cached_bounded.get("llm_total_tokens"),
                },
            })
        _write_tool_calls(analysis_path, cached_bounded.get("tool_calls") or {})
        return cached_bounded

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
            write_diff_artifacts(bounded_dir, diff_info["unified"], diff_info["artifact_meta"])
            notes["artifacts"].append({"kind": "diff_meta", "path": "bounded/diff_meta.json"})
            return diff_info, diff_elapsed_s

        diff_info, diff_elapsed_s = _fetch_and_write_diff()

        if opts.get("no_bounded"):
            # Dry run: produce everything the bounded agent would receive (the unified diff
            # plus the reachable added-callee decomps) on disk, but don't run the agent.
            unified = diff_info.get("unified") or ""
            callee_texts: Dict[str, str] = {}
            if unified.strip() and not diff_info["tool_error"]:
                callee_texts = callee_added_funcs(taddr, added_callee_index)
            write_agent_inputs(bounded_dir, unified, callee_texts)
            return _write_analysis(
                label="skipped", why="Dry run: bounded inputs produced, agent not run.", bounded_ran=False,
                failure_reason="dry_run", failure_detail="", diff_elapsed_s=diff_elapsed_s,
                llm_elapsed_s=0.0, llm_input_tokens=0, llm_output_tokens=0, llm_total_tokens=0, notes=notes,
                callee_augmented=bool(callee_texts), diff_text=unified,
                diff_meta=diff_info.get("artifact_meta") or {},
                callee_texts=callee_texts,
            )

        bounded_ran = False
        failure_reason: Optional[str] = None

        if diff_info["tool_error"]:
            notes["observations"].append(f"diff tool failed: {diff_info.get('error')!r}")
            return _write_analysis(
                label="failed", why="Diff generation failed before bounded could run.", bounded_ran=False,
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
                label="failed", why=messages["final_why"], bounded_ran=False,
                failure_reason=failure_reason, failure_detail="", diff_elapsed_s=diff_elapsed_s,
                llm_elapsed_s=0.0, llm_input_tokens=0, llm_output_tokens=0, llm_total_tokens=0, notes=notes,
                diff_text=diff_info.get("unified") or "", diff_meta=diff_info.get("artifact_meta") or {},
            )

        unified = diff_info["unified"] or ""

        if skip_bounded and unified.strip():
            return _write_analysis(
                label="skipped", why="Bounded skipped: candidate escalated to unbounded without a bounded report.",
                bounded_ran=False, failure_reason=None, failure_detail="",
                diff_elapsed_s=diff_elapsed_s, llm_elapsed_s=0.0, llm_input_tokens=0,
                llm_output_tokens=0, llm_total_tokens=0, notes=notes,
                diff_text=unified, diff_meta=diff_info.get("artifact_meta") or {},
                callee_texts=callee_added_funcs(taddr, added_callee_index),
            )

        callee_texts: Dict[str, str] = {}
        if unified.strip():
            callee_texts = callee_added_funcs(taddr, added_callee_index)

        llm_elapsed_s = 0.0
        llm_input_tokens = 0
        llm_output_tokens = 0
        llm_total_tokens = 0

        if unified.strip():
            bounded_ran = True
            bounded = run_bounded(
                runtime,
                unified_diff=unified,
                notes=notes,
                callee_texts=callee_texts,
                trace_path=trace_path,
            )
            label = bounded.get("label", "failed")
            why = (bounded.get("why") or "").strip()
            failure_reason = bounded.get("failure_reason")
            failure_detail = (bounded.get("failure_detail") or "").strip()
            llm_elapsed_s = float(bounded.get("llm_elapsed_s") or 0.0)
            llm_input_tokens = int(bounded.get("llm_input_tokens") or 0)
            llm_output_tokens = int(bounded.get("llm_output_tokens") or 0)
            llm_total_tokens = int(bounded.get("llm_total_tokens") or 0)
        else:
            failure_reason = "empty_unified_diff"
            failure_detail = ""
            notes["observations"].append("empty unified diff; recorded as failed")
            label = "failed"
            why = "Bounded did not run because the unified diff was empty."
            bounded = {"final_md": ""}

        label = _coerce_result_label(label, failure_reason)
        if failure_detail and label == "failed":
            why = f"{why} Detail: {failure_detail}".strip()
        result = _write_analysis(
            label=label, why=why, bounded_ran=bounded_ran, failure_reason=failure_reason,
            failure_detail=failure_detail, diff_elapsed_s=diff_elapsed_s, llm_elapsed_s=llm_elapsed_s,
            llm_input_tokens=llm_input_tokens, llm_output_tokens=llm_output_tokens,
            llm_total_tokens=llm_total_tokens, notes=notes,
            final_md=_coerce_str(bounded.get("final_md")),
            callee_augmented=bool(callee_texts), diff_text=unified,
            diff_meta=diff_info.get("artifact_meta") or {},
            callee_texts=callee_texts,
        )
        if os.path.exists(trace_path):
            write_trace_view(trace_path, os.path.join(bounded_dir, "trace_view.txt"))
        result["tool_calls"] = _count_tool_calls(trace_path) or {"total": 0, "by_tool": {}}
        _write_tool_calls(analysis_path, result["tool_calls"])
        if is_cacheable(result):
            store_cached_stage_result(target_oid, bounded_cache_opts, bounded_cache_key, result)
        return result

    return _run_fresh()


def _run_function_pairs(
    filtered_mods: List[Dict[str, Any]],
    *,
    baseline_oid: Any,
    target_oid: Any,
    fp_idx: int,
    outdir: str,
    opts: Dict[str, Any],
    runtime: Any,
    bounded_fingerprint: str,
    added_callee_index: Optional[AddedCalleeIndex],
    label: str,
) -> List[Tuple[int, Dict[str, Any], Any]]:
    """Bounded every modified function in a file pair, returning results in function order.

    Sequential by design: one comparison owns one model endpoint. Concurrency is the
    caller's job, run one whole comparison per endpoint (see delt_verification_experiment),
    which parallelizes bounded, binary context, and unbounded rather than bounded alone.

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
            fp_idx=fp_idx, func_idx=func_idx,
            outdir=outdir, opts=opts, runtime=runtime, bounded_fingerprint=bounded_fingerprint,
            added_callee_index=added_callee_index,
        )
        ordered.append((func_idx, modified, result))
        if func_idx % step == 0 or func_idx == func_total:
            elapsed = time.perf_counter() - t0
            rate = func_idx / elapsed if elapsed > 0 else 0.0
            logger.info(
                "%s: bounded %d/%d (%.0f%%) elapsed %.1fm eta %.1fm",
                label, func_idx, func_total, 100.0 * func_idx / func_total,
                elapsed / 60.0,
                ((func_total - func_idx) / rate / 60.0) if rate > 0 else 0.0,
            )
    return ordered


def run_comparison(target: str, baseline: str, outdir: str, opts: Dict[str, Any]) -> Dict[str, Any]:
    opts = _normalize_run_opts(opts)
    os.makedirs(outdir, exist_ok=True)

    # Dry run (no_bounded): no model is needed, so skip building the Ollama runtime and run
    # single-threaded -- the per-function loop only fetches diffs and writes agent inputs.
    no_bounded = bool(opts.get("no_bounded"))
    runtime = None if no_bounded else get_or_build_runtime(opts)
    prompt_bundle = load_prompt_bundle(opts)
    bounded_fingerprint = cache_keys.bounded_opts_fingerprint(opts, prompt_bundle)
    unbounded_fingerprint = cache_keys.unbounded_opts_fingerprint(opts, prompt_bundle)
    include_added_callees = bool(opts.get("include_added_callees", True))
    skip_bounded = bool(opts.get("skip_bounded"))
    # Ablation: run bounded and escalate on its decision as usual, but withhold its report
    # from unbounded. Unbounded then starts from the same candidate and diff with no
    # claim to react to, which separates the report as evidence from the report as a
    # conclusion. Distinct from skip_bounded, where bounded never runs and every filtered
    # candidate is verified.
    no_bounded_report = bool(opts.get("no_bounded_report"))
    # Ablation: stop after bounded, so each candidate is decided from the prepared evidence
    # alone with no whole-binary follow-up. Bounded itself is unchanged, so a run at this
    # setting reuses the cached bounded labels of the full pipeline.
    skip_unbounded = bool(opts.get("skip_unbounded"))
    diff_raw_for_stats = _resolve_bool_override(opts, "raw", "_diff_raw")

    filter_val = normalize_filter_value(opts.get("filter"))
    diff_mode = _coerce_str(opts.get("diff_mode")) or ("raw" if diff_raw_for_stats else "processed")
    filter_mode = _display_filter_mode(filter_val)

    drift_json = build_drift_file_pairs(target, baseline, filter_val) or {}
    write_json(os.path.join(outdir, "drift_raw.json"), drift_json)

    file_pairs: List[Dict[str, Any]] = drift_json.get("file_pairs", []) or []

    target_name = str(target)
    baseline_name = str(baseline)

    try:
        target_name = api.get_colname_from_oid(target) or str(target)
    except Exception:
        target_name = str(target)

    try:
        baseline_name = api.get_colname_from_oid(baseline) or str(baseline)
    except Exception:
        baseline_name = str(baseline)


    # gt_only: restrict bounded to the ground-truth insertion function(s) so a
    # backdoor-recall check spends LLM budget only on the GT candidate. The full
    # filtered set is still counted/reported; only the boundedd subset shrinks.
    # Pairs with no ground truth (e.g. safe variants) bounded nothing under gt_only.
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

    per_function_results: List[Dict[str, Any]] = []
    unbounded_results: List[Dict[str, Any]] = []

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
    # Counted separately from the runs: a replay attaches a report without spending
    # tokens, so the two together explain why runs can exceed the token totals.
    unbounded_ran_count = 0
    unbounded_flagged_functions = 0
    unbounded_cleared_functions = 0
    unbounded_failed_functions = 0
    unbounded_input_tokens = 0
    unbounded_output_tokens = 0
    unbounded_total_tokens = 0

    if not file_pairs:
        logger.info("No file pairs or modifications were reported by drift.")

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


        # Under gt_only, bounded only the ground-truth candidate(s); otherwise the whole
        # filtered set. filtered_mods stays intact above so the filter counts are unchanged.
        if gt_only:
            bounded_mods = [
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
        else:
            bounded_mods = filtered_mods

        # Build the CFG and BinDiff artifacts the Unbounded tools sit on before any agent
        # starts, so a cold miss costs wall clock here instead of eating a run budget.
        prewarm_summary = prewarm_filepair_artifacts(
            baseline_oid=baseline_oid,
            target_oid=target_oid,
            label=f"{target_name} fp{fp_idx}/{len(file_pairs)}",
        )
        filepair_dir = os.path.join(outdir, f"filepair_{fp_idx:02d}")
        os.makedirs(filepair_dir, exist_ok=True)
        write_json(os.path.join(filepair_dir, "prewarm.json"), prewarm_summary)

        added_callee_index: Optional[AddedCalleeIndex] = None
        if include_added_callees and added_funcs and bounded_mods:
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
            bounded_mods,
            baseline_oid=baseline_oid, target_oid=target_oid,
            fp_idx=fp_idx,
            outdir=outdir, opts=opts, runtime=runtime, bounded_fingerprint=bounded_fingerprint,
            added_callee_index=added_callee_index,
            label=fp_label,
        )

        filepair_unbounded_results: List[Dict[str, Any]] = []
        for func_idx, modified, result in function_results:
            baseline_addr = ensure_decimal_str(modified.get("baseline_func_addr"))
            target_addr = ensure_decimal_str(modified.get("target_func_addr"))
            _llm_in = int(result.get("llm_input_tokens") or 0)
            _llm_out = int(result.get("llm_output_tokens") or 0)
            _llm_tot = int(result.get("llm_total_tokens") or 0)
            sum_llm_input_tokens += _llm_in
            sum_llm_output_tokens += _llm_out
            sum_llm_total_tokens += _llm_tot

            bounded_label = _coerce_result_label(result.get("label"), result.get("failure_reason"))
            bounded_flagged = bool(bounded_label == "not_safe")
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
                "bounded_label": bounded_label,
                "bounded_flagged": bounded_flagged,
                "diff_elapsed_s": float(result.get("diff_elapsed_s") or 0.0),
                "llm_elapsed_s": float(result.get("llm_elapsed_s") or 0.0),
                "llm_input_tokens": _llm_in,
                "llm_output_tokens": _llm_out,
                "llm_total_tokens": _llm_tot,
                "bounded_ran": bool(result.get("bounded_ran")),
                "failure_reason": result.get("failure_reason"),
                "failure_detail": result.get("failure_detail", ""),
                "callee_augmented": callee_augmented,
                "tool_calls": result.get("tool_calls") or {},
            })
            if bounded_flagged:
                flagged_filtered += 1
            elif bounded_label == "failed":
                failed_filtered += 1
            elif bounded_label == "skipped":
                skipped_filtered += 1
            else:
                safe_filtered += 1

            # Unbounded escalation. Candidates Bounded retained go on to a binary-wide
            # investigation: flagged ones to confirm, and Bounded failures because the
            # fail-closed policy retains those as alert burden, so Unbounded is the only
            # place they can be cleared. Bounded writes final.md only when it decides
            # not_safe, so a failure escalates with the diff alone.
            row = per_function_results[-1]
            escalate = runtime is not None and not skip_unbounded and (
                bounded_label in {"not_safe", "failed"}
                or (skip_bounded and not result.get("failure_reason"))
            )
            row["unbounded_ran"] = escalate
            if not escalate:
                row["unbounded_label"] = ""
                _set_pipeline_outcome(row, bounded_label)
                continue

            bounded_dir = os.path.join(result.get("func_dir") or "", "bounded")
            final_md_path = os.path.join(bounded_dir, "final.md")
            local_report = {
                "function_index": func_idx,
                "func_dir": result.get("func_dir"),
                "baseline_addr": baseline_addr,
                "target_addr": target_addr,
                "label": bounded_label,
                "final_md": (
                    "" if no_bounded_report
                    else _coerce_str(result.get("bounded_final_md")) or read_text(final_md_path)
                ),
                "final_md_path": final_md_path,
                "diff_path": os.path.join(bounded_dir, "diff.txt"),
                "diff_text": _coerce_str(result.get("bounded_diff_text")),
                "callee_texts": result.get("callee_texts") or {},
            }
            unbounded_cache_key = cache_keys.unbounded_result_cache_key(
                target_oid,
                baseline_oid,
                baseline_addr,
                target_addr,
                unbounded_fingerprint,
                cache_keys.unbounded_inputs_digest(
                    _coerce_str(local_report.get("final_md")),
                    local_report.get("callee_texts") or {},
                ),
            )
            unbounded_cache_opts = stage_cache_opts("unbounded_result", unbounded_fingerprint)
            unbounded_result = load_cached_stage_result(target_oid, unbounded_cache_opts, unbounded_cache_key)
            unbounded_result = _with_tool_calls(
                unbounded_result,
                os.path.join(result.get("func_dir") or "", "unbounded", "agent_trace.log"),
                target_oid, unbounded_cache_opts, unbounded_cache_key,
            )
            if unbounded_result is None:
                # Unbounded is the long pole, minutes per investigation against the
                # whole binary. Log each one starting, or a running comparison looks hung.
                logger.info(
                    "%s: unbounded %d starting (function %d, bounded=%s)",
                    fp_label, unbounded_ran_count + 1, func_idx, bounded_label,
                )
                verify_t0 = time.perf_counter()
                unbounded_result = run_unbounded(
                    runtime=runtime,
                    fp_idx=fp_idx,
                    baseline_oid=baseline_oid,
                    target_oid=target_oid,
                    local_report=local_report,
                )
                unbounded_outdir = _coerce_str(unbounded_result.get("outdir"))
                unbounded_result["tool_calls"] = _count_tool_calls(
                    os.path.join(unbounded_outdir, "agent_trace.log")
                ) or {"total": 0, "by_tool": {}}
                if unbounded_outdir:
                    _write_tool_calls(
                        os.path.join(unbounded_outdir, "result.json"), unbounded_result["tool_calls"]
                    )
                if is_cacheable(unbounded_result):
                    store_cached_stage_result(
                        target_oid, unbounded_cache_opts, unbounded_cache_key, unbounded_result
                    )
                logger.info(
                    "%s: unbounded %d done in %.1fm -> %s%s",
                    fp_label, unbounded_ran_count + 1,
                    (time.perf_counter() - verify_t0) / 60.0,
                    _coerce_str(unbounded_result.get("label")) or "failed",
                    f" ({_coerce_str(unbounded_result.get('failure_reason'))})"
                    if unbounded_result.get("failure_reason") else "",
                )
            else:
                unbounded_dir = os.path.join(result.get("func_dir") or "", "unbounded")
                unbounded_result = dict(unbounded_result)
                unbounded_result["filepair_index"] = fp_idx
                unbounded_result["function_index"] = func_idx
                unbounded_result["bounded_label"] = bounded_label
                unbounded_result["outdir"] = unbounded_dir
                if _coerce_str(unbounded_result.get("final_md")):
                    unbounded_result["final_md_path"] = os.path.join(unbounded_dir, "final.md")
                restore_cached_unbounded_artifacts(unbounded_dir, unbounded_result)
            filepair_unbounded_results.append(unbounded_result)
            unbounded_results.append(unbounded_result)
            unbounded_ran_count += 1
            unbounded_input_tokens += int(unbounded_result.get("llm_input_tokens") or 0)
            unbounded_output_tokens += int(unbounded_result.get("llm_output_tokens") or 0)
            unbounded_total_tokens += int(unbounded_result.get("llm_total_tokens") or 0)

            # The last stage to run owns the verdict. Unbounded is authoritative over the
            # candidates it reaches, including when it fails: inheriting the Bounded label
            # instead would record an unresolved investigation as a confirmed one, so a
            # failure would be invisible in the flagged counts and would silently earn
            # detection credit that no stage actually established. The candidate is still
            # retained under the fail-closed policy, because burden counts flagged plus
            # failed; only the attribution changes.
            unbounded_label = _coerce_str(unbounded_result.get("label"))
            if unbounded_label == "not_safe":
                unbounded_flagged_functions += 1
                pipeline_label = "not_safe"
            elif unbounded_label == "safe":
                unbounded_cleared_functions += 1
                pipeline_label = "safe"
            else:
                unbounded_failed_functions += 1
                pipeline_label = "failed"
            row["unbounded_label"] = unbounded_label
            row["unbounded_failure_reason"] = unbounded_result.get("failure_reason")
            row["unbounded_llm_elapsed_s"] = float(unbounded_result.get("llm_elapsed_s") or 0.0)
            row["unbounded_llm_input_tokens"] = int(unbounded_result.get("llm_input_tokens") or 0)
            row["unbounded_llm_output_tokens"] = int(unbounded_result.get("llm_output_tokens") or 0)
            row["unbounded_llm_total_tokens"] = int(unbounded_result.get("llm_total_tokens") or 0)
            row["unbounded_tool_calls"] = unbounded_result.get("tool_calls") or {}
            _set_pipeline_outcome(row, pipeline_label)


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
    # The same outcomes scored on Bounded's label alone, kept for the per-stage file so a
    # two-stage run stays comparable to a single-stage one.
    bounded_hit_count = 0
    bounded_dismissed_count = 0
    bounded_failed_count = 0

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
            # Bounded's own outcome, for the per-stage breakdown.
            bounded_outcome = _outcome(
                _coerce_str(row.get("bounded_label")), bool(row.get("bounded_flagged"))
            )
            row["gt_outcome_bounded"] = bounded_outcome
            bounded_hit_count += bounded_outcome == "hit"
            bounded_dismissed_count += bounded_outcome == "dismissed"
            bounded_failed_count += bounded_outcome == "failed"
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
    unbounded_with_report = sum(1 for r in unbounded_results if r.get("had_bounded_report"))

    total_input_tokens = sum_llm_input_tokens + unbounded_input_tokens
    total_output_tokens = sum_llm_output_tokens + unbounded_output_tokens
    total_tokens = sum_llm_total_tokens + unbounded_total_tokens

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
        "investigated_functions": unbounded_ran_count,
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

    # Per-stage breakdown. Bounded's counts are what a single-stage run of this
    # configuration would have reported, so the two are directly comparable.
    stage_metrics: Dict[str, Any] = {
        "bounded": {
            "reviewed_functions": len(per_function_results),
            "flagged_functions": flagged_filtered,
            "dismissed_functions": safe_filtered,
            "failed_functions": failed_filtered,
            "skipped_functions": skipped_filtered,
            "hit": bounded_hit_count,
            "dismissed": bounded_dismissed_count,
            "failed": bounded_failed_count,
            "input_tokens": sum_llm_input_tokens,
            "output_tokens": sum_llm_output_tokens,
            "total_tokens": sum_llm_total_tokens,
            "avg_total_tokens_per_function": (
                sum_llm_total_tokens / float(total_modified_filtered)
            ) if total_modified_filtered else 0.0,
        },
        "unbounded": {
            "investigations": unbounded_ran_count,
            "with_report": unbounded_with_report,
            "without_report": unbounded_ran_count - unbounded_with_report,
            "flagged_functions": unbounded_flagged_functions,
            "cleared_functions": unbounded_cleared_functions,
            "failed_functions": unbounded_failed_functions,
            "input_tokens": unbounded_input_tokens,
            "output_tokens": unbounded_output_tokens,
            "total_tokens": unbounded_total_tokens,
            "avg_total_tokens_per_investigation": (
                unbounded_total_tokens / float(unbounded_ran_count)
            ) if unbounded_ran_count else 0.0,
        },
    }

    write_comparison_outputs(
        outdir=outdir,
        per_function_results=per_function_results,
        unbounded_results=unbounded_results,
        stage_metrics=stage_metrics,
        stats=stats,
    )

    return build_analyzer_result(
        target=target,
        baseline=baseline,
        stats=stats,
        stage_metrics=stage_metrics,
        per_function_results=per_function_results,
        unbounded_results=unbounded_results,
        file_pairs=file_pairs,
    )
