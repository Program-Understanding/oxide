import logging
import os
import queue
import threading
import time
from typing import Any, Dict, List, Optional, Set, Tuple

from oxide.core import api, progress

from oxide.modules.analyzers.delt.config import NAME
from oxide.modules.analyzers.delt.pipeline.agent.triage import run_triage
from oxide.modules.analyzers.delt.pipeline.agent.telemetry.agent_trace import write_trace_view
from oxide.modules.analyzers.delt.pipeline.agent.endpoints import resolve_function_endpoints
from oxide.modules.analyzers.delt.pipeline.agent.runtime import build_worker_runtime, get_or_build_runtime
from oxide.modules.analyzers.delt.pipeline.types import AnalyzeFunctionResult, ComparisonStats
from oxide.modules.analyzers.delt.pipeline.utils import cache, ground_truth
from oxide.modules.analyzers.delt.pipeline.utils.callees import (
    callee_added_funcs,
    fetch_added_func_decomps,
    save_added_function_artifacts,
)
from oxide.modules.analyzers.delt.pipeline.utils.drift_adapter import build_drift_file_pairs
from oxide.modules.analyzers.delt.pipeline.utils.llm import load_prompt_bundle
from oxide.modules.analyzers.delt.pipeline.utils.text_utils import (
    _EMPTY_DECOMP_FAILURE_MESSAGES,
    _coerce_result_label,
    _coerce_str,
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
        callee_augmented: bool = False,
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
                "why": why,
                "flagged": flagged,
                "verdict": verdict,
                "triage_ran": triage_ran,
                "failure_reason": failure_reason,
                "failure_detail": failure_detail,
                "callee_augmented": callee_augmented,
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
            "callee_augmented": callee_augmented,
        }

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
            callee_augmented=bool(callee_texts),
        )
        if os.path.exists(trace_path):
            write_trace_view(trace_path, os.path.join(func_dir, "trace_view.txt"))
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
    fingerprint: str,
    added_func_decomp: Dict[str, str],
    function_workers: int,
    base_urls: List[str],
    prog: Any,
) -> List[Tuple[int, Dict[str, Any], Any]]:
    """Triage every modified function in a file pair, returning results in function order.

    Sequential when function_workers <= 1 (uses the shared runtime). Otherwise runs N
    long-lived worker threads, each owning its own runtime pinned to one endpoint, pulling
    functions from a shared queue. Aggregation stays on the caller in deterministic order.
    Ticks prog once per completed function so the progress bar advances in real time."""
    func_total = len(filtered_mods)

    def _compute(func_idx: int, modified: Dict[str, Any], rt: Any) -> Any:
        baseline_addr = ensure_decimal_str(modified.get("baseline_func_addr"))
        target_addr = ensure_decimal_str(modified.get("target_func_addr"))
        return analyze_function_pair(
            baseline_oid=baseline_oid, target_oid=target_oid, baddr=baseline_addr, taddr=target_addr,
            fp_idx=fp_idx, fp_total=fp_total, func_idx=func_idx, func_total=func_total,
            outdir=outdir, opts=opts, runtime=rt, fingerprint=fingerprint,
            added_func_decomp=added_func_decomp,
        )

    if function_workers <= 1 or func_total <= 1:
        ordered: List[Tuple[int, Dict[str, Any], Any]] = []
        for i, m in enumerate(filtered_mods, 1):
            result = _compute(i, m, runtime)
            ordered.append((i, m, result))
            prog.tick()
        return ordered

    n_workers = min(function_workers, func_total)
    endpoints: List[Optional[str]] = list(base_urls) if base_urls else [None] * n_workers
    work: "queue.Queue[Tuple[int, Dict[str, Any]]]" = queue.Queue()
    for i, m in enumerate(filtered_mods, 1):
        work.put((i, m))
    results: Dict[int, Tuple[int, Dict[str, Any], Any]] = {}
    results_lock = threading.Lock()

    def _worker(worker_idx: int) -> None:
        base_url = endpoints[worker_idx % len(endpoints)]
        worker_runtime = build_worker_runtime(opts, base_url)
        while True:
            try:
                func_idx, modified = work.get_nowait()
            except queue.Empty:
                return
            try:
                result: Any = _compute(func_idx, modified, worker_runtime)
            except Exception as exc:  # noqa: BLE001 — record as a function failure, don't kill the worker
                logger.exception("function %d/%d failed on %s", func_idx, func_total, base_url or "default")
                result = {"label": "failed", "failure_reason": "worker_exception", "failure_detail": repr(exc)}
            with results_lock:
                results[func_idx] = (func_idx, modified, result)
                prog.tick()
            work.task_done()

    threads = [threading.Thread(target=_worker, args=(w,), daemon=True) for w in range(n_workers)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()
    return [results[i] for i in sorted(results)]


def run_comparison(target: str, baseline: str, outdir: str, opts: Dict[str, Any]) -> Dict[str, Any]:
    opts = _normalize_run_opts(opts)
    os.makedirs(outdir, exist_ok=True)

    runtime = get_or_build_runtime(opts)
    fingerprint = cache.opts_fingerprint(opts, load_prompt_bundle(opts))
    include_added_callees = bool(opts.get("include_added_callees", True))
    diff_raw_for_stats = _resolve_bool_override(opts, "raw", "_diff_raw")

    # Per-function parallelism (prototype, behind function_workers). When > 1, functions
    # within each file pair are triaged concurrently by worker threads, each pinned to one
    # Ollama endpoint. Endpoints are provisioned lazily by the module (one server per GPU).
    function_workers = int(opts.get("function_workers") or 1)
    function_base_urls = resolve_function_endpoints(opts) if function_workers > 1 else []
    if function_workers > 1:
        logger.info(
            "per-function parallelism enabled: %d workers, %s",
            function_workers,
            f"{len(function_base_urls)} endpoint(s)" if function_base_urls else "shared endpoint",
        )

    filter_val = normalize_filter_value(opts.get("filter"))
    diff_mode = _coerce_str(opts.get("diff_mode")) or ("raw" if diff_raw_for_stats else "processed")
    filter_mode = _display_filter_mode(filter_val)
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

    triage_index: List[Dict[str, Any]] = []
    per_function_results: List[Dict[str, Any]] = []

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
        report_lines.append(f"- modified functions (filtered): {len(filtered_mods)}")
        report_lines.append(f"- added functions: {len(added_funcs)}")
        if excluded_mods:
            try:
                report_lines.append(f"- modified functions (excluded by filter): {len(excluded_mods)}")
            except Exception:
                report_lines.append("- modified functions (excluded by filter): <unknown>")
        report_lines.append("")

        added_func_decomp: Dict[str, str] = {}
        if include_added_callees and added_funcs:
            added_func_decomp = fetch_added_func_decomps(target_oid, added_funcs)
            save_added_function_artifacts(
                target_oid=target_oid, added_functions=added_funcs, fp_idx=fp_idx,
                outdir=outdir, decomp_map=added_func_decomp,
            )

        prog = progress.Progress(len(filtered_mods))

        function_results = _run_function_pairs(
            filtered_mods,
            baseline_oid=baseline_oid, target_oid=target_oid,
            fp_idx=fp_idx, fp_total=len(file_pairs),
            outdir=outdir, opts=opts, runtime=runtime, fingerprint=fingerprint,
            added_func_decomp=added_func_decomp,
            function_workers=function_workers, base_urls=function_base_urls,
            prog=prog,
        )

        for func_idx, modified, result in function_results:
            baseline_addr = ensure_decimal_str(modified.get("baseline_func_addr"))
            target_addr = ensure_decimal_str(modified.get("target_func_addr"))
            _llm_in = int(result.get("llm_input_tokens") or 0)
            _llm_out = int(result.get("llm_output_tokens") or 0)
            _llm_tot = int(result.get("llm_total_tokens") or 0)
            sum_llm_input_tokens += _llm_in
            sum_llm_output_tokens += _llm_out
            sum_llm_total_tokens += _llm_tot

            final_label = _coerce_result_label(result.get("label"), result.get("failure_reason"))
            flagged_final = bool(final_label == "not_safe")
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
                "final_label": final_label,
                "flagged_final": flagged_final,
                "dismissed_final": final_label == "safe",
                "failed_final": final_label == "failed",
                "skipped_final": final_label == "skipped",
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
                })
            elif final_label == "failed":
                failed_filtered += 1
            elif final_label == "skipped":
                skipped_filtered += 1
            else:
                safe_filtered += 1

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
    hit_count = 0
    dismissed_count = 0
    failed_gt_count = 0

    if gt_norm:
        gt_target_count = len(gt_norm.get("targets", []) or [])
        for row in per_function_results:
            gt_match = ground_truth.gt_row_matches_any(row, gt_norm)
            row["gt_match"] = gt_match
            if not gt_match:
                continue
            gt_retained += 1
            if row.get("flagged_final"):
                row["gt_outcome"] = "hit"
                hit_count += 1
            elif row.get("final_label") in {"failed", "skipped"}:
                row["gt_outcome"] = "failed"
                failed_gt_count += 1
            else:
                row["gt_outcome"] = "dismissed"
                dismissed_count += 1
    else:
        for row in per_function_results:
            row["gt_match"] = False

    stats: ComparisonStats = {
        "target": target,
        "baseline": baseline,
        "target_name": target_name,
        "baseline_name": baseline_name,
        "diff_mode": diff_mode,
        "filter_mode": filter_mode,
        "modified_files": len(file_pairs),
        "flagged_files": len({row.get("filepair_index") for row in triage_index}),
        "modified_functions": total_modified_all,
        "filtered_functions": total_modified_filtered,
        "excluded_functions": total_excluded_functions,
        "flagged_functions": flagged_filtered,
        "failed_functions": failed_filtered,
        "callee_augmented_count": callee_augmented_count,
        "gt_sample_key": gt_norm.get("sample_key") if gt_norm else None,
        "gt_target_count": gt_target_count,
        "gt_retained": gt_retained,
        "hit": hit_count,
        "dismissed": dismissed_count,
        "failed": failed_gt_count,
        "input_tokens": sum_llm_input_tokens,
        "output_tokens": sum_llm_output_tokens,
        "total_tokens": sum_llm_total_tokens,
        "avg_input_tokens": (sum_llm_input_tokens / float(total_modified_filtered)) if total_modified_filtered else 0.0,
        "avg_output_tokens": (sum_llm_output_tokens / float(total_modified_filtered)) if total_modified_filtered else 0.0,
        "avg_total_tokens": (sum_llm_total_tokens / float(total_modified_filtered)) if total_modified_filtered else 0.0,
    }

    write_text(os.path.join(outdir, "final_report.txt"), "\n".join(report_lines))
    write_json(os.path.join(outdir, "triage_index.json"), triage_index)
    write_json(os.path.join(outdir, "per_function_results.json"), per_function_results)
    write_json(os.path.join(outdir, "stats.json"), stats)

    return {
        "target": target,
        "baseline": baseline,
        "stats": stats,
        "triage_index": triage_index,
        "per_function_results": per_function_results,
        "file_pairs": file_pairs,
    }
