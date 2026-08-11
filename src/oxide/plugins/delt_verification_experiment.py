from __future__ import annotations

import json
import logging
import os
import queue
import re
import socket
import threading
import time
import urllib.request
from typing import Any, Dict, List, Optional, Set, Tuple

from oxide.core import oxide as oxide
from oxide.core.oxide import api

from oxide.modules.analyzers.delt_verification.pipeline.utils.drift_adapter import build_drift_file_pairs
from oxide.modules.analyzers.delt_verification.pipeline.utils.ground_truth import (
    get_ground_truth_for_target,
    gt_row_matches_any,
    load_ground_truth_file,
)
from oxide.modules.analyzers.delt_verification.pipeline.utils.text_utils import comparison_dir_name, ensure_decimal_str

NAME = "delt_verification_experiment"
logger = logging.getLogger(NAME)
logging.getLogger("httpx").setLevel(logging.WARNING)

FP_BINS: Tuple[Tuple[str, int, Optional[int]], ...] = (
    ("0", 0, 0),
    ("1", 1, 1),
    ("2-5", 2, 5),
    ("6-10", 6, 10),
    ("11-25", 11, 25),
    (">25", 26, None),
)

# Structural-filter census policies reported in the paper's Filter Coverage table
# (Table tab:filter-coverage). The AND policy is not reported, so it is not run.
FILTER_CENSUS_CONFIGS: Tuple[Tuple[str, Optional[str]], ...] = (
    ("filter_OR", "Call_OR_Control_Modified"),
    ("filter_NONE", None),
)


# Full two-stage DELT plus one config per ablated design element. Each config perturbs
# exactly one element away from the deployed configuration, so the paper's
# Delta = Full - Ablated stays attributable.
#
# Diff processing is not ablated here: it showed no detection or false-positive effect
# through the triage agent, so this module runs processed diffs throughout.
#
# Triage alone is not a config either. Every run records both the Triage label and the
# post-Verification pipeline label per candidate, so the single-stage and two-stage numbers
# both come out of one pass.
EXPERIMENT_CONFIGS: Tuple[Tuple[str, str, Optional[str], Dict[str, Any]], ...] = (
    ("delt_verification", "processed", "Call_OR_Control_Modified", {}),
    # ("no_added_callees", "processed", "Call_OR_Control_Modified", {"include_added_callees": False}),
    # ("no_filter", "processed", None, {}),
)


def _read_json(path: str) -> Any:
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


def _write_json(path: str, data: Any) -> None:
    with open(path, "w", encoding="utf-8") as handle:
        json.dump(data, handle, indent=2, ensure_ascii=False, default=str)


def _write_text(path: str, text: str) -> None:
    with open(path, "w", encoding="utf-8") as handle:
        handle.write(text)


def _read_series_file(path: str, sep: str = ",") -> List[Tuple[str, str]]:
    """Read a series file where each non-comment line is `coll_old, coll_new`.

    Returns a list of (cid_left, cid_right) tuples, resolving collection names to
    collection IDs. Copied from the `drift` plugin so this experiment has no
    dependency on it.
    """
    pairs: List[Tuple[str, str]] = []

    with open(path, "r", encoding="utf-8") as f:
        for raw_ln in f:
            ln = raw_ln.strip()
            if not ln or ln.startswith("#"):
                continue

            parts = [p.strip() for p in ln.split(sep)]
            if len(parts) != 2:
                raise ValueError(
                    f"Line {raw_ln!r} does not contain exactly two collections "
                    f"separated by {sep!r}"
                )

            left_name, right_name = parts
            cid_left = api.get_cid_from_name(left_name)
            cid_right = api.get_cid_from_name(right_name)
            if not cid_left:
                raise ValueError(
                    f"Unknown target collection {left_name!r} in {path}."
                )
            if not cid_right:
                raise ValueError(
                    f"Unknown baseline collection {right_name!r} in {path}."
                )
            pairs.append((cid_left, cid_right))

    return pairs


def _comparison_dir(target: str, baseline: str) -> str:
    return comparison_dir_name(str(target), str(baseline))


def _resolve_pairs(args: List[str], opts: Dict[str, Any]) -> List[Tuple[str, str]]:
    series_file = opts.get("entries")
    if series_file:
        return _read_series_file(series_file)
    if len(args) == 2:
        return [(args[0], args[1])]
    raise ValueError("Pass either [target, baseline] or --entries with at least one target,baseline pair per line.")


def _parse_models_file(path: str) -> List[Tuple[str, int]]:
    """Parse a models file. Each non-comment line is `model_tag [sample_workers]`
    (whitespace- or comma-separated); sample_workers defaults to 1."""
    specs: List[Tuple[str, int]] = []
    with open(path, "r", encoding="utf-8") as handle:
        for raw_line in handle:
            line = raw_line.split("#", 1)[0].strip()
            if not line:
                continue
            parts = line.replace(",", " ").split()
            model = parts[0]
            sample_workers = int(parts[1]) if len(parts) > 1 else 1
            if sample_workers < 1:
                raise ValueError(f"sample_workers must be >= 1 for model '{model}' (got {sample_workers}).")
            specs.append((model, sample_workers))
    if not specs:
        raise ValueError(f"Models file '{path}' contained no models.")
    return specs


def _model_slug(model: str) -> str:
    return re.sub(r"[^A-Za-z0-9._-]+", "_", str(model)).strip("_") or "model"


def _resolve_model_specs(opts: Dict[str, Any]) -> Tuple[List[Tuple[str, int]], bool, bool]:
    """Return (model_specs, nested, dry_run). Each spec is (model, sample_workers).
    `nested` is True when results should live under a per-model subdirectory (multi-model
    runs); False keeps the flat single-model layout. `dry_run` is True when no model was
    given: the pipeline then produces every triage input (unified diffs + added-callee
    context) without running the agent, for ground-truth authoring."""
    models_path = opts.get("models")
    if models_path:
        return _parse_models_file(models_path), True, False
    model = opts.get("model")
    if not model:
        # No model -> dry run: produce triage inputs only, no LLM.
        return [("dry_run", 1)], False, True
    sample_workers = int(opts.get("sample_workers") or 1)
    if sample_workers < 1:
        raise ValueError(f"--sample_workers must be >= 1 (got {sample_workers}).")
    return [(str(model), sample_workers)], False, False


def _run_one_comparison(target: str, baseline: str, outdir: str, opts: Dict[str, Any]) -> Dict[str, Any]:
    call_opts = dict(opts)
    call_opts["outdir"] = outdir
    return api.retrieve("delt_verification", [target, baseline], call_opts) or {}


def _sample_is_complete(sample_outdir: str) -> bool:
    return os.path.exists(os.path.join(sample_outdir, "stats.json"))


def _refresh_cached_stats_ground_truth(
    pair_dir: str,
    stats: Dict[str, Any],
    gt: Dict[str, Any],
    target_name: str,
    target_oid: Optional[str] = None,
) -> Dict[str, Any]:
    gt_norm = get_ground_truth_for_target(
        gt,
        target_name,
        pair_dir=pair_dir,
        target_oid=target_oid or stats.get("target"),
    )
    if not gt_norm:
        return stats

    per_function_path = os.path.join(pair_dir, "per_function_results.json")
    if not os.path.exists(per_function_path):
        logger.warning("Cannot refresh ground truth for %s: missing per_function_results.json", pair_dir)
        return stats

    per_function_results = _read_json(per_function_path)
    if not isinstance(per_function_results, list):
        logger.warning("Cannot refresh ground truth for %s: per_function_results.json is not a list", pair_dir)
        return stats

    gt_target_count = len(gt_norm.get("targets", []) or [])
    gt_retained = 0
    counts = {"hit": 0, "dismissed": 0, "failed": 0}
    triage_counts = {"hit": 0, "dismissed": 0, "failed": 0}

    def _outcome(label: Any, flagged: Any) -> str:
        if flagged:
            return "hit"
        return "failed" if label in {"failed", "skipped"} else "dismissed"

    for row in per_function_results:
        if not isinstance(row, dict):
            continue
        if not gt_row_matches_any(row, gt_norm):
            continue
        gt_retained += 1
        # Rows written before verification existed carry no pipeline label; fall back to
        # the triage label so a refreshed older run stays internally consistent.
        counts[
            _outcome(
                row.get("pipeline_label") or row.get("triage_label"),
                row.get("pipeline_flagged", row.get("triage_flagged")),
            )
        ] += 1
        triage_counts[_outcome(row.get("triage_label"), row.get("triage_flagged"))] += 1

    refreshed = dict(stats)
    refreshed.update(
        {
            "gt_sample_key": gt_norm.get("sample_key"),
            "gt_target_count": gt_target_count,
            "gt_retained": gt_retained,
            **counts,
        }
    )
    _write_json(os.path.join(pair_dir, "stats.json"), refreshed)

    stage_path = os.path.join(pair_dir, "stage_metrics.json")
    if os.path.exists(stage_path):
        stage_metrics = _read_json(stage_path)
        if isinstance(stage_metrics, dict) and isinstance(stage_metrics.get("triage"), dict):
            stage_metrics["triage"].update(triage_counts)
            _write_json(stage_path, stage_metrics)
    return refreshed


def _process_pair(
    idx: int,
    total: int,
    target: str,
    baseline: str,
    category_outdir: str,
    run_opts: Dict[str, Any],
    gt: Optional[Dict[str, Any]],
) -> Dict[str, Any]:
    try:
        target_name = oxide.api.get_colname_from_oid(target)
    except Exception:
        target_name = str(target)
    if isinstance(target_name, set):
        target_name = next(iter(sorted(str(x) for x in target_name)), str(target))
    if not target_name:
        target_name = str(target)
    try:
        baseline_name = oxide.api.get_colname_from_oid(baseline)
    except Exception:
        baseline_name = str(baseline)
    if isinstance(baseline_name, set):
        baseline_name = next(iter(sorted(str(x) for x in baseline_name)), str(baseline))
    if not baseline_name:
        baseline_name = str(baseline)

    pair_dir = os.path.join(category_outdir, _comparison_dir(target_name, baseline_name))
    if _sample_is_complete(pair_dir):
        logger.info("[%d/%d] %s -> %s (cached)", idx, total, target_name, baseline_name)
        stats = _read_json(os.path.join(pair_dir, "stats.json"))
        if gt:
            stats = _refresh_cached_stats_ground_truth(pair_dir, stats, gt, target_name, target)
        stage_metrics = _read_json(os.path.join(pair_dir, "stage_metrics.json"))
    else:
        logger.info("[%d/%d] START %s -> %s", idx, total, target_name, baseline_name)
        pair_t0 = time.perf_counter()
        result = _run_one_comparison(target, baseline, pair_dir, run_opts)
        stats = result.get("stats")
        stage_metrics = result.get("stage_metrics")
        # Without a finish line an interleaved run shows only starts, so there is no way
        # to tell which samples are still in flight or how long any of them took.
        summary = stats if isinstance(stats, dict) else {}
        logger.info(
            "[%d/%d] DONE %s in %.1fm (%d filtered, %d investigated, %d flagged, %d failed)",
            idx, total, target_name, (time.perf_counter() - pair_t0) / 60.0,
            int(summary.get("filtered_functions") or 0),
            int(summary.get("investigated_functions") or 0),
            int(summary.get("flagged_functions") or 0),
            int(summary.get("failed_functions") or 0),
        )

    row = dict(stats) if isinstance(stats, dict) else {}
    # Carried in memory only, for the per-stage columns of the summary. stats.json on disk
    # stays a clean tool-wide record with no stage fields in it.
    if isinstance(stage_metrics, dict):
        row["_stage_metrics"] = stage_metrics
    return row


DEFAULT_OLLAMA_URL = "http://127.0.0.1:11434"
DEFAULT_OLLAMA_BASE_PORT = 11435


def _explicit_endpoints(opts: Dict[str, Any]) -> List[str]:
    """Ollama base URLs given by the caller, if any."""
    raw = opts.get("endpoints") or opts.get("ollama_base_urls") or os.getenv("DELT_ENDPOINTS")
    if isinstance(raw, (list, tuple)):
        return [str(u).strip() for u in raw if str(u).strip()]
    return [u.strip() for u in str(raw or "").split(",") if u.strip()]


def _endpoint_serves_model(base_url: str, model: str, timeout: float = 5.0) -> Optional[str]:
    """None if base_url is serving `model`, else a one-line reason why not."""
    url = base_url.rstrip("/") + "/api/tags"
    try:
        with urllib.request.urlopen(url, timeout=timeout) as resp:
            payload = json.loads(resp.read().decode("utf-8", errors="replace"))
    except Exception as exc:  # noqa: BLE001 — any failure here is a config error to report
        return f"unreachable ({exc!r})"
    names = {str(entry.get("name") or "") for entry in (payload.get("models") or [])}
    if model not in names:
        listed = ", ".join(sorted(names)[:4]) or "none"
        return f"reachable but does not serve {model!r} (has: {listed})"
    return None


def _preflight_endpoints(endpoints: List[str], model: str) -> None:
    """Fail before any comparison runs if an endpoint cannot serve the model.

    Without this a dead or misconfigured endpoint just makes every model call raise
    ConnectError, and the run still writes a full set of stats.json files reporting zero
    detections -- an infrastructure failure that reads exactly like a model result.
    """
    problems = [(url, why) for url in endpoints if (why := _endpoint_serves_model(url, model))]
    if not problems:
        logger.info("endpoint preflight ok: %d endpoint(s) serving %s", len(endpoints), model)
        return
    detail = "\n".join(f"  {url}: {why}" for url, why in problems)
    raise RuntimeError(
        f"{len(problems)} of {len(endpoints)} Ollama endpoint(s) cannot serve {model!r}:\n{detail}\n"
        "Fix the endpoints (or drop --endpoints to let the run launch its own) and retry."
    )


def _free_port_block(base_port: int, count: int, limit: int = 200) -> int:
    """First port p >= base_port where p .. p+count-1 are all unused.

    Ports near the Ollama default are often already taken -- 11435 in particular may
    belong to another user's server -- so scan rather than fail on the first collision.
    """
    for start in range(base_port, base_port + limit):
        if all(_port_is_free(start + offset) for offset in range(count)):
            return start
    raise RuntimeError(
        f"No block of {count} free ports found at or above {base_port}."
    )


def _port_is_free(port: int) -> bool:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.settimeout(0.3)
        return sock.connect_ex(("127.0.0.1", port)) != 0


def _provision_sample_endpoints(
    opts: Dict[str, Any], sample_workers: int
) -> Tuple[List[str], Any]:
    """Return (endpoints, manager) ready for use, or raise explaining what is wrong.

    Explicit endpoints (the `endpoints` opt or DELT_ENDPOINTS) are used as given. Otherwise
    one Ollama server per GPU is launched for the run and shut down afterwards. Either way
    every endpoint is verified to serve the model before any comparison starts; `manager`
    is None when nothing was launched and must otherwise be shut down by the caller.
    """
    model = str(opts.get("model") or "")
    explicit = _explicit_endpoints(opts)
    if explicit:
        logger.info("using %d caller-supplied endpoint(s)", len(explicit))
        _preflight_endpoints(explicit, model)
        return explicit, None

    if sample_workers <= 1:
        _preflight_endpoints([DEFAULT_OLLAMA_URL], model)
        return [], None

    # Lazy import: only pull in the launcher when multi-endpoint fan-out is actually used.
    from oxide.plugins import delt_three_stage

    base_port = _free_port_block(
        int(opts.get("ollama_base_port") or DEFAULT_OLLAMA_BASE_PORT), sample_workers
    )
    logger.info(
        "launching %d Ollama server(s) for this run on ports %d-%d (one per GPU)",
        sample_workers, base_port, base_port + sample_workers - 1,
    )
    manager = delt_three_stage.OllamaManager()
    endpoints = manager.launch(sample_workers, model, base_port=base_port)
    try:
        # OllamaManager only logs a warning when warmup fails, so a server can come up
        # pointed at the wrong model store and 404 every call. Verify before running.
        _preflight_endpoints(endpoints, model)
    except Exception:
        manager.shutdown()
        raise
    return endpoints, manager


def _run_category(
    pairs: List[Tuple[str, str]],
    category_outdir: str,
    run_opts: Dict[str, Any],
    *,
    gt: Optional[Dict[str, Any]] = None,
    sample_workers: int = 1,
    endpoints: Optional[List[str]] = None,
) -> List[Dict[str, Any]]:
    """Run every comparison in a category, returning rows in the input pair order.

    Parallelism is at the sample level: each worker runs whole comparisons end to end, so
    triage, binary context, and verification all run concurrently across workers. Workers
    pull from a shared queue, which self-balances the very uneven per-sample function
    counts without needing to know them up front.
    """
    os.makedirs(category_outdir, exist_ok=True)
    total = len(pairs)
    endpoints = list(endpoints or [])

    if sample_workers <= 1 or total <= 1:
        return [
            _process_pair(idx, total, target, baseline, category_outdir, run_opts, gt)
            for idx, (target, baseline) in enumerate(pairs, 1)
        ]

    n_workers = min(sample_workers, total)
    work: "queue.Queue[Tuple[int, str, str]]" = queue.Queue()
    for idx, (target, baseline) in enumerate(pairs, 1):
        work.put((idx, target, baseline))
    results: Dict[int, Dict[str, Any]] = {}
    results_lock = threading.Lock()

    def _worker(worker_idx: int) -> None:
        # One endpoint per worker, so each worker's runtime gets its own model client.
        worker_opts = dict(run_opts)
        if endpoints:
            worker_opts["ollama_base_url"] = endpoints[worker_idx % len(endpoints)]
        while True:
            try:
                idx, target, baseline = work.get_nowait()
            except queue.Empty:
                return
            try:
                row = _process_pair(idx, total, target, baseline, category_outdir, worker_opts, gt)
            except Exception as exc:  # noqa: BLE001 — one bad comparison must not kill the worker
                logger.exception(
                    "[%d/%d] FAILED %s -> %s on %s", idx, total, target, baseline,
                    worker_opts.get("ollama_base_url") or "default endpoint",
                )
                row = {"error": repr(exc)}
            with results_lock:
                results[idx] = row
                completed = len(results)
            logger.info("progress: %d/%d comparisons complete, %d in flight",
                        completed, total, min(n_workers, total - completed))
            work.task_done()

    logger.info(
        "sample-level parallelism: %d workers over %d comparisons, %s",
        n_workers, total,
        f"{len(endpoints)} endpoint(s)" if endpoints else "shared endpoint",
    )
    threads = [threading.Thread(target=_worker, args=(w,), daemon=True) for w in range(n_workers)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()
    return [results[i] for i in sorted(results)]


def _stage(row: Dict[str, Any], stage: str) -> Dict[str, Any]:
    """Per-stage metrics attached to a result row by _process_pair, or {} if absent."""
    metrics = row.get("_stage_metrics")
    if not isinstance(metrics, dict):
        return {}
    stage_metrics = metrics.get(stage)
    return stage_metrics if isinstance(stage_metrics, dict) else {}


def _fp_bin_counts(results: List[Dict[str, Any]], stage: Optional[str] = None) -> Dict[str, int]:
    counts = {label: 0 for label, _, _ in FP_BINS}
    for row in results:
        source = _stage(row, stage) if stage else row
        # Under the TPS paper definition, failed reviews remain in the final
        # not_safe queue rather than being counted as cleared.
        flagged = int(source.get("flagged_functions") or 0) + int(source.get("failed_functions") or 0)
        for label, lower, upper in FP_BINS:
            if flagged < lower:
                continue
            if upper is not None and flagged > upper:
                continue
            counts[label] += 1
            break
    return counts


def _summarize_category(results: List[Dict[str, Any]], category: str) -> Dict[str, Any]:
    total_pairs = len(results)
    total_input_tokens = sum(int(row.get("input_tokens") or 0) for row in results)
    total_output_tokens = sum(int(row.get("output_tokens") or 0) for row in results)
    total_tokens = sum(int(row.get("total_tokens") or 0) for row in results)
    total_filtered = sum(int(row.get("filtered_functions") or 0) for row in results)
    total_flagged = sum(int(row.get("flagged_functions") or 0) for row in results)
    total_failed = sum(int(row.get("failed_functions") or 0) for row in results)
    investigated = sum(int(row.get("investigated_functions") or 0) for row in results)

    def _stage_sum(stage: str, key: str) -> int:
        return sum(int(_stage(row, stage).get(key) or 0) for row in results)

    triage_tokens = _stage_sum("triage", "total_tokens")
    verification_tokens = _stage_sum("verification", "total_tokens")

    summary: Dict[str, Any] = {
        "total_pairs": total_pairs,
        "input_tokens": total_input_tokens,
        "output_tokens": total_output_tokens,
        "total_tokens": total_tokens,
        "filtered_functions": total_filtered,
        "investigated_functions": investigated,
        "flagged_functions": total_flagged,
        "failed_functions": total_failed,
        "avg_input_tokens_per_invocation": (total_input_tokens / float(total_filtered)) if total_filtered else 0.0,
        "avg_output_tokens_per_invocation": (total_output_tokens / float(total_filtered)) if total_filtered else 0.0,
        "avg_total_tokens_per_invocation": (total_tokens / float(total_filtered)) if total_filtered else 0.0,
        # Per-stage breakdown. Triage runs on every filtered candidate; Verification only on
        # the escalated ones, so each average carries its own denominator.
        "stages": {
            "triage": {
                "flagged_functions": _stage_sum("triage", "flagged_functions"),
                "dismissed_functions": _stage_sum("triage", "dismissed_functions"),
                "failed_functions": _stage_sum("triage", "failed_functions"),
                "total_tokens": triage_tokens,
                "avg_tokens_per_function": (triage_tokens / float(total_filtered)) if total_filtered else 0.0,
            },
            "verification": {
                "investigations": _stage_sum("verification", "investigations"),
                "with_report": _stage_sum("verification", "with_report"),
                "without_report": _stage_sum("verification", "without_report"),
                "flagged_functions": _stage_sum("verification", "flagged_functions"),
                "cleared_functions": _stage_sum("verification", "cleared_functions"),
                "failed_functions": _stage_sum("verification", "failed_functions"),
                "total_tokens": verification_tokens,
                "avg_tokens_per_investigation": (verification_tokens / float(investigated)) if investigated else 0.0,
            },
        },
    }

    if category == "backdoored":
        def _recall(rows: List[Dict[str, Any]], src: Optional[str]) -> Dict[str, Any]:
            def _get(row: Dict[str, Any], key: str) -> int:
                return int((_stage(row, src) if src else row).get(key) or 0)

            hits = sum(1 for row in rows if _get(row, "hit") > 0)
            dismissed = sum(1 for row in rows if _get(row, "hit") <= 0 and _get(row, "dismissed") > 0)
            failed = sum(1 for row in rows if _get(row, "hit") <= 0 and _get(row, "failed") > 0)
            not_safe_pairs = hits + failed
            safe_pairs = total_pairs - not_safe_pairs
            return {
                "not_safe_pairs": not_safe_pairs,
                "safe_pairs": safe_pairs,
                "not_safe_pairs_hit": hits,
                "not_safe_pairs_failed": failed,
                "safe_pairs_dismissed": dismissed,
                "safe_pairs_no_gt_retained": max(0, safe_pairs - dismissed),
            }

        summary.update(_recall(results, None))
        # Triage's recall on its own, for the single-stage comparison.
        summary["stages"]["triage"].update(_recall(results, "triage"))
    else:
        not_safe_pairs = sum(
            1
            for row in results
            if (int(row.get("flagged_functions") or 0) + int(row.get("failed_functions") or 0)) > 0
        )
        summary["not_safe_pairs"] = not_safe_pairs
        summary["safe_pairs"] = total_pairs - not_safe_pairs
        summary["fp_bins"] = _fp_bin_counts(results)
        summary["stages"]["triage"]["fp_bins"] = _fp_bin_counts(results, "triage")

    return summary


def _function_names(oid: str) -> Dict[str, str]:
    """Decimal address string -> function name for one binary."""
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    return {str(addr): str((meta or {}).get("name") or "") for addr, meta in funcs.items() if addr is not None}


def _candidate_target_addr(item: Any) -> Optional[str]:
    """Pull the target-side address out of a drift item. Filtered functions come from
    the drift adapter already normalized, excluded ones are still drift's raw
    {"pair": [target, baseline]} shape, and added ones carry a bare "address"."""
    if not isinstance(item, dict):
        return ensure_decimal_str(item)
    if item.get("target_func_addr") is not None:
        return ensure_decimal_str(item.get("target_func_addr"))
    if item.get("address") is not None:
        return ensure_decimal_str(item.get("address"))
    pair = item.get("pair") or []
    return ensure_decimal_str(pair[0]) if pair else None


def _hex_addr(addr: Optional[str]) -> str:
    try:
        return hex(int(str(addr)))
    except (TypeError, ValueError):
        return ""


def _build_candidate_functions(
    drift_json: Dict[str, Any],
    gt_norm: Optional[Dict[str, Any]],
) -> List[Dict[str, Any]]:
    """Flatten a comparison's drift output into one row per function drift saw, so the
    search space can be eyeballed (and ground truth authored) without running triage."""
    candidates: List[Dict[str, Any]] = []

    for file_pair in drift_json.get("file_pairs", []) or []:
        target_oid = file_pair.get("target_oid")
        baseline_oid = file_pair.get("baseline_oid")
        names = _function_names(target_oid) if target_oid else {}

        for kind, items in (
            ("filtered", file_pair.get("modified_functions") or []),
            ("excluded", file_pair.get("excluded_functions") or []),
            ("added", file_pair.get("added_functions") or []),
        ):
            for item in items:
                addr = _candidate_target_addr(item)
                name = names.get(addr or "") or (item.get("name") if isinstance(item, dict) else None)
                row: Dict[str, Any] = {
                    "kind": kind,
                    "target_oid": target_oid,
                    "baseline_oid": baseline_oid,
                    "target_addr": addr,
                    "target_addr_hex": _hex_addr(addr),
                    "target_func_name": str(name or ""),
                }
                if gt_norm:
                    row["ground_truth"] = gt_row_matches_any(
                        {"target_addr": addr, "target_oid": target_oid}, gt_norm
                    )
                candidates.append(row)

    return candidates


def _run_filter_census_comparison(
    target: str,
    baseline: str,
    outdir: str,
    filter_key: Optional[str],
    gt: Dict[str, Any],
    target_name: str,
) -> Dict[str, Any]:
    os.makedirs(outdir, exist_ok=True)
    drift_json = build_drift_file_pairs(target, baseline, filter_key) or {}
    _write_json(os.path.join(outdir, "drift_raw.json"), drift_json)

    gt_norm = get_ground_truth_for_target(gt, target_name, pair_dir=outdir, target_oid=target)
    candidates = _build_candidate_functions(drift_json, gt_norm)
    _write_json(os.path.join(outdir, "candidate_functions.json"), candidates)

    filtered = [row for row in candidates if row["kind"] == "filtered"]
    excluded = [row for row in candidates if row["kind"] == "excluded"]

    stats = {
        "modified_functions": len(filtered) + len(excluded),
        "filtered_functions": len(filtered),
        "excluded_functions": len(excluded),
        "added_functions": sum(1 for row in candidates if row["kind"] == "added"),
        "gt_in_filtered": int(any(row.get("ground_truth") for row in filtered)),
        "gt_in_excluded": int(any(row.get("ground_truth") for row in excluded)),
    }
    _write_json(os.path.join(outdir, "stats.json"), stats)
    return stats


def _run_filter_census_category(
    pairs: List[Tuple[str, str]],
    category_outdir: str,
    filter_key: Optional[str],
    gt: Dict[str, Any],
) -> List[Dict[str, Any]]:
    os.makedirs(category_outdir, exist_ok=True)
    results: List[Dict[str, Any]] = []
    candidates_by_sample: Dict[str, Any] = {}
    total = len(pairs)

    for idx, (target, baseline) in enumerate(pairs, 1):
        try:
            target_name = oxide.api.get_colname_from_oid(target)
        except Exception:
            target_name = str(target)
        try:
            baseline_name = oxide.api.get_colname_from_oid(baseline)
        except Exception:
            baseline_name = str(baseline)

        pair_dir = os.path.join(category_outdir, _comparison_dir(target_name, baseline_name))
        candidates_path = os.path.join(pair_dir, "candidate_functions.json")
        # Pairs cached by an older run have stats but no candidate dump, so re-run those
        # (the underlying drift results are cached, only the reshaping repeats).
        if _sample_is_complete(pair_dir) and os.path.exists(candidates_path):
            logger.info("[%d/%d] skipping %s (already complete)", idx, total, pair_dir)
            stats = _read_json(os.path.join(pair_dir, "stats.json"))
            results.append(stats if isinstance(stats, dict) else {})
            candidates_by_sample[str(target_name)] = _read_json(candidates_path)
            continue

        logger.info("[%d/%d] %s -> %s", idx, total, target_name, baseline_name)
        stats = _run_filter_census_comparison(target, baseline, pair_dir, filter_key, gt, target_name)
        results.append(stats)
        candidates_by_sample[str(target_name)] = _read_json(candidates_path)

    _write_json(os.path.join(category_outdir, "candidate_functions_by_sample.json"), candidates_by_sample)
    return results


def _summarize_filter_census(results: List[Dict[str, Any]], category: str) -> Dict[str, Any]:
    summary: Dict[str, Any] = {
        "total_pairs": len(results),
        "modified_functions": sum(int(row.get("modified_functions") or 0) for row in results),
        "filtered_functions": sum(int(row.get("filtered_functions") or 0) for row in results),
        "excluded_functions": sum(int(row.get("excluded_functions") or 0) for row in results),
        "added_functions": sum(int(row.get("added_functions") or 0) for row in results),
    }
    if category == "backdoored":
        summary["gt_in_filter"] = sum(int(row.get("gt_in_filtered") or 0) for row in results)
        summary["gt_in_excluded"] = sum(int(row.get("gt_in_excluded") or 0) for row in results)
    return summary


def _build_openwrt_rows(results: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    for row in results:
        rows.append(
            {
                "target": row.get("target_name") or row.get("target"),
                "baseline": row.get("baseline_name") or row.get("baseline"),
                "modified_files": int(row.get("modified_files") or 0),
                "flagged_files": int(row.get("flagged_files") or 0),
                "modified_functions": int(row.get("modified_functions") or 0),
                "filtered_functions": int(row.get("filtered_functions") or 0),
                "flagged_functions": int(row.get("flagged_functions") or 0),
                "failed_functions": int(row.get("failed_functions") or 0),
                "investigated_functions": int(row.get("investigated_functions") or 0),
                "triage_total_tokens": int(_stage(row, "triage").get("total_tokens") or 0),
                "verification_total_tokens": int(_stage(row, "verification").get("total_tokens") or 0),
                "input_tokens": int(row.get("input_tokens") or 0),
                "output_tokens": int(row.get("output_tokens") or 0),
                "total_tokens": int(row.get("total_tokens") or 0),
            }
        )
    return rows


def _prepare_run_opts(opts: Dict[str, Any], *, diff_mode: str, filter_key: Optional[str], gt_path: Optional[str], overrides: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    run_opts = dict(opts)
    run_opts["diff_mode"] = diff_mode
    run_opts["filter"] = filter_key
    run_opts["ground_truth"] = gt_path
    if overrides:
        run_opts.update(overrides)
    return run_opts


def _run_filter_census(
    outdir: str,
    backdoored_pairs: List[Tuple[str, str]],
    safe_pairs: List[Tuple[str, str]],
    gt: Dict[str, Any],
) -> Dict[str, Any]:
    """Run the model-independent structural filter census once at the experiment root."""
    census_summaries: Dict[str, Any] = {}
    for census_name, filter_key in FILTER_CENSUS_CONFIGS:
        census_dir = os.path.join(outdir, census_name)
        os.makedirs(census_dir, exist_ok=True)
        census_summary: Dict[str, Any] = {}

        for category, pairs, category_gt in (
            ("backdoored", backdoored_pairs, gt),
            ("safe", safe_pairs, {}),
        ):
            if not pairs:
                continue
            results = _run_filter_census_category(
                pairs,
                os.path.join(census_dir, category),
                filter_key,
                category_gt,
            )
            summary = _summarize_filter_census(results, category)
            census_summary[category] = summary
            _write_json(os.path.join(census_dir, category, "series_metrics.json"), summary)

        _write_json(os.path.join(census_dir, "config_summary.json"), census_summary)
        census_summaries[census_name] = census_summary
    return census_summaries


def _run_experiment_configs(
    base_opts: Dict[str, Any],
    *,
    config_root: str,
    backdoored_pairs: List[Tuple[str, str]],
    safe_pairs: List[Tuple[str, str]],
    openwrt_pairs: List[Tuple[str, str]],
    gt: Dict[str, Any],
    gt_path: Optional[str],
    dry_run: bool = False,
) -> Dict[str, Any]:
    """Run the LLM experiment configs for a single model into config_root. In dry_run mode
    only the deployed `delt_verification` config runs, with triage disabled, so each modified function
    gets its unified diff and agent inputs on disk but the agent never runs."""
    configs = EXPERIMENT_CONFIGS
    if dry_run:
        configs = tuple(cfg for cfg in EXPERIMENT_CONFIGS if cfg[0] == "delt_verification")
    config_summaries: Dict[str, Any] = {}
    for config_name, diff_mode, filter_key, overrides in configs:
        config_dir = os.path.join(config_root, config_name)
        os.makedirs(config_dir, exist_ok=True)
        include_added_callees = bool(
            overrides.get("include_added_callees", base_opts.get("include_added_callees", True))
        )
        config_summary: Dict[str, Any] = {
            "model": base_opts.get("model"),
            "sample_workers": int(base_opts.get("sample_workers") or 1),
            "diff_mode": diff_mode,
            "filter_mode": "NONE" if not filter_key else filter_key,
            "include_added_callees": include_added_callees,
            "verification_request_s": float(base_opts.get("verification_request_s") or 600.0),
        }

        # gt_only is a backdoor-recall shortcut: only the ground-truth function is triaged.
        # It applies to the backdoored set alone. The safe/openwrt categories have no ground
        # truth, so they always run in full, with gt_only forced off for them below.
        gt_only = bool(base_opts.get("gt_only"))
        categories: List[Tuple[str, List[Tuple[str, str]], Optional[str], Dict[str, Any]]] = []
        if backdoored_pairs:
            categories.append(("backdoored", backdoored_pairs, gt_path, gt))
        if safe_pairs:
            categories.append(("safe", safe_pairs, None, {}))
        if openwrt_pairs and config_name == "delt_verification":
            categories.append(("openwrt", openwrt_pairs, None, {}))

        for category, pairs, category_gt_path, category_gt in categories:
            category_dir = os.path.join(config_dir, category)
            run_opts = _prepare_run_opts(
                base_opts,
                diff_mode=diff_mode,
                filter_key=filter_key,
                gt_path=category_gt_path,
                overrides=overrides,
            )
            # gt_only restricts triage to the ground-truth function, which only exists for
            # the backdoored set. Force it off everywhere else so safe/openwrt triage every
            # filtered function and their false-positive counts stay complete.
            run_opts["gt_only"] = gt_only and category == "backdoored"
            results = _run_category(
                pairs, category_dir, run_opts, gt=category_gt,
                sample_workers=int(base_opts.get("sample_workers") or 1),
                endpoints=list(base_opts.get("_endpoints") or []),
            )
            summary = _summarize_category(results, category)
            config_summary[category] = summary

            comparison_rows = [
                {"index": index + 1, **row}
                for index, row in enumerate(results)
            ]
            _write_json(
                os.path.join(category_dir, "comparisons_summary.json"),
                {
                    "config": config_name,
                    "category": category,
                    "comparisons": comparison_rows,
                },
            )
            _write_json(os.path.join(category_dir, "series_metrics.json"), summary)
            if category == "openwrt":
                _write_json(os.path.join(category_dir, "openwrt_table_rows.json"), _build_openwrt_rows(results))
            _write_text(
                os.path.join(category_dir, "series_summary.txt"),
                "\n".join([f"{key}: {value}" for key, value in summary.items()]),
            )

        _write_json(os.path.join(config_dir, "config_summary.json"), config_summary)
        config_summaries[config_name] = config_summary
    return config_summaries


def run_drift(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Run only the structural drift stage over the backdoored and safe pairs, no LLM.

    Use this before `run_experiments` to see the search space each comparison produces
    and to work out ground truth. Both filter policies are run (filter_OR and
    filter_NONE), which is exactly the census `run_experiments` does at its root, so
    pointing this at the same --outdir means the full run reuses these results.

    Opts:
      backdoored   -- entries file of backdoored target,baseline pairs
      safe         -- entries file of safe target,baseline pairs
      ground_truth -- optional ground-truth JSON; when given, each candidate row is
                      marked with whether it matches a ground-truth target
      outdir       -- root output directory (default: out/delt_verification_experiments)

    Per comparison this writes drift_raw.json, stats.json, and candidate_functions.json
    (one row per filtered/excluded/added function with decimal + hex target address and
    the Ghidra function name). Each category also gets
    candidate_functions_by_sample.json, keyed by target collection name, which is the
    same key the ground-truth file uses.
    """
    backdoored_path: Optional[str] = opts.get("backdoored")
    safe_path: Optional[str] = opts.get("safe")
    gt_path: Optional[str] = opts.get("ground_truth")
    outdir = str(opts.get("outdir") or "out/delt_verification_experiments")

    if not backdoored_path and not safe_path:
        raise ValueError("At least one of --backdoored or --safe must be provided.")

    backdoored_pairs = _read_series_file(backdoored_path) if backdoored_path else []
    safe_pairs = _read_series_file(safe_path) if safe_path else []
    gt = load_ground_truth_file(gt_path) if gt_path else {}

    os.makedirs(outdir, exist_ok=True)
    census_summaries = _run_filter_census(outdir, backdoored_pairs, safe_pairs, gt)
    _write_json(os.path.join(outdir, "drift_summary.json"), census_summaries)
    logger.info("Drift summary written to %s", os.path.join(outdir, "drift_summary.json"))
    return census_summaries


def run_experiments(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Run the paper's full DeLT experiment matrix using the `delt_verification` analyzer.

    Required/expected opts:
      backdoored   -- entries file of backdoored target,baseline pairs
      ground_truth -- ground-truth JSON for the backdoored pairs

    Model selection:
      model        -- a single model tag passed through to the delt_verification analyzer
      models       -- a models file (like models.txt); each line is
                      `model_tag [sample_workers]` (sample_workers defaults to 1).
                      Results for each model land under outdir/<model_slug>/.
      (neither)    -- dry run: only the deployed `delt_verification` config runs, with triage
                      disabled, so each modified function gets its unified diff and the
                      agent's input files (outdir/delt/<category>/<pair>/filepair_NN/
                      modified_functions/<b..t..>/{diff.txt,agent_inputs/}) written to
                      disk without invoking the agent. Use this to author ground truth.

    Parallelization is owned by this plugin, not the analyzer: the analyzer runs one
    comparison sequentially, and this plugin runs several comparisons at once, one per
    Ollama endpoint. That parallelizes all three stages -- triage, binary context, and
    verification -- where per-function fan-out inside the analyzer would only have
    parallelized triage, the smallest share of the work. Workers pull from a shared queue,
    which self-balances the very uneven per-sample function counts.

    Endpoints are handled for you: with sample_workers > 1 and no explicit endpoints, one
    Ollama server per GPU is launched for the run and shut down when it finishes. Every
    endpoint is verified to serve the model before any comparison starts, so a dead server
    or a wrong model store fails immediately instead of producing a full set of zero-
    detection results that look like a model outcome.
      sample_workers -- how many comparisons run concurrently for the single --model form
                      (default 1). In the models file it is the per-model second column.
                      Set it to the number of GPUs you want to use.
      endpoints    -- optional comma-separated Ollama base URLs (or DELT_ENDPOINTS) to use
                      servers you started yourself, e.g.
                      http://127.0.0.1:11436,http://127.0.0.1:11437. Each worker is pinned
                      to one, and nothing is launched or shut down.
      ollama_base_port -- first port to try when launching (default 11435). Ports in use
                      are skipped, so a neighbouring server is never hijacked.

    Optional opts:
      safe         -- entries file of safe target,baseline pairs
      openwrt      -- entries file of OpenWrt target,baseline pairs
      outdir       -- root output directory (default: out/delt_verification_experiments)
      gt_only      -- backdoor-recall shortcut: triage only the ground-truth
                      insertion function(s) of each backdoored pair instead of every
                      filtered candidate, and skip the safe/openwrt categories entirely
                      (they have no ground truth). Filter counts are still reported; only
                      the triaged subset shrinks, so it runs much faster when you only
                      need to check whether the backdoor is detected.

    To run only the structural drift stage (no LLM), use `run_drift` with the same
    --backdoored/--safe/--outdir; this run then reuses its filter census.
    """
    backdoored_path: Optional[str] = opts.get("backdoored")
    safe_path: Optional[str] = opts.get("safe")
    openwrt_path: Optional[str] = opts.get("openwrt")
    gt_path: Optional[str] = opts.get("ground_truth")
    outdir = str(opts.get("outdir") or "out/delt_verification_experiments")

    if not backdoored_path and not safe_path and not openwrt_path:
        raise ValueError("At least one of --backdoored, --safe, or --openwrt must be provided.")

    model_specs, nested, dry_run = _resolve_model_specs(opts)

    backdoored_pairs = _read_series_file(backdoored_path) if backdoored_path else []
    safe_pairs = _read_series_file(safe_path) if safe_path else []
    openwrt_pairs = _read_series_file(openwrt_path) if openwrt_path else []
    gt = load_ground_truth_file(gt_path) if gt_path else {}

    os.makedirs(outdir, exist_ok=True)
    experiment_summary: Dict[str, Any] = {}

    # The structural filter census is model-independent; run it once at the root.
    experiment_summary.update(_run_filter_census(outdir, backdoored_pairs, safe_pairs, gt))

    model_summaries: Dict[str, Any] = {}
    for model, sample_workers in model_specs:
        base_opts = dict(opts)
        base_opts["model"] = model
        # Whole comparisons run concurrently here, one per endpoint; the analyzer itself is
        # sequential. See _run_category.
        base_opts["sample_workers"] = sample_workers
        # Dry run: disable triage so the analyzer only produces per-function diffs and
        # agent inputs. No model client is built.
        base_opts["no_triage"] = dry_run
        config_root = os.path.join(outdir, _model_slug(model)) if nested else outdir
        os.makedirs(config_root, exist_ok=True)

        # Provision and verify endpoints once per model, before any comparison runs, and
        # tear down anything this run launched. A dry run never calls a model.
        manager = None
        if dry_run:
            logger.info("running dry-run (no triage) to produce triage inputs")
        else:
            endpoints, manager = _provision_sample_endpoints(base_opts, sample_workers)
            base_opts["_endpoints"] = endpoints
            logger.info(
                "running experiment configs for model %s (sample_workers %d, %s)",
                model, sample_workers,
                f"{len(endpoints)} endpoint(s)" if endpoints else "default endpoint",
            )

        try:
            config_summaries = _run_experiment_configs(
                base_opts,
                config_root=config_root,
                backdoored_pairs=backdoored_pairs,
                safe_pairs=safe_pairs,
                openwrt_pairs=openwrt_pairs,
                gt=gt,
                gt_path=gt_path,
                dry_run=dry_run,
            )
        finally:
            if manager is not None:
                logger.info("shutting down Ollama server(s) launched for this run")
                manager.shutdown()

        if nested:
            model_summaries[model] = config_summaries
            _write_json(os.path.join(config_root, "experiment_summary.json"), config_summaries)
        else:
            experiment_summary.update(config_summaries)

    if nested:
        experiment_summary["models"] = model_summaries

    _write_json(os.path.join(outdir, "experiment_summary.json"), experiment_summary)
    logger.info("Experiment summary written to %s", os.path.join(outdir, "experiment_summary.json"))
    return experiment_summary


exports = [run_experiments, run_drift]
