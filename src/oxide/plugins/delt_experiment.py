from __future__ import annotations

import json
import logging
import os
import re
from typing import Any, Dict, List, Optional, Set, Tuple

from oxide.core import oxide as oxide
from oxide.core.oxide import api

from oxide.modules.analyzers.delt.pipeline.utils.drift_adapter import build_drift_file_pairs
from oxide.modules.analyzers.delt.pipeline.utils.ground_truth import (
    get_ground_truth_for_target,
    gt_row_matches_any,
    load_ground_truth_file,
)
from oxide.modules.analyzers.delt.pipeline.utils.text_utils import comparison_dir_name

NAME = "delt_experiment"
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


# Full DELT plus one config per ablated design element. Each config perturbs exactly
# one element away from the deployed configuration and every config runs the single
# triage agent, so the paper's Delta = Full - Ablated stays attributable.
EXPERIMENT_CONFIGS: Tuple[Tuple[str, str, Optional[str], Dict[str, Any]], ...] = (
    ("delt", "processed", "Call_OR_Control_Modified", {}),
    ("no_added_callees", "processed", "Call_OR_Control_Modified", {"include_added_callees": False}),
    ("no_diff_processing", "raw", "Call_OR_Control_Modified", {}),
    ("no_filter", "processed", None, {}),
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
    """Parse a models file. Each non-comment line is `model_tag [function_workers]`
    (whitespace- or comma-separated); function_workers defaults to 1."""
    specs: List[Tuple[str, int]] = []
    with open(path, "r", encoding="utf-8") as handle:
        for raw_line in handle:
            line = raw_line.split("#", 1)[0].strip()
            if not line:
                continue
            parts = line.replace(",", " ").split()
            model = parts[0]
            function_workers = int(parts[1]) if len(parts) > 1 else 1
            if function_workers < 1:
                raise ValueError(f"function_workers must be >= 1 for model '{model}' (got {function_workers}).")
            specs.append((model, function_workers))
    if not specs:
        raise ValueError(f"Models file '{path}' contained no models.")
    return specs


def _model_slug(model: str) -> str:
    return re.sub(r"[^A-Za-z0-9._-]+", "_", str(model)).strip("_") or "model"


def _resolve_model_specs(opts: Dict[str, Any]) -> Tuple[List[Tuple[str, int]], bool]:
    """Return (model_specs, nested). Each spec is (model, function_workers). `nested` is
    True when results should live under a per-model subdirectory (multi-model runs);
    False keeps the flat single-model layout."""
    models_path = opts.get("models")
    if models_path:
        return _parse_models_file(models_path), True
    model = opts.get("model")
    if not model:
        raise ValueError("run_experiments requires --model or --models (a models file).")
    function_workers = int(opts.get("function_workers") or 1)
    if function_workers < 1:
        raise ValueError(f"--function_workers must be >= 1 (got {function_workers}).")
    return [(str(model), function_workers)], False


def _run_one_comparison(target: str, baseline: str, outdir: str, opts: Dict[str, Any]) -> Dict[str, Any]:
    call_opts = dict(opts)
    call_opts["outdir"] = outdir
    return api.retrieve("delt", [target, baseline], call_opts) or {}


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
    hit_count = 0
    dismissed_count = 0
    failed_count = 0

    for row in per_function_results:
        if not isinstance(row, dict):
            continue
        if not gt_row_matches_any(row, gt_norm):
            continue
        gt_retained += 1
        if row.get("flagged_final"):
            hit_count += 1
        elif row.get("final_label") in {"failed", "skipped"}:
            failed_count += 1
        else:
            dismissed_count += 1

    refreshed = dict(stats)
    refreshed.update(
        {
            "gt_sample_key": gt_norm.get("sample_key"),
            "gt_target_count": gt_target_count,
            "gt_retained": gt_retained,
            "hit": hit_count,
            "dismissed": dismissed_count,
            "failed": failed_count,
        }
    )
    _write_json(os.path.join(pair_dir, "stats.json"), refreshed)
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
    if not target_name:
        target_name = str(target)
    try:
        baseline_name = oxide.api.get_colname_from_oid(baseline)
    except Exception:
        baseline_name = str(baseline)
    if not baseline_name:
        baseline_name = str(baseline)

    pair_dir = os.path.join(category_outdir, _comparison_dir(target_name, baseline_name))
    if _sample_is_complete(pair_dir):
        logger.info("[%d/%d] %s -> %s (cached)", idx, total, target_name, baseline_name)
        stats = _read_json(os.path.join(pair_dir, "stats.json"))
        if gt:
            stats = _refresh_cached_stats_ground_truth(pair_dir, stats, gt, target_name, target)
        return stats if isinstance(stats, dict) else {}

    logger.info("[%d/%d] %s -> %s", idx, total, target_name, baseline_name)
    result = _run_one_comparison(target, baseline, pair_dir, run_opts)
    return dict(result.get("stats") or {})


def _run_category(
    pairs: List[Tuple[str, str]],
    category_outdir: str,
    run_opts: Dict[str, Any],
    *,
    gt: Optional[Dict[str, Any]] = None,
) -> List[Dict[str, Any]]:
    # Comparisons run sequentially. Any parallelism (per-function fan-out across GPUs)
    # lives in the delt analyzer and is driven by the function_workers opt in run_opts.
    os.makedirs(category_outdir, exist_ok=True)
    total = len(pairs)
    return [
        _process_pair(idx, total, target, baseline, category_outdir, run_opts, gt)
        for idx, (target, baseline) in enumerate(pairs, 1)
    ]


def _fp_bin_counts(results: List[Dict[str, Any]]) -> Dict[str, int]:
    counts = {label: 0 for label, _, _ in FP_BINS}
    for row in results:
        # Under the TPS paper definition, failed reviews remain in the final
        # not_safe queue rather than being counted as cleared.
        flagged = int(row.get("flagged_functions") or 0) + int(row.get("failed_functions") or 0)
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

    summary: Dict[str, Any] = {
        "total_pairs": total_pairs,
        "input_tokens": total_input_tokens,
        "output_tokens": total_output_tokens,
        "total_tokens": total_tokens,
        "filtered_functions": total_filtered,
        "flagged_functions": total_flagged,
        "failed_functions": total_failed,
        "avg_input_tokens_per_invocation": (total_input_tokens / float(total_filtered)) if total_filtered else 0.0,
        "avg_output_tokens_per_invocation": (total_output_tokens / float(total_filtered)) if total_filtered else 0.0,
        "avg_total_tokens_per_invocation": (total_tokens / float(total_filtered)) if total_filtered else 0.0,
    }

    if category == "backdoored":
        hits = sum(1 for row in results if int(row.get("hit") or 0) > 0)
        dismissed = sum(1 for row in results if int(row.get("hit") or 0) <= 0 and int(row.get("dismissed") or 0) > 0)
        failed = sum(1 for row in results if int(row.get("hit") or 0) <= 0 and int(row.get("failed") or 0) > 0)
        not_safe_pairs = hits + failed
        safe_pairs = total_pairs - not_safe_pairs
        summary.update(
            {
                "not_safe_pairs": not_safe_pairs,
                "safe_pairs": safe_pairs,
                "not_safe_pairs_hit": hits,
                "not_safe_pairs_failed": failed,
                "safe_pairs_dismissed": dismissed,
                "safe_pairs_no_gt_retained": max(0, safe_pairs - dismissed),
            }
        )
    else:
        not_safe_pairs = sum(
            1
            for row in results
            if (int(row.get("flagged_functions") or 0) + int(row.get("failed_functions") or 0)) > 0
        )
        summary["not_safe_pairs"] = not_safe_pairs
        summary["safe_pairs"] = total_pairs - not_safe_pairs
        summary["fp_bins"] = _fp_bin_counts(results)

    return summary


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

    file_pairs = drift_json.get("file_pairs", []) or []
    modified_functions = 0
    filtered_functions = 0
    excluded_functions = 0

    gt_norm = get_ground_truth_for_target(gt, target_name, pair_dir=outdir, target_oid=target)
    gt_in_filtered = 0

    for file_pair in file_pairs:
        target_oid = file_pair.get("target_oid")
        filtered_mods = file_pair.get("modified_functions", []) or []
        excluded_mods = file_pair.get("excluded_functions", []) or []

        modified_functions += len(filtered_mods) + len(excluded_mods)
        filtered_functions += len(filtered_mods)
        excluded_functions += len(excluded_mods)

        if gt_norm and not gt_in_filtered:
            for func in filtered_mods:
                row = {"target_addr": func.get("target_func_addr"), "target_oid": target_oid}
                if gt_row_matches_any(row, gt_norm):
                    gt_in_filtered = 1
                    break

    stats = {
        "modified_functions": modified_functions,
        "filtered_functions": filtered_functions,
        "excluded_functions": excluded_functions,
        "gt_in_filtered": gt_in_filtered,
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
        if _sample_is_complete(pair_dir):
            logger.info("[%d/%d] skipping %s (already complete)", idx, total, pair_dir)
            stats = _read_json(os.path.join(pair_dir, "stats.json"))
            results.append(stats if isinstance(stats, dict) else {})
            continue

        logger.info("[%d/%d] %s -> %s", idx, total, target_name, baseline_name)
        stats = _run_filter_census_comparison(target, baseline, pair_dir, filter_key, gt, target_name)
        results.append(stats)

    return results


def _summarize_filter_census(results: List[Dict[str, Any]], category: str) -> Dict[str, Any]:
    summary: Dict[str, Any] = {
        "total_pairs": len(results),
        "modified_functions": sum(int(row.get("modified_functions") or 0) for row in results),
        "filtered_functions": sum(int(row.get("filtered_functions") or 0) for row in results),
        "excluded_functions": sum(int(row.get("excluded_functions") or 0) for row in results),
    }
    if category == "backdoored":
        summary["gt_in_filter"] = sum(int(row.get("gt_in_filtered") or 0) for row in results)
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
) -> Dict[str, Any]:
    """Run the LLM experiment configs for a single model into config_root."""
    config_summaries: Dict[str, Any] = {}
    for config_name, diff_mode, filter_key, overrides in EXPERIMENT_CONFIGS:
        config_dir = os.path.join(config_root, config_name)
        os.makedirs(config_dir, exist_ok=True)
        include_added_callees = bool(
            overrides.get("include_added_callees", base_opts.get("include_added_callees", True))
        )
        config_summary: Dict[str, Any] = {
            "model": base_opts.get("model"),
            "function_workers": int(base_opts.get("function_workers") or 1),
            "diff_mode": diff_mode,
            "filter_mode": "NONE" if not filter_key else filter_key,
            "include_added_callees": include_added_callees,
        }

        categories: List[Tuple[str, List[Tuple[str, str]], Optional[str], Dict[str, Any]]] = []
        if backdoored_pairs:
            categories.append(("backdoored", backdoored_pairs, gt_path, gt))
        if safe_pairs:
            categories.append(("safe", safe_pairs, None, {}))
        if openwrt_pairs and config_name == "delt":
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
            results = _run_category(pairs, category_dir, run_opts, gt=category_gt)
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


def run_experiments(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Run the paper's full DeLT experiment matrix using the `delt` analyzer.

    Required/expected opts:
      backdoored   -- entries file of backdoored target,baseline pairs
      ground_truth -- ground-truth JSON for the backdoored pairs

    Model selection (exactly one of):
      model        -- a single model tag passed through to the delt analyzer
      models       -- a models file (like models.txt); each line is
                      `model_tag [function_workers]` (function_workers defaults to 1).
                      Results for each model land under outdir/<model_slug>/.

    Parallelization is owned by the delt analyzer, not this plugin: comparisons run
    sequentially here, and when function_workers > 1 the analyzer triages functions
    concurrently, provisioning one Ollama server per GPU on its own. This plugin only
    forwards the relevant opts to the analyzer:
      function_workers -- per-function worker count for the single --model form
                      (default 1). In the models file it is the per-model second column.
      ollama_base_port -- base port for the analyzer's per-GPU Ollama servers (default
                      11435; worker i -> GPU i on port base_port + i).
      endpoints    -- explicit comma-separated Ollama base URLs (or DELT_ENDPOINTS),
                      overriding auto-launch.

    Optional opts:
      safe         -- entries file of safe target,baseline pairs
      openwrt      -- entries file of OpenWrt target,baseline pairs
      outdir       -- root output directory (default: out_delt_experiments)
    """
    backdoored_path: Optional[str] = opts.get("backdoored")
    safe_path: Optional[str] = opts.get("safe")
    openwrt_path: Optional[str] = opts.get("openwrt")
    gt_path: Optional[str] = opts.get("ground_truth")
    outdir = str(opts.get("outdir") or "out/delt_experiments")

    if not backdoored_path and not safe_path and not openwrt_path:
        raise ValueError("At least one of --backdoored, --safe, or --openwrt must be provided.")

    model_specs, nested = _resolve_model_specs(opts)

    backdoored_pairs = _read_series_file(backdoored_path) if backdoored_path else []
    safe_pairs = _read_series_file(safe_path) if safe_path else []
    openwrt_pairs = _read_series_file(openwrt_path) if openwrt_path else []
    gt = load_ground_truth_file(gt_path) if gt_path else {}

    os.makedirs(outdir, exist_ok=True)
    experiment_summary: Dict[str, Any] = {}

    # The structural filter census is model-independent; run it once at the root.
    experiment_summary.update(_run_filter_census(outdir, backdoored_pairs, safe_pairs, gt))

    model_summaries: Dict[str, Any] = {}
    for model, function_workers in model_specs:
        base_opts = dict(opts)
        base_opts["model"] = model
        # Comparisons run sequentially here; the delt analyzer fans functions across GPUs
        # when function_workers > 1, provisioning per-GPU Ollama servers on its own.
        base_opts["function_workers"] = function_workers
        config_root = os.path.join(outdir, _model_slug(model)) if nested else outdir
        os.makedirs(config_root, exist_ok=True)

        logger.info(
            "running experiment configs for model %s (function_workers %d)",
            model, function_workers,
        )

        config_summaries = _run_experiment_configs(
            base_opts,
            config_root=config_root,
            backdoored_pairs=backdoored_pairs,
            safe_pairs=safe_pairs,
            openwrt_pairs=openwrt_pairs,
            gt=gt,
            gt_path=gt_path,
        )

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


exports = [run_experiments]
