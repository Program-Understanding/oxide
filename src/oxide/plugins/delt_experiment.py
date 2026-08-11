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
from oxide.modules.analyzers.delt.pipeline.utils.text_utils import comparison_dir_name, ensure_decimal_str

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
# (Table tab:filter-coverage). AND is DRIFT's C&C Modified criterion, reported to show
# what the tighter policy would have cost in insertion-point coverage.
FILTER_CENSUS_CONFIGS: Tuple[Tuple[str, Optional[str]], ...] = (
    ("filter_OR", "Call_OR_Control_Modified"),
    ("filter_AND", "Control_Call_Modified"),
    ("filter_NONE", None),
)


# Full DELT plus one config per ablated design element. Each ablation perturbs exactly
# one element away from the deployed configuration and every config runs the single
# triage agent, so the paper's Delta = Full - Ablated stays attributable. `base` strips
# all three at once, giving the floor the deployed configuration is measured against:
# every modified function forwarded, as a raw decompiled diff, with no added callees.
EXPERIMENT_CONFIGS: Tuple[Tuple[str, str, Optional[str], Dict[str, Any]], ...] = (
    ("delt", "processed", "Call_OR_Control_Modified", {}),
    ("no_added_callees", "processed", "Call_OR_Control_Modified", {"include_added_callees": False}),
    ("no_diff_processing", "raw", "Call_OR_Control_Modified", {}),
    ("no_filter", "processed", None, {}),
    ("base", "raw", None, {"include_added_callees": False}),
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


def _parse_models_file(path: str) -> List[str]:
    """Parse a models file. Each non-comment line is one model tag."""
    models: List[str] = []
    with open(path, "r", encoding="utf-8") as handle:
        for raw_line in handle:
            line = raw_line.split("#", 1)[0].strip()
            if not line:
                continue
            models.append(line.replace(",", " ").split()[0])
    if not models:
        raise ValueError(f"Models file '{path}' contained no models.")
    return models


def _model_slug(model: str) -> str:
    return re.sub(r"[^A-Za-z0-9._-]+", "_", str(model)).strip("_") or "model"


def _resolve_model_specs(opts: Dict[str, Any]) -> Tuple[List[str], bool, bool]:
    """Return (models, nested, dry_run).
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
        return ["dry_run"], False, True
    return [str(model)], False, False


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
    # Comparisons run sequentially.
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
    only the deployed `delt` config runs, with triage disabled, so each modified function
    gets its unified diff and agent inputs on disk but the agent never runs."""
    configs = EXPERIMENT_CONFIGS
    if dry_run:
        configs = tuple(cfg for cfg in EXPERIMENT_CONFIGS if cfg[0] == "delt")
    config_summaries: Dict[str, Any] = {}
    for config_name, diff_mode, filter_key, overrides in configs:
        config_dir = os.path.join(config_root, config_name)
        os.makedirs(config_dir, exist_ok=True)
        include_added_callees = bool(
            overrides.get("include_added_callees", base_opts.get("include_added_callees", True))
        )
        config_summary: Dict[str, Any] = {
            "model": base_opts.get("model"),
            "diff_mode": diff_mode,
            "filter_mode": "NONE" if not filter_key else filter_key,
            "include_added_callees": include_added_callees,
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
            # gt_only restricts triage to the ground-truth function, which only exists for
            # the backdoored set. Force it off everywhere else so safe/openwrt triage every
            # filtered function and their false-positive counts stay complete.
            run_opts["gt_only"] = gt_only and category == "backdoored"
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


def run_drift(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Run only the structural drift stage over the backdoored and safe pairs, no LLM.

    Use this before `run_experiments` to see the search space each comparison produces
    and to work out ground truth. Every filter policy is run (filter_OR, filter_AND, and
    filter_NONE), which is exactly the census `run_experiments` does at its root, so
    pointing this at the same --outdir means the full run reuses these results.

    Opts:
      backdoored   -- entries file of backdoored target,baseline pairs
      safe         -- entries file of safe target,baseline pairs
      ground_truth -- optional ground-truth JSON; when given, each candidate row is
                      marked with whether it matches a ground-truth target
      outdir       -- root output directory (default: out/delt_experiments)

    Per comparison this writes drift_raw.json, stats.json, and candidate_functions.json
    (one row per filtered/excluded/added function with decimal + hex target address and
    the Ghidra function name). Each category also gets
    candidate_functions_by_sample.json, keyed by target collection name, which is the
    same key the ground-truth file uses.
    """
    backdoored_path: Optional[str] = opts.get("backdoored")
    safe_path: Optional[str] = opts.get("safe")
    gt_path: Optional[str] = opts.get("ground_truth")
    outdir = str(opts.get("outdir") or "out/delt_experiments")

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
    """Run the paper's full DeLT experiment matrix using the `delt` analyzer.

    Required/expected opts:
      backdoored   -- entries file of backdoored target,baseline pairs
      ground_truth -- ground-truth JSON for the backdoored pairs

    Model selection:
      model        -- a single model tag passed through to the delt analyzer
      models       -- a models file (like models.txt); each line is
                      one model tag.
                      Results for each model land under outdir/<model_slug>/.
      (neither)    -- dry run: only the deployed `delt` config runs, with triage
                      disabled, so each modified function gets its unified diff and the
                      agent's input files (outdir/delt/<category>/<pair>/filepair_NN/
                      modified_functions/<b..t..>/{diff.txt,agent_inputs/}) written to
                      disk without invoking the agent. Use this to author ground truth.

    Comparisons run one at a time against a single Ollama host.

    Optional opts:
      safe         -- entries file of safe target,baseline pairs
      openwrt      -- entries file of OpenWrt target,baseline pairs
      outdir       -- root output directory (default: out_delt_experiments)
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
    outdir = str(opts.get("outdir") or "out/delt_experiments")

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
    for model in model_specs:
        base_opts = dict(opts)
        base_opts["model"] = model
        # Dry run: disable triage so the analyzer only produces per-function diffs and
        # agent inputs. No model client is built.
        base_opts["no_triage"] = dry_run
        config_root = os.path.join(outdir, _model_slug(model)) if nested else outdir
        os.makedirs(config_root, exist_ok=True)

        if dry_run:
            logger.info("running dry-run (no triage) to produce triage inputs")
        else:
            logger.info("running experiment configs for model %s", model)

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
