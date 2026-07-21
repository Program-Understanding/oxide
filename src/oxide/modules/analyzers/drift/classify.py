import logging
from typing import Any, Dict, Tuple

from oxide.core import api, progress

from oxide.modules.analyzers.drift.cache import function_diff_cache_key, get_or_compute
from oxide.modules.analyzers.drift.constants import NAME
from oxide.modules.analyzers.drift.types import FileDiffRecord, FunctionClassification

logger = logging.getLogger(NAME)


def build_function_diffs(pair_files_results: Dict[str, Any]) -> Dict[Tuple[str, str], FileDiffRecord]:
    """ Classify functions for every modified file pair reported by pair_files. """
    modified = pair_files_results.get("MODIFIED_EXECUTABLES", {})
    diffs: Dict[Tuple[str, str], FileDiffRecord] = {}

    p = progress.Progress(len(modified.items()))
    for (target_oid, baseline_oid), info in modified.items():
        cache_key = function_diff_cache_key(target_oid, baseline_oid)
        fc = get_or_compute(
            NAME, cache_key, lambda: classify_function_diffs(target_oid, baseline_oid, info.get("diff", {}))
        )

        diffs[(target_oid, baseline_oid)] = {
            "filenames": {
                "target": api.get_names_from_oid(target_oid),
                "baseline": api.get_names_from_oid(baseline_oid),
            },
            "function_classification": fc,
        }
        p.tick()
    return diffs


def classify_function_diffs(target_oid: str, baseline_oid: str, bindiff_full: Dict[str, Any]) -> FunctionClassification:
    """ Classify one file pair's functions into unmatched/matched/modified using BinDiff similarity. """
    func_matches = bindiff_full.get("function_matches", {})
    ranked_pairs = sorted(func_matches.items(), key=lambda kv: kv[1]["similarity"])
    rank_map = {key: idx + 1 for idx, (key, _) in enumerate(ranked_pairs)}

    unmatched_target = list(bindiff_full.get("unmatched_primary", []))
    unmatched_baseline = list(bindiff_full.get("unmatched_secondary", []))
    matched = []
    modified = []

    funcs_target = api.get_field("ghidra_disasm", target_oid, "functions") or {}
    funcs_baseline = api.get_field("ghidra_disasm", baseline_oid, "functions") or {}

    name_target = {off: meta.get("name") for off, meta in funcs_target.items()}
    name_baseline = {off: meta.get("name") for off, meta in funcs_baseline.items()}

    p = progress.Progress(len(func_matches.items()))
    for (addr_target, addr_baseline), match_info in func_matches.items():
        similarity = match_info["similarity"]
        info = {
            "name_target_func": name_target.get(addr_target),
            "name_baseline_func": name_baseline.get(addr_baseline),
            "bindiff_similarity": similarity,
            "bindiff_ranking": rank_map[(addr_target, addr_baseline)],
        }
        if similarity >= 1.0:
            matched.append((addr_target, addr_baseline))
        else:
            features = api.retrieve(
                "function_diff_features",
                [target_oid, baseline_oid],
                {"target": addr_target, "baseline": addr_baseline},
            ) or {}
            modified.append({"pair": (addr_target, addr_baseline), "features": features, "info": info})
        p.tick()

    return {
        "unmatched_target": unmatched_target,
        "unmatched_baseline": unmatched_baseline,
        "matched": matched,
        "modified": modified,
    }


def filter_modified_by_rule(function_diffs: Dict[Tuple[str, str], Any], filter_rules: Any, filter_name: str) -> Dict[Tuple[str, str], Any]:
    """ Split each pair's "modified" functions into those that satisfy filter_rules
        (moved under filter_name) and those that don't (left in "modified").
    """
    if isinstance(filter_rules, dict):
        and_keys = filter_rules.get("and", []) or []
        or_keys = filter_rules.get("or", []) or []
    elif isinstance(filter_rules, (list, tuple, set)):
        and_keys, or_keys = [], list(filter_rules)
    else:
        raise ValueError("feature_rules must be a list or dict with 'and'/'or' keys")

    def _any_nonzero(keys, feats):
        if isinstance(keys, (list, tuple, set)):
            return any(_any_nonzero(k, feats) for k in keys)
        return feats.get(keys, 0) != 0

    def entry_pass(entry):
        feats = entry.get("features", {})

        if and_keys and not all(_any_nonzero(k, feats) for k in and_keys):
            return False

        if or_keys and not any(feats.get(k, 0) != 0 for k in or_keys):
            return False

        return True

    filtered = {}
    for key, diff in function_diffs.items():
        fc = dict(diff["function_classification"])

        passed, remaining = [], []
        for item in fc.get("modified", []):
            (passed if entry_pass(item) else remaining).append(item)
        fc["modified"] = remaining
        fc[filter_name] = passed

        filtered[key] = {
            **diff,
            "function_classification": fc,
        }
    return filtered
