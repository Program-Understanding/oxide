from typing import Any, Dict, Optional, Tuple

from oxide.modules.analyzers.drift.classify import filter_modified_by_rule


def summarize_file_classifications(pair_files_results: Dict[str, Any]) -> Dict[str, int]:
    """ Count files per pair_files category (matched, modified, added, removed). """
    return {category: len(oids) for category, oids in pair_files_results.items()}


def summarize_function_classifications(
    function_diffs: Dict[Tuple[str, str], Any],
    filter_rules: Optional[Dict[str, Any]] = None,
    filter_name: Optional[str] = None,
) -> Tuple[Dict[Tuple[str, str], Any], Dict[str, int]]:
    """ Reduce per-pair function classifications into per-file and total counts,
        optionally splitting out a named filter category from "modified".
    """
    per_file: Dict[Tuple[str, str], Any] = {}
    total_ut = total_ub = total_mat = total_mod = total_filt = 0

    if filter_rules and filter_name:
        function_diffs = filter_modified_by_rule(function_diffs, filter_rules, filter_name)

    for key, diff in function_diffs.items():
        fc = dict(diff["function_classification"])

        unmatched_target_count = len(fc.get("unmatched_target", []))
        unmatched_baseline_count = len(fc.get("unmatched_baseline", []))
        matched_count = len(fc.get("matched", []))
        modified_entries = list(fc.get("modified", []))
        filtered_entries = list(fc.get(filter_name, [])) if filter_name else []

        entry = {
            "unmatched_target": unmatched_target_count,
            "unmatched_baseline": unmatched_baseline_count,
            "matched": matched_count,
            "modified": modified_entries,
        }
        if filter_name:
            entry[filter_name] = filtered_entries
        per_file[key] = entry

        total_ut += unmatched_target_count
        total_ub += unmatched_baseline_count
        total_mat += matched_count
        total_mod += len(modified_entries)
        total_filt += len(filtered_entries)

    totals = {
        "unmatched_target": total_ut,
        "unmatched_baseline": total_ub,
        "matched": total_mat,
        "modified": total_mod,
    }
    if filter_name:
        totals[filter_name] = total_filt

    return per_file, totals
