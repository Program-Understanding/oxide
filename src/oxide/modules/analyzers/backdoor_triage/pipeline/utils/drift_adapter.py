"""Reshapes the `drift` analyzer's per-comparison output into the flat
{"file_pairs": [...]} structure this package's triage pipeline consumes,
grouping each comparison's modified/excluded/added functions by file pair.
"""

from typing import Any, Dict, List, Optional

from oxide.core import api

from oxide.modules.analyzers.backdoor_triage.pipeline.utils.text_utils import ensure_decimal_str


def _normalize_unmatched_target_ref(raw_item: Any) -> Optional[Dict[str, str]]:
    """ Normalize one of drift's raw unmatched_target entries (address under
        "address"/"addr"/"offset", or a bare address value) into this package's
        added_functions wire shape: {"address", "name"}.
    """
    if isinstance(raw_item, dict):
        addr = raw_item.get("address") or raw_item.get("addr") or raw_item.get("offset")
        name = raw_item.get("name")
    else:
        addr = raw_item
        name = None

    normalized_addr = ensure_decimal_str(addr)
    if not normalized_addr:
        return None
    return {"address": normalized_addr, "name": str(name or "")}


def build_drift_file_pairs(target_cid: str, baseline_cid: str, filter_val: Optional[str] = None) -> Dict[str, Any]:
    """ Call the `drift` analyzer once and reshape its output per file pair into
        modified_functions / excluded_functions / added_functions.

        drift's own filtering (drift.classify.filter_modified_by_rule) already
        partitions the pre-filter "modified" list into two disjoint sets: items
        that pass move under a key named after the filter, everything else stays
        under "modified". So when a filter is active, file_entry["modified"] IS
        the excluded set already -- no extra set-difference is needed to get it.
    """
    opts = {"filter": filter_val} if filter_val else {}
    drift_output = api.retrieve("drift", [target_cid, baseline_cid], opts) or {}
    per_file = (drift_output.get("FUNCTION_CLASSIFICATION") or {}).get("PER_FILE") or {}
    raw_function_diffs = drift_output.get("FUNCTION_DIFFS") or {}

    out: Dict[str, Any] = {"file_pairs": []}
    for file_key, file_entry in per_file.items():
        if not isinstance(file_key, (tuple, list)) or len(file_key) != 2:
            continue
        target_oid, baseline_oid = file_key

        if filter_val:
            search_space = file_entry.get(filter_val) or []
            excluded_functions = list(file_entry.get("modified") or [])
        else:
            search_space = file_entry.get("modified") or []
            excluded_functions = []

        modified_functions: List[Dict[str, Any]] = []
        for item in search_space:
            features = item.get("features", {}) if isinstance(item, dict) else {}
            pair = item.get("pair", [None, None]) if isinstance(item, dict) else [None, None]
            modified_functions.append(
                {
                    "target_func_addr": ensure_decimal_str(pair[0]) if len(pair) > 0 else None,
                    "baseline_func_addr": ensure_decimal_str(pair[1]) if len(pair) > 1 else None,
                    "features": features,
                }
            )

        raw_classification = (
            (raw_function_diffs.get((target_oid, baseline_oid)) or {}).get("function_classification") or {}
        )
        added_functions: List[Dict[str, Any]] = []
        for raw_item in raw_classification.get("unmatched_target", []):
            normalized = _normalize_unmatched_target_ref(raw_item)
            if normalized:
                added_functions.append(normalized)

        out["file_pairs"].append(
            {
                "baseline_oid": baseline_oid,
                "target_oid": target_oid,
                "modified_functions": modified_functions,
                "added_functions": added_functions,
                "excluded_functions": excluded_functions,
            }
        )
    return out
