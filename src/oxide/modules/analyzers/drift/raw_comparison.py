from typing import Any, Dict, List, Tuple

from oxide.core import api

from oxide.modules.analyzers.drift.cache import comparison_cache_key, get_or_compute
from oxide.modules.analyzers.drift.classify import build_function_diffs
from oxide.modules.analyzers.drift.constants import NAME


def resolve_collection_pair(oid_list: List[str]) -> Tuple[str, str]:
    if len(oid_list) < 2:
        raise ValueError("drift requires two collection OIDs: [target_oid, baseline_oid]")

    valid, invalid = api.valid_oids(oid_list[:2])
    if len(valid) < 2:
        raise ValueError(f"Invalid collections: {invalid}")
    return valid[0], valid[1]


def build_raw_comparison(target_oid: str, baseline_oid: str) -> Dict[str, Any]:
    def compute() -> Dict[str, Any]:
        pair_files_results = api.retrieve("pair_files", [target_oid, baseline_oid]) or {}
        return {
            "PAIR_FILES_RESULTS": pair_files_results,
            "FUNCTION_DIFFS": build_function_diffs(pair_files_results),
        }

    cache_key = comparison_cache_key(target_oid, baseline_oid)
    return get_or_compute(NAME, cache_key, compute)
