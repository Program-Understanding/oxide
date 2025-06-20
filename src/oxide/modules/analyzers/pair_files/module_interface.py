DESC = " This module pairs files via exact, name, and BinDiff tiers"
NAME = "pair_files"

import logging
from typing import Dict, Any, List, Set
import numpy as np
from scipy.optimize import linear_sum_assignment
from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

def documentation() -> Dict[str, Any]:
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": True,
        "atomic": True
    }

def results(collection_list: List[str], opts: dict) -> Dict[str, Any]:
    """Categorize files, returning full BinDiff results for each modified executable."""
    # Expand collections
    target_cid = collection_list[0]
    baseline_cid = collection_list[1] if len(collection_list) > 1 else None
    target_oids = set(api.expand_oids(target_cid))
    baseline_oids = set(api.expand_oids(baseline_cid)) if baseline_cid else set()

    # Split executables vs non-executables
    target_exes, target_non = separate_oids(list(target_oids))
    baseline_exes, baseline_non = separate_oids(list(baseline_oids))

    # Tier 0: Exact matches
    exact_exes = target_exes & baseline_exes
    rem_t_exes = target_exes - exact_exes
    rem_b_exes = baseline_exes - exact_exes

    # Name-based filename matching
    name_exes, rem_t_exes, rem_b_exes = match_by_filename(rem_t_exes, rem_b_exes)

    # Tier 2A: Retrieve full BinDiff diff for name-matched
    name_bindiff: Dict[str, Any] = {}
    for t_oid, b_oid in name_exes.items():
        try:
            diff = api.retrieve("bindiff", [t_oid, b_oid]) or {}
        except Exception as e:
            logger.error(f"BinDiff failed on name match {t_oid},{b_oid}: {e}")
            diff = {}
        name_bindiff[(t_oid, b_oid)] = {
            "method": "name",
            "diff": diff
        }

    # Tier 2B: BinDiff on remaining executables
    bindiff_exes = match_by_bindiff(rem_t_exes, rem_b_exes)

    # Combine both sets of BinDiff results
    modified_exes = {**name_bindiff, **bindiff_exes}

    # Exact-only matched executables
    matched_exes = {
        oid: {"baseline_oid": oid, "method": "exact"}
        for oid in exact_exes
    }

    # Non-executables: exact matching then filename-based modification matching
    # 1) Exact matches
    exact_non = target_non & baseline_non
    matched_non = {
        oid: {"baseline_oid": oid, "method": "exact"}
        for oid in exact_non
    }

    # 2) Remove exact matches from consideration
    remaining_t_non = target_non - exact_non
    remaining_b_non = baseline_non - exact_non

    # 3) Filename-based modified non-executables on remainders
    name_non, rem_t_non, rem_b_non = match_by_filename(remaining_t_non, remaining_b_non)
    modified_non = {
        t: {"baseline_oid": b, "method": "name"}
        for t, b in name_non.items()
    }

    # 4) Any left in rem_t_non or rem_b_non are unmatched
    unmatched_t_non = rem_t_non
    unmatched_b_non = rem_b_non

    # Unmatched executables
    unmatched_t_exes = list(rem_t_exes - set(bindiff_exes.keys()))
    used_b = set(name_exes.values()) | {info["baseline_oid"] for info in bindiff_exes.values()}
    unmatched_b_exes = list(rem_b_exes - used_b)

    # Unmatched non-executables
    unmatched_t_non = list(rem_t_non - set(name_non.keys()))
    used_b_non = (target_non & baseline_non) | set(name_non.values())
    unmatched_b_non = list(rem_b_non - used_b_non)

    return {
        "MODIFIED_EXECUTABLES": modified_exes,
        "MATCHED_EXECUTABLES": matched_exes,
        "MODIFIED_NON_EXECUTABLES": modified_non,
        "MATCHED_NON_EXECUTABLES": matched_non,
        "UNMATCHED_TARGET_EXECUTABLES": unmatched_t_exes,
        "UNMATCHED_BASELINE_EXECUTABLES": unmatched_b_exes,
        "UNMATCHED_TARGET_NON_EXECUTABLES": unmatched_t_non,
        "UNMATCHED_BASELINE_NON_EXECUTABLES": unmatched_b_non
    }

def match_by_filename(
    target_set: Set[str], baseline_set: Set[str]
) -> tuple[Dict[str, str], Set[str], Set[str]]:
    """Pair by overlapping filenames."""
    matched, rem_t, rem_b = {}, set(target_set), set(baseline_set)
    for t in list(target_set):
        t_names = set(api.get_names_from_oid(t) or [])
        for b in list(baseline_set):
            if t in rem_t and b in rem_b:
                b_names = set(api.get_names_from_oid(b) or [])
                if t_names & b_names:
                    matched[t] = b
                    rem_t.remove(t)
                    rem_b.remove(b)
                    break
    return matched, rem_t, rem_b

def match_by_bindiff(
    target_set: Set[str], baseline_set: Set[str]
) -> Dict[str, Dict[str, Any]]:
    """Run full BinDiff on each pair and return matches with their diffs."""
    if not target_set or not baseline_set:
        return {}
    t_list, b_list = list(target_set), list(baseline_set)

    # Collect raw diffs
    raw_diffs: Dict[tuple, Any] = {}
    scores: Dict[tuple, float] = {}
    for t in t_list:
        for b in b_list:
            try:
                diff = api.retrieve("bindiff", [t, b]) or {}
            except Exception as e:
                logger.error(f"BinDiff failed for {t},{b}: {e}")
                diff = {}
            raw_diffs[(t, b)] = diff
            scores[(t, b)] = diff.get("file_stats", {}).get("similarity", 0.0)

    # Hungarian assignment on negative similarity
    A, B = len(t_list), len(b_list)
    M = max(A, B)
    cost = np.full((M, M), 1e6)
    t_pad = t_list + [f"DUMMY_T_{i}" for i in range(M - A)]
    b_pad = b_list + [f"DUMMY_B_{i}" for i in range(M - B)]
    for i, t in enumerate(t_pad):
        for j, b in enumerate(b_pad):
            cost[i, j] = (1e6 if t.startswith("DUMMY") or b.startswith("DUMMY") else -scores.get((t, b), 0.0))

    rows, cols = linear_sum_assignment(cost)
    matched: Dict[str, Dict[str, Any]] = {}
    for i, j in zip(rows, cols):
        t, b = t_pad[i], b_pad[j]
        if t in target_set and b in baseline_set:
            matched[(t, b)] = {
                "baseline_oid": b,
                "method": "bindiff",
                "diff": raw_diffs[(t, b)]
            }
    return matched

def separate_oids(oids: List[str]) -> tuple[Set[str], Set[str]]:
    """Categorize by executability."""
    exes, non_ex = set(), set()
    for oid in oids:
        cat = api.get_field("categorize", oid, oid)
        if cat == "executable":
            exes.add(oid)
        else:
            non_ex.add(oid)
    return exes, non_ex
