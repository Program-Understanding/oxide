DESC = " This module pairs files via exact, name, and BinDiff tiers"
NAME = "pair_files"

import logging
from typing import Dict, Any, List, Set, Tuple
import numpy as np
from scipy.optimize import linear_sum_assignment
from oxide.core import api, progress

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
    baseline_cid = collection_list[1]
    target_oids = set(api.expand_oids(target_cid))
    baseline_oids = set(api.expand_oids(baseline_cid))

    # Split executables vs non-executables
    target_exes, target_non = separate_oids(list(target_oids))
    baseline_exes, baseline_non = separate_oids(list(baseline_oids))
    
    # Tier 0: Exact matches
    exact_exes = target_exes & baseline_exes
    rem_t_exes = target_exes - exact_exes
    rem_b_exes = baseline_exes - exact_exes

    # Tier 1: Name-based filename matching
    name_exes, rem_t_exes, rem_b_exes = match_by_filename(rem_t_exes, rem_b_exes)

    # Tier 2A: Name-tier BinDiff
    name_bindiff: Dict[Tuple[str, str], Dict[str, Any]] = {}
    print("BINDIFF FOR FILE NAME MATCHES")
    p = progress.Progress(len(name_exes))
    for t_oid, b_oid in name_exes.items():
        try:
            diff = api.retrieve("bindiff", [t_oid, b_oid]) or {}
        except Exception as e:
            logger.error(f"BinDiff failed on name match {t_oid},{b_oid}: {e}")
            diff = {}
        name_bindiff[(t_oid, b_oid)] = {
            "baseline_oid": b_oid,
            "method": "name",
            "diff": diff
        }
        p.tick()

    # Tier 2B: BinDiff on remaining executables
    bindiff_exes = match_by_bindiff(rem_t_exes, rem_b_exes)

    # Build matched and modified executables
    matched_exes = {
        oid: {"baseline_oid": oid, "method": "exact"}
        for oid in exact_exes
    }
    modified_exes = {**name_bindiff, **bindiff_exes}

    # Compute removed executables
    matched_b_exes = (
        exact_exes
        | set(name_exes.values())
        | {info["baseline_oid"] for info in bindiff_exes.values()}
    )
    removed_exes = list(baseline_exes - matched_b_exes)

    # Compute unmatched target executables
    matched_t_exes = (
        exact_exes
        | set(name_exes.keys())
        | {t for (t, _) in bindiff_exes.keys()}
    )
    unmatched_t_exes = list(target_exes - matched_t_exes)

    # Non-executables: exact matching then filename-based modification matching
    exact_non = target_non & baseline_non
    matched_non = {
        oid: {"baseline_oid": oid, "method": "exact"}
        for oid in exact_non
    }
    rem_t_non = target_non - exact_non
    rem_b_non = baseline_non - exact_non

    name_non, rem_t_non, rem_b_non = match_by_filename(rem_t_non, rem_b_non)
    modified_non = {
        t: {"baseline_oid": b, "method": "name"}
        for t, b in name_non.items()
    }
    unmatched_t_non = list(rem_t_non - set(name_non.keys()))
    used_b_non = set(name_non.values())
    unmatched_b_non = list(rem_b_non - used_b_non)

    return {
        "MATCHED_EXECUTABLES": matched_exes,
        "MODIFIED_EXECUTABLES": modified_exes,
        "UNMATCHED_TARGET_EXECUTABLES": unmatched_t_exes,
        "UNMATCHED_BASELINE_EXECUTABLES": removed_exes,
        "MATCHED_NON_EXECUTABLES": matched_non,
        "MODIFIED_NON_EXECUTABLES": modified_non,
        "UNMATCHED_TARGET_NON_EXECUTABLES": unmatched_t_non,
        "UNMATCHED_BASELINE_NON_EXECUTABLES": unmatched_b_non
    }

def match_by_filename(
    target_set: Set[str], baseline_set: Set[str]
) -> Tuple[Dict[str, str], Set[str], Set[str]]:
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

def match_by_bindiff(target_set: Set[str], baseline_set: Set[str]) -> Dict[Tuple[str, str], Dict[str, Any]]:
    """Run full BinDiff on each pair and return matches with their diffs."""
    if not target_set or not baseline_set:
        return {}
    t_list, b_list = list(target_set), list(baseline_set)

    raw_diffs: Dict[Tuple[str, str], Any] = {}
    scores: Dict[Tuple[str, str], float] = {}
    print("MATCH BY BINDIFF")
    p = progress.Progress(len(t_list))
    for t in t_list:
        for b in b_list:
            try:
                diff = api.retrieve("bindiff", [t, b]) or {}
            except Exception as e:
                logger.error(f"BinDiff failed for {t},{b}: {e}")
                diff = {}
            raw_diffs[(t, b)] = diff
            scores[(t, b)] = diff.get("file_stats", {}).get("similarity", 0.0)
        p.tick()

    M = max(len(t_list), len(b_list))
    cost = np.full((M, M), 1e6)
    t_pad = t_list + [f"DUMMY_T_{i}" for i in range(M - len(t_list))]
    b_pad = b_list + [f"DUMMY_B_{i}" for i in range(M - len(b_list))]
    for i, t in enumerate(t_pad):
        for j, b in enumerate(b_pad):
            cost[i, j] = (1e6 if t.startswith("DUMMY") or b.startswith("DUMMY") else -scores.get((t, b), 0.0))

    rows, cols = linear_sum_assignment(cost)
    matched: Dict[Tuple[str, str], Dict[str, Any]] = {}
    for i, j in zip(rows, cols):
        t, b = t_pad[i], b_pad[j]
        if t in target_set and b in baseline_set:
            matched[(t, b)] = {
                "baseline_oid": b,
                "method": "bindiff",
                "diff": raw_diffs[(t, b)]
            }
    return matched

def separate_oids(oids: List[str]) -> Tuple[Set[str], Set[str]]:
    """Categorize by executability."""
    exes, non_ex = set(), set()
    for oid in oids:
        cat = api.get_field("categorize", oid, oid)
        if cat == "executable":
            exes.add(oid)
        else:
            non_ex.add(oid)
    return exes, non_ex
