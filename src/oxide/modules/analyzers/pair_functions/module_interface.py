DESC = ""
NAME = "pair_functions"

import logging
from typing import Dict, Any, List, Tuple, Set, Optional

import numpy as np
from sklearn.metrics.pairwise import cosine_similarity
from scipy.optimize import linear_sum_assignment
from sklearn.preprocessing import RobustScaler, normalize

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

def documentation() -> Dict[str, Any]:
    """ Documentation for this module
        private - Whether module shows up in help
        set - Whether this module accepts collections
        atomic - TBD
    """
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True
    }

def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    """
    Entry point to compare functions between two files.
    Returns a dict with five buckets:
      - matched_funcs
      - lifted_matched_funcs
      - modified_funcs
      - unmatched_baseline_funcs
      - unmatched_target_funcs

    Each bucket is itself a dict whose keys are (baseline_addr, target_addr),
    and whose values are dicts containing similarity, func_addr, func_name, and file
    for both baseline and target (None where unmatched).
    """
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    baseline_file, target_file = oid_list[0], oid_list[1]

    # Step A: Retrieve function representations
    funcs_baseline      = retrieve_funcs(baseline_file, lift_addrs=False)
    funcs_target        = retrieve_funcs(target_file,   lift_addrs=False)
    funcs_baseline_lift = retrieve_funcs(baseline_file, lift_addrs=True)
    funcs_target_lift   = retrieve_funcs(target_file,   lift_addrs=True)

    acfg_baseline = api.retrieve("acfg", baseline_file) or {}
    acfg_target   = api.retrieve("acfg",   target_file)   or {}

    # Step B: Unique-hash matching (no lift)
    matched_funcs, rem_b0, rem_t0 = unique_hash_match(
        baseline_file, funcs_baseline,
        target_file,   funcs_target
    )

    # Step C: Lifted-hash matching (only on leftovers from Step B)
    baseline_lift_candidates = {
        addr: funcs_baseline_lift[addr]
        for addr in rem_b0
        if addr in funcs_baseline_lift
    }
    target_lift_candidates = {
        addr: funcs_target_lift[addr]
        for addr in rem_t0
        if addr in funcs_target_lift
    }

    lifted_matched_funcs, rem_b1, rem_t1 = lifted_hash_match(
        baseline_file, baseline_lift_candidates,
        target_file,   target_lift_candidates
    )

    # Step D: ACFG matching on the addresses still remaining after lifted-match
    matched_baseline_lift_addrs = {b for (b, _) in lifted_matched_funcs.keys()}
    matched_target_lift_addrs   = {t for (_, t) in lifted_matched_funcs.keys()}

    still_rem_b = rem_b0 - matched_baseline_lift_addrs
    still_rem_t = rem_t0 - matched_target_lift_addrs

    modified_funcs, unmatched_baseline_funcs, unmatched_target_funcs = acfg_match(
        baseline_file,          acfg_baseline,        still_rem_b,
        funcs_baseline_lift,
        target_file,            acfg_target,          still_rem_t,
        funcs_target_lift
    )

    # Package final result
    return {
        "matched_funcs":            matched_funcs,
        "lifted_matched_funcs":     lifted_matched_funcs,
        "modified_funcs":           modified_funcs,
        "unmatched_baseline_funcs": unmatched_baseline_funcs,
        "unmatched_target_funcs":   unmatched_target_funcs
    }

def retrieve_funcs(file: str, lift_addrs: bool) -> Dict[str, Dict[str, Any]]:
    """
    Wrapper around api.retrieve("function_representations", …).
    Returns a dict mapping func_addr (as str) → { 'hash': str, 'name': str, … }.
    """
    return api.retrieve("function_representations", file, {"lift_addrs": lift_addrs}) or {}


def unique_hash_match(
    baseline_file: str,
    baseline_funcs: Dict[str, Dict[str, Any]],
    target_file:   str,
    target_funcs:   Dict[str, Dict[str, Any]]
) -> Tuple[
        Dict[Tuple[str,str], Dict[str, Any]],
        Set[str],  # remaining baseline addresses
        Set[str]   # remaining target addresses
    ]:
    """
    1) Group baseline_funcs by hash, keep only hashes that occur exactly once.
    2) Group target_funcs by hash, keep only unique.
    3) For each hash present in both with exactly one address each, match (b_addr, t_addr).
       Build matched[(b_addr, t_addr)] = { … }
    4) Return matched dict, plus sets of addresses that did NOT get matched.
    """
    # (a) Build hash → [baseline_addrs]
    hash_to_baseline: Dict[str, List[str]] = {}
    for addr, data in baseline_funcs.items():
        h = data.get("hash")
        if h is None:
            continue
        hash_to_baseline.setdefault(h, []).append(addr)

    # (b) Build hash → [target_addrs]
    hash_to_target: Dict[str, List[str]] = {}
    for addr, data in target_funcs.items():
        h = data.get("hash")
        if h is None:
            continue
        hash_to_target.setdefault(h, []).append(addr)

    matched: Dict[Tuple[str,str], Dict[str, Any]] = {}
    matched_baseline: Set[str] = set()
    matched_target:   Set[str] = set()

    # (c) For each hash present in both with exactly one addr each, match them
    for h, b_list in hash_to_baseline.items():
        t_list = hash_to_target.get(h)
        if not t_list or len(b_list) != 1 or len(t_list) != 1:
            continue
        b_addr = b_list[0]
        t_addr = t_list[0]
        matched[(b_addr, t_addr)] = {
            "similarity": 1.0,
            "baseline_file": baseline_file,
            "baseline_func_addr": b_addr,
            "baseline_func_name": baseline_funcs[b_addr].get("name"),
            "target_file": target_file,
            "target_func_addr": t_addr,
            "target_func_name": target_funcs[t_addr].get("name")
        }
        matched_baseline.add(b_addr)
        matched_target.add(t_addr)

    # (d) Compute remaining (unmatched) addresses
    rem_baseline = set(baseline_funcs.keys()) - matched_baseline
    rem_target   = set(target_funcs.keys())   - matched_target

    return matched, rem_baseline, rem_target


def lifted_hash_match(
    baseline_file: str,
    baseline_funcs_lift: Dict[str, Dict[str, Any]],
    target_file:   str,
    target_funcs_lift:   Dict[str, Dict[str, Any]]
) -> Tuple[
        Dict[Tuple[str,str], Dict[str, Any]],
        Set[str],  # remaining baseline addresses after lifted-match
        Set[str]   # remaining target addresses after lifted-match
    ]:
    """
    Same logic as unique_hash_match, but using lifted-address representations.
    Matches any hash that is unique in both lifted sets.
    """
    hash_to_baseline: Dict[str, List[str]] = {}
    for addr, data in baseline_funcs_lift.items():
        h = data.get("hash")
        if h is None:
            continue
        hash_to_baseline.setdefault(h, []).append(addr)

    hash_to_target: Dict[str, List[str]] = {}
    for addr, data in target_funcs_lift.items():
        h = data.get("hash")
        if h is None:
            continue
        hash_to_target.setdefault(h, []).append(addr)

    matched: Dict[Tuple[str,str], Dict[str, Any]] = {}
    matched_baseline: Set[str] = set()
    matched_target:   Set[str] = set()

    for h, b_list in hash_to_baseline.items():
        t_list = hash_to_target.get(h)
        if not t_list or len(b_list) != 1 or len(t_list) != 1:
            continue
        b_addr = b_list[0]
        t_addr = t_list[0]
        matched[(b_addr, t_addr)] = {
            "similarity": 1.0,
            "baseline_file": baseline_file,
            "baseline_func_addr": b_addr,
            "baseline_func_name": baseline_funcs_lift[b_addr].get("name"),
            "target_file": target_file,
            "target_func_addr": t_addr,
            "target_func_name": target_funcs_lift[t_addr].get("name")
        }
        matched_baseline.add(b_addr)
        matched_target.add(t_addr)

    rem_baseline = set(baseline_funcs_lift.keys()) - matched_baseline
    rem_target   = set(target_funcs_lift.keys())   - matched_target

    return matched, rem_baseline, rem_target


def acfg_match(
    baseline_file: str,
    baseline_acfg: Dict[str, np.ndarray],
    rem_baseline_addrs: Set[str],
    funcs_baseline_lift: Dict[str, Dict[str, Any]],
    target_file: str,
    target_acfg:   Dict[str, np.ndarray],
    rem_target_addrs: Set[str],
    funcs_target_lift: Dict[str, Dict[str, Any]]
) -> Tuple[
    Dict[Tuple[str,str], Dict[str, Any]],
    Dict[Tuple[Optional[str],Optional[str]], Dict[str, Any]],
    Dict[Tuple[Optional[str],Optional[str]], Dict[str, Any]]
]:
    """
    1) Build matrices only for the “remaining” baseline and target addresses.
    2) If either side is empty, mark all from the other side as unmatched.
    3) Otherwise, run:
         - Convert remaining addresses to lists: addrsA, addrsB
         - A_keys = tuple(str(addr) for addr in addrsA), A_matrix = np.vstack([baseline_acfg[a] for a in addrsA])
         - B_keys = tuple(str(addr) for addr in addrsB), B_matrix = np.vstack([target_acfg[b] for b in addrsB])
         - Normalize, cosine_similarity, pad to square, Hungarian.
    4) For each assignment (i,j):
         - If A_keys[i] or B_keys[j] is a DUMMY → unmatched entry.
         - Else → modified_funcs[(b_addr, t_addr)] with sim = sim_matrix[i,j].
    5) Anything in rem_baseline_addrs not matched → unmatched_baseline
       Anything in rem_target_addrs not matched → unmatched_target
    """
    modified_funcs: Dict[Tuple[str,str], Dict[str, Any]] = {}
    unmatched_baseline: Dict[Tuple[Optional[str],Optional[str]], Dict[str, Any]] = {}
    unmatched_target:   Dict[Tuple[Optional[str],Optional[str]], Dict[str, Any]] = {}

    # Step 1: Prepare lists of addresses (convert to strings for DUMMY checks)
    addrsA = [addr for addr in rem_baseline_addrs if addr in baseline_acfg]
    addrsB = [addr for addr in rem_target_addrs if addr in target_acfg]

    # If either is empty, mark the other side's remaining as unmatched
    if not addrsA or not addrsB:
        for b_addr in addrsA:
            b_name = funcs_baseline_lift.get(b_addr, {}).get("name")
            key = (b_addr, None)
            unmatched_baseline[key] = {
                "similarity": None,
                "baseline_file": baseline_file,
                "baseline_func_addr": b_addr,
                "baseline_func_name": b_name,
                "target_file": None,
                "target_func_addr": None,
                "target_func_name": None
            }
        for t_addr in addrsB:
            t_name = funcs_target_lift.get(t_addr, {}).get("name")
            key = (None, t_addr)
            unmatched_target[key] = {
                "similarity": None,
                "baseline_file": None,
                "baseline_func_addr": None,
                "baseline_func_name": None,
                "target_file": target_file,
                "target_func_addr": t_addr,
                "target_func_name": t_name
            }
        return modified_funcs, unmatched_baseline, unmatched_target

    # Step 2: Build NumPy matrices
    A_mat = np.vstack([baseline_acfg[addr] for addr in addrsA])
    B_mat = np.vstack([target_acfg[addr]   for addr in addrsB])

    # Normalize
    scaler = RobustScaler()
    A_norm = normalize(scaler.fit_transform(A_mat), norm="l2")
    B_norm = normalize(scaler.fit_transform(B_mat), norm="l2")

    sim_matrix = cosine_similarity(A_norm, B_norm)
    len_A, len_B = len(addrsA), len(addrsB)
    max_size = max(len_A, len_B)

    # Step 3: Pad with "-1" rows/columns if needed, and build keys
    A_keys = tuple(str(addr) for addr in addrsA)
    B_keys = tuple(str(addr) for addr in addrsB)

    if len_A < max_size:
        pad_rows = max_size - len_A
        sim_matrix = np.vstack([sim_matrix, np.full((pad_rows, len_B), -1.0)])
        A_keys = A_keys + tuple(f"DUMMY_A_{i}" for i in range(pad_rows))
    if len_B < max_size:
        pad_cols = max_size - len_B
        sim_matrix = np.hstack([sim_matrix, np.full((max_size, pad_cols), -1.0)])
        B_keys = B_keys + tuple(f"DUMMY_B_{i}" for i in range(pad_cols))

    cost_matrix = np.where(sim_matrix >= 0, 1.0 - sim_matrix, 9999.0)
    row_ind, col_ind = linear_sum_assignment(cost_matrix)

    matched_A: Set[str] = set()
    matched_B: Set[str] = set()

    # Step 4: Process each assignment
    for i, j in zip(row_ind, col_ind):
        keyA = A_keys[i]
        keyB = B_keys[j]

        # Both DUMMY: skip
        if keyA.startswith("DUMMY_A_") and keyB.startswith("DUMMY_B_"):
            continue

        # keyA is DUMMY → unmatched target
        if keyA.startswith("DUMMY_A_"):
            # Map keyB back to original address
            t_addr = addrsB[j]
            t_name = funcs_target_lift.get(t_addr, {}).get("name")
            unmatched_target[(None, t_addr)] = {
                "similarity": None,
                "baseline_file": None,
                "baseline_func_addr": None,
                "baseline_func_name": None,
                "target_file": target_file,
                "target_func_addr": t_addr,
                "target_func_name": t_name
            }
            matched_B.add(t_addr)
            continue

        # keyB is DUMMY → unmatched baseline
        if keyB.startswith("DUMMY_B_"):
            b_addr = addrsA[i]
            b_name = funcs_baseline_lift.get(b_addr, {}).get("name")
            unmatched_baseline[(b_addr, None)] = {
                "similarity": None,
                "baseline_file": baseline_file,
                "baseline_func_addr": b_addr,
                "baseline_func_name": b_name,
                "target_file": None,
                "target_func_addr": None,
                "target_func_name": None
            }
            matched_A.add(b_addr)
            continue

        # Real match: both keys are actual addresses (as strings)
        b_addr = addrsA[i]
        t_addr = addrsB[j]
        sim = float(sim_matrix[i, j])
        matched_A.add(b_addr)
        matched_B.add(t_addr)
        b_name = funcs_baseline_lift.get(b_addr, {}).get("name")
        t_name = funcs_target_lift.get(t_addr, {}).get("name")
        modified_funcs[(b_addr, t_addr)] = {
            "similarity": sim,
            "baseline_file": baseline_file,
            "baseline_func_addr": b_addr,
            "baseline_func_name": b_name,
            "target_file": target_file,
            "target_func_addr": t_addr,
            "target_func_name": t_name
        }

    # Step 5: Any remaining in addrsA not in matched_A → unmatched baseline
    for b_addr in addrsA:
        if b_addr not in matched_A:
            b_name = funcs_baseline_lift.get(b_addr, {}).get("name")
            unmatched_baseline[(b_addr, None)] = {
                "similarity": None,
                "baseline_file": baseline_file,
                "baseline_func_addr": b_addr,
                "baseline_func_name": b_name,
                "target_file": None,
                "target_func_addr": None,
                "target_func_name": None
            }

    # Any remaining in addrsB not in matched_B → unmatched target
    for t_addr in addrsB:
        if t_addr not in matched_B:
            t_name = funcs_target_lift.get(t_addr, {}).get("name")
            unmatched_target[(None, t_addr)] = {
                "similarity": None,
                "baseline_file": None,
                "baseline_func_addr": None,
                "baseline_func_name": None,
                "target_file": target_file,
                "target_func_addr": t_addr,
                "target_func_name": t_name
            }

    return modified_funcs, unmatched_baseline, unmatched_target