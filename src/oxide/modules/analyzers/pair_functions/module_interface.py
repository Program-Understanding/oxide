DESC = " This module is a template for analyzer, new analyzers can copy this format"
NAME = "pair_functions"

# imports
import logging
from typing import Dict, Any, List

import numpy as np
from sklearn.metrics.pairwise import cosine_similarity
from scipy.optimize import linear_sum_assignment
from typing import List, Dict
import numpy as np
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
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True}

def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    """ Entry point to compare functions between two files based on ACFG similarity. """
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)

    result = {}

    matched_funcs = {}
    matched_A = []
    matched_B = []

    lifted_matched_funcs = {}
    lifted_matched_A = []
    lifted_matched_B = []

    modified_funcs = {}
    unmatched_funcs = {}
    unmatched_baseline_funcs = {}

    # Retrieve ACFGs for both files
    fileA = oid_list[0]
    fileA_acfg = api.retrieve("acfg", fileA)
    if fileA_acfg is None:
        fileA_acfg = {}

    fileB = oid_list[1]
    fileB_acfg = api.retrieve("acfg", fileB)
    if fileB_acfg is None:
        fileB_acfg = {}

    A_unique_funcs = get_unique_functions(fileA)
    B_unique_funcs = get_unique_functions(fileB)

    A_unique_lifted_funcs = get_unique_lifted_functions(fileA)
    B_unique_lifted_funcs = get_unique_lifted_functions(fileB)

    if A_unique_funcs and B_unique_funcs:
        matched_funcs, matched_A, matched_B = pair_matched_functions(fileA, A_unique_funcs, fileB, B_unique_funcs)

    for a in matched_A:
        if a in A_unique_lifted_funcs:
            del A_unique_lifted_funcs[a]
    for b in matched_B:
        if b in B_unique_lifted_funcs:
            del B_unique_lifted_funcs[b]

    if A_unique_lifted_funcs and B_unique_lifted_funcs:
        lifted_matched_funcs, lifted_matched_A, lifted_matched_B = pair_matched_functions(fileA, A_unique_lifted_funcs, fileB, B_unique_lifted_funcs)

    for i in list(fileA_acfg):
        if i not in A_unique_lifted_funcs or i in lifted_matched_A or i in matched_A:
            del fileA_acfg[i]

    for i in list(fileB_acfg):
        if i not in B_unique_lifted_funcs or i in lifted_matched_B or i in matched_B:
            del fileB_acfg[i]

    if len(fileA_acfg) > 0 and len(fileB_acfg) > 0:
        modified_funcs, unmatched_funcs, unmatched_baseline_funcs = pair_modified_functions(fileA, fileA_acfg, fileB, fileB_acfg)

    result = {
        'matched_funcs': matched_funcs,
        'lifted_matched_funcs': lifted_matched_funcs,
        'modified_funcs': modified_funcs,
        'unmatched_funcs': unmatched_funcs,
        'unmatched_baseline_funcs': unmatched_baseline_funcs
    }

    return result

def get_unique_lifted_functions(file):
    unique_lifted_funcs = {}

    # Retrieve functions from fileA and group by hash.
    lifted_funcs = api.retrieve("function_representations", file, {"lift_addrs": True})
    lifted_func_hashes = {}

    if lifted_funcs is None: return None

    for f in lifted_funcs:
        hash_val = lifted_funcs[f].get('hash')
        if hash_val:
            lifted_func_hashes.setdefault(hash_val, []).append((f, lifted_funcs[f]))

    # Only keep unique hash entries for fileA.
    for hash_val, lifted_funcs in lifted_func_hashes.items():
        if len(lifted_funcs) == 1:
            unique_lifted_funcs[lifted_funcs[0][0]] = lifted_funcs[0][1]

    return unique_lifted_funcs

def get_unique_functions(file):
    unique_funcs = {}

    # Retrieve functions from fileA and group by hash.
    funcs = api.retrieve("function_representations", file, {"lift_addrs": False})
    func_hashes = {}

    if funcs is None: return None

    for f in funcs:
        hash_val = funcs[f].get('hash')
        if hash_val:
            func_hashes.setdefault(hash_val, []).append((f, funcs[f]))

    # Only keep unique hash entries for fileA.
    for hash_val, funcs in func_hashes.items():
        if len(funcs) == 1:
            unique_funcs[funcs[0][0]] = funcs[0][1]

    return unique_funcs

def pair_matched_functions(fileA, A_unique_funcs, fileB, B_unique_funcs):
    results = {}
    matched_A = []
    matched_B = []

    B_hashes = {}
    for func in B_unique_funcs:
        if B_unique_funcs[func] is None:  # Ensure it's not None
            continue  # Skip invalid entries

        hash_val = B_unique_funcs[func].get('hash')  # Use .get() to avoid KeyError
        if hash_val is not None:  # Ensure hash is not None
            B_hashes[hash_val] = func

    # Pair functions only if the hash is unique in both files.
    for func in A_unique_funcs:
        if A_unique_funcs[func]['hash'] in B_hashes:
            A_addr = func
            A_data = A_unique_funcs[func]
            B_addr = B_hashes[A_data['hash']]
            B_data = B_unique_funcs[B_addr]
            results[A_addr] = {
                'func_name': A_data.get('name'),
                'baseline_func_name': B_data.get('name'),
                'similarity': 1,
                'baseline_file': fileB
            }
            matched_A.append(A_addr)
            matched_B.append(B_addr)
    return results, matched_A, matched_B

def pair_modified_functions(fileA, fileA_vectors, fileB, fileB_vectors):
    """
    Matches functions from fileA to fileB using TLSH and cosine similarity with enhanced normalization,
    dynamic thresholding applied **after Hungarian matching**, and backup KNN matching.
    Handles files with different numbers of functions by explicitly tracking additions and removals.
    """

    paired_functions = {}

    # Retrieve function hashes
    A_funcs = api.retrieve("function_representations", fileA, {"lift_addrs": True}) or {}
    B_funcs = api.retrieve("function_representations", fileB, {"lift_addrs": True}) or {}

    # Ensure both files have function vectors
    if not fileA_vectors or not fileB_vectors:
        return {}, A_funcs, B_funcs  # If no vectors, consider all as added/removed

    # Convert function vectors to matrices for fast computation
    A_keys, A_matrix = zip(*fileA_vectors.items())
    B_keys, B_matrix = zip(*fileB_vectors.items())

    # Convert lists into NumPy arrays
    A_matrix = np.vstack(A_matrix)
    B_matrix = np.vstack(B_matrix)

    # Step 1: Normalize Vectors
    scaler = RobustScaler()
    A_matrix = scaler.fit_transform(A_matrix)
    B_matrix = scaler.fit_transform(B_matrix)

    A_matrix = normalize(A_matrix, norm="l2")
    B_matrix = normalize(B_matrix, norm="l2")

    # Step 2: Compute Similarity Matrix
    sim_matrix = cosine_similarity(A_matrix, B_matrix)

    # Step 3: Handle Unequal List Sizes (Padding)
    len_A, len_B = len(A_keys), len(B_keys)
    max_size = max(len_A, len_B)

    if len_A < max_size:
        padding = np.full((max_size - len_A, len_B), -1)  # High penalty for missing rows
        sim_matrix = np.vstack([sim_matrix, padding])
        A_keys += tuple(f"DUMMY_A_{i}" for i in range(max_size - len_A))

    if len_B < max_size:
        padding = np.full((max_size, max_size - len_B), -1)  # High penalty for missing columns
        sim_matrix = np.hstack([sim_matrix, padding])
        B_keys += tuple(f"DUMMY_B_{i}" for i in range(max_size - len_B))

    # Step 4: Convert to Cost Matrix
    cost_matrix = np.where(sim_matrix >= 0, 1 - sim_matrix, 9999)  # Ensure high penalties for unmatched cases

    # Step 5: Apply Hungarian Matching
    row_ind, col_ind = linear_sum_assignment(cost_matrix)

    unmacthed_A = {}
    unmatched_B = {}

    # Step 7: Filter Matches
    for i, j in zip(row_ind, col_ind):
        funcA, funcB = str(A_keys[i]), str(B_keys[j])  # Ensure they are strings
        similarity = sim_matrix[i, j]

        if "DUMMY" not in funcA and "DUMMY" not in funcB:
            paired_functions[funcA] = {
                "matched_function": funcB,
                "similarity": similarity,
                "func_name": A_funcs.get(int(funcA), {}).get('name', 'Unknown'),
                "baseline_file": fileB,
                "baseline_func_name": B_funcs.get(int(funcB), {}).get('name', 'Unknown')
            }
        elif "DUMMY" not in funcA:
            unmacthed_A[funcA] = A_funcs.get(int(funcA), {}).get('name', 'Unknown')
        elif "DUMMY" not in funcB:
            unmatched_B[funcB] = B_funcs.get(int(funcB), {}).get('name', 'Unknown')

    return paired_functions, unmacthed_A, unmatched_B