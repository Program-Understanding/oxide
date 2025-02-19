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

opts_doc = {"functionA": {"type": str, "mangle": True, "default": "None"},
            "functionB": {"type": str, "mangle": True, "default": "None"}
}

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

    # Retrieve ACFGs for both files
    fileA = oid_list[0]
    fileA_acfg = api.retrieve("acfg", fileA)

    fileB = oid_list[1]
    fileB_acfg = api.retrieve("acfg", fileB)

    A_unique_funcs, A_repeated_funcs = get_unique_functions(fileA)
    B_unique_funcs, B_repeated_funcs = get_unique_functions(fileB)

    matched_funcs, matched_A, matched_B = pair_matched_functions(A_unique_funcs, B_unique_funcs)

    for m in matched_A:
        if m in fileA_acfg:
            del fileA_acfg[m]

    for r in A_repeated_funcs:
        if r in fileA_acfg:
            del fileA_acfg[r]

    for m in matched_B:
        if m in fileB_acfg:
            del fileB_acfg[m]

    for r in B_repeated_funcs:
        if r in fileB_acfg:
            del fileB_acfg[r]

    if len(fileA_acfg) > 0 and len(fileB_acfg) > 0:
        modified_funcs, added_funcs, removed_funcs = pair_modified_functions(fileA, fileA_acfg, fileB, fileB_acfg)
    else:
        modified_funcs = {}
        unmatched = {}
        added_funcs = {}
        removed_funcs = {}
        # Probably need to fix this at somepoint

    result = {
        'matched_funcs': matched_funcs,
        'modified_funcs': modified_funcs,
        'unmatched_funcs': added_funcs
    }

    return result

def get_unique_functions(file):
    unique_funcs = {}
    repeated_funcs = []

    # Retrieve functions from fileA and group by tlsh hash.
    funcs = api.retrieve("function_tlsh", file, {"replace_addrs": True})
    func_hashes = {}
    for f in funcs:
        hash_val = funcs[f].get('tlsh hash')
        if hash_val:
            func_hashes.setdefault(hash_val, []).append((f, funcs[f]))
        else:
            # Probably need to figure out how we want to handle these types of functions
            # Functions that were to small to get a hash
            repeated_funcs.append(f)

    # Only keep unique tlsh hash entries for fileA.
    for hash_val, funcs in func_hashes.items():
        if len(funcs) == 1:
            unique_funcs[funcs[0][0]] = funcs[0][1]
        else:
            for f in funcs:
                repeated_funcs.append(f[0])
    return unique_funcs, repeated_funcs

def pair_matched_functions(A_unique_funcs, B_unique_funcs):
    results = {}
    matched_A = []
    matched_B = []

    B_hashes = {}
    for func in B_unique_funcs:
        B_hashes[B_unique_funcs[func]['tlsh hash']] = func

    # Pair functions only if the hash is unique in both files.
    for func in A_unique_funcs:
        if A_unique_funcs[func]['tlsh hash'] in B_hashes:
            A_addr = func
            A_data = A_unique_funcs[func]
            B_addr = B_hashes[A_data['tlsh hash']]
            B_data = B_unique_funcs[B_addr]
            results[A_addr] = {
                'func_name': A_data.get('name'),
                'ref_func_name': B_data.get('name')
            }
            matched_A.append(A_addr)
            matched_B.append(B_addr)
    return results, matched_A, matched_B

def pair_modified_functions(fileA, fileA_vectors, fileB, fileB_vectors):
    """
    Matches functions from fileA to fileB using TLSH and cosine similarity with enhanced normalization,
    dynamic thresholding, and backup KNN matching.
    Handles files with different numbers of functions by explicitly tracking additions and removals.
    """
    paired_functions = {}
    added_functions = {}  # Functions in fileA that have no match in fileB
    removed_functions = {}  # Functions in fileB that have no match in fileA

    # Retrieve function TLSH hashes
    A_funcs = api.retrieve("function_tlsh", fileA, {"replace_addrs": True})
    B_funcs = api.retrieve("function_tlsh", fileB, {"replace_addrs": True})

    # Convert function vectors to matrix form for fast computation.
    # This extracts the function addresses (keys) and corresponding vectors.
    A_keys, A_matrix = zip(*fileA_vectors.items())
    B_keys, B_matrix = zip(*fileB_vectors.items())

    # Step 3: Normalize Vectors
    scaler = RobustScaler()
    A_matrix = scaler.fit_transform(A_matrix)
    B_matrix = scaler.transform(B_matrix)

    A_matrix = normalize(A_matrix, norm="l2")
    B_matrix = normalize(B_matrix, norm="l2")

    # Step 4: Compute Similarity
    sim_matrix = cosine_similarity(A_matrix, B_matrix)

    # Step 5: Compute Dynamic Similarity Threshold
    dynamic_threshold = compute_dynamic_threshold(sim_matrix)

    # Step 6: Hungarian Matching
    cost_matrix = 1 - sim_matrix
    row_ind, col_ind = linear_sum_assignment(cost_matrix)

    matched_A = set()
    matched_B = set()

    for i, j in zip(row_ind, col_ind):
        funcA, funcB = A_keys[i], B_keys[j]
        similarity = sim_matrix[i, j]

        if similarity >= dynamic_threshold:
            paired_functions[funcA] = {
                "matched_function": funcB,
                "similarity": similarity,
                "func_name": A_funcs[funcA]['name'],
                "ref_file": fileB,
                "ref_func_name": B_funcs[funcB]['name']
            }
            matched_A.add(funcA)
            matched_B.add(funcB)

    # Step 7: Identify Added & Removed Functions
    added_functions = {k: A_funcs[k] for k in A_keys if k not in matched_A}
    removed_functions = {k: B_funcs[k] for k in B_keys if k not in matched_B}

    return paired_functions, added_functions, removed_functions

def compute_dynamic_threshold(similarity_matrix):
    valid_scores = similarity_matrix[similarity_matrix >= 0]
    if valid_scores.size < 5:
        return 0.6  # Default fallback threshold

    q1 = np.percentile(valid_scores, 25)
    q3 = np.percentile(valid_scores, 75)
    iqr = q3 - q1

    return max(q1 - 1.5 * iqr, 0.4)  # Prevent threshold from dropping too low