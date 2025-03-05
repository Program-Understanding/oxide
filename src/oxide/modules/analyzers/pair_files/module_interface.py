DESC = " This module is a template for analyzer, new analyzers can copy this format"
NAME = "pair_files"

# imports
import logging
from typing import Dict, Any, List
from collections import defaultdict

import numpy as np
from scipy.optimize import linear_sum_assignment
from typing import List, Dict
import numpy as np
import tlsh


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
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": True,
            "atomic": True}

def results(collection_list: List[str], opts: dict) -> Dict[str, dict]:
    """Temp"""
    logger.debug("process()")

    target_collection_cid = collection_list[0]
    target_collection_oids = api.expand_oids(target_collection_cid)
    baseline_collection_cid = collection_list[1]
    if baseline_collection_cid:
        baseline_collection_oids = api.expand_oids(baseline_collection_cid)
    else:
        baseline_collection_oids = {}

    result = {}

    target_collection_exes, target_collection_non_exes = separate_oids(target_collection_oids)

    if baseline_collection_oids:
        baseline_collection_exes, baseline_collection_non_exec = separate_oids(baseline_collection_oids)  
    else:       
        baseline_collection_oids = []
        baseline_collection_exes = []
        baseline_collection_non_exec = []

    matched_exes, uniq_target_exes, uniq_baseline_exes = file_matches(target_collection_exes, baseline_collection_exes)
    matched_non_exes, uniq_col_non_exes, uniq_baseline_non_exes = file_matches(target_collection_non_exes, baseline_collection_non_exec)
    matched_exes = get_num_funcs(matched_exes)
    modified_target_exes, unmatched_target_oids, failed_target_exes = classify_files(uniq_target_exes, uniq_baseline_exes)
    unmatched_target_oids = get_num_funcs(unmatched_target_oids)
    modified_target_exes = match_functions(modified_target_exes)
    result = {
        'MATCHED_EXECUTABLES': matched_exes,
        'MATCHED_NON_EXECUTABLES': matched_non_exes,
        'MODIFIED_EXECUTABLES': modified_target_exes,
        'UNMATCHED_EXECUTABLES': unmatched_target_oids,
        'UNMATCHED_NON_EXECUTABLES': uniq_col_non_exes,
        'FAILED_EXECUTABLES': failed_target_exes
    }

    return result

def pair_modified_functions(oid, modified_target_exes):
    """
    Identify modified functions by comparing them with baseline functions and 
    classify them based on their match scores.
    """
    baseline_oid = modified_target_exes[oid]['baseline_oid']

    print(baseline_oid)

    pair_results = api.retrieve("pair_functions", [oid, baseline_oid])
    modified_funcs = pair_results['modified_funcs']

    modified_target_exes[oid]['matched_funcs'] = pair_results['matched_funcs']
    modified_target_exes[oid]['modified_funcs'] = {}
    modified_target_exes[oid]['modified_operand_funcs'] = {}
    modified_target_exes[oid]['unmatched_funcs'] = pair_results['unmatched_funcs']
    modified_target_exes[oid]['unmatched_baseline_funcs'] = pair_results['unmatched_baseline_funcs']

    for func_addr, func in modified_funcs.items():
        diff_features = api.retrieve("function_diff_features", [oid, baseline_oid], {"functionA": func['func_name'], "functionB": func['baseline_func_name']})
        if all(feature_value == 0 for feature, feature_value in diff_features.items() if feature != 'modified_operand_instr'):
            modified_target_exes[oid]['modified_operand_funcs'][func_addr] = diff_features
            modified_target_exes[oid]['modified_operand_funcs'][func_addr]['func_name'] = func['func_name']
            modified_target_exes[oid]['modified_operand_funcs'][func_addr]['baseline_func_name'] = func['baseline_func_name']
            modified_target_exes[oid]['modified_operand_funcs'][func_addr]['similarity'] = func['similarity']
            modified_target_exes[oid]['modified_operand_funcs'][func_addr]['baseline_file'] = func['baseline_file']
            
        else:
            modified_target_exes[oid]['modified_funcs'][func_addr] = diff_features
            modified_target_exes[oid]['modified_funcs'][func_addr]['func_name'] = func['func_name']
            modified_target_exes[oid]['modified_funcs'][func_addr]['baseline_func_name'] = func['baseline_func_name']
            modified_target_exes[oid]['modified_funcs'][func_addr]['similarity'] = func['similarity']
            modified_target_exes[oid]['modified_funcs'][func_addr]['baseline_file'] = func['baseline_file']
    return modified_target_exes

def get_all_functions(oids):
    functions = []
    for oid in oids:
        funcs = api.retrieve("function_tlsh", oid)
        if funcs:
            functions += funcs
    return functions

def match_functions(modified_target_exes):
    oids = list(modified_target_exes.keys())
    for oid in oids:
        modified_target_exes = pair_modified_functions(oid, modified_target_exes)
    return modified_target_exes

def classify_files(uniq_target_exes, uniq_baseline_exes):
    """
    Pairs `oid` files with the best `baseline_oid` files based on TLSH similarity,
    handling different list sizes. Now excludes any file where DISASM == 'FAIL'.
    """

    modified_target_exes = {}
    unmatched_target_oids = set(uniq_target_exes)
    unmatched_baseline_oids = set(uniq_baseline_exes)
    failed_target_exes = []
    failed_baseline_exes = []

    # Convert sets to lists for indexing and cost-matrix alignment
    target_oid_list = list(uniq_target_exes)
    baseline_oid_list = list(uniq_baseline_exes)

    ########################################################################
    # STEP 0a: Remove all "FAIL" files from both lists before building the
    # similarity matrix. We record them in failed_exes.
    ########################################################################
    filtered_oid_list = []
    for oid in target_oid_list:
        disasm_result = api.retrieve('ghidra_disasm', oid)
        if disasm_result is None or disasm_result == {} or disasm_result["original_blocks"] == {}:
            failed_target_exes.append(oid)
        else:
            filtered_oid_list.append(oid)
            
    target_oid_list = filtered_oid_list

    filtered_baseline_oid_list = []
    for baseline_oid in baseline_oid_list:
        disasm_result = api.retrieve('ghidra_disasm', oid)
        if disasm_result is None or disasm_result == {} or disasm_result["original_blocks"] == {}:
            failed_baseline_exes.append(baseline_oid)
        else:
            filtered_baseline_oid_list.append(baseline_oid)
    baseline_oid_list = filtered_baseline_oid_list

    len_A, len_B = len(target_oid_list), len(baseline_oid_list)
    if len_A == 0 or len_B == 0:
        # If nothing remains, no pairing is possible
        return modified_target_exes, unmatched_target_oids, failed_target_exes

    ########################################################################
    # STEP 1: Retrieve TLSH Hashes for All Remaining Files.
    # Also drop files that do not have a valid TLSH.
    ########################################################################
    file_hashes = {}
    for oid in target_oid_list + baseline_oid_list:
        tlsh_hash = api.get_field("tlshash", oid, 'hash')
        if not tlsh_hash or tlsh_hash == "TNULL":
            # Record failures, remove them from the list
            failed_target_exes.append(oid)
            if oid in target_oid_list:
                target_oid_list.remove(oid)
            if oid in baseline_oid_list:
                baseline_oid_list.remove(oid)
            continue
        file_hashes[oid] = tlsh_hash

    # Recompute lengths after removing invalid TLSH files
    len_A, len_B = len(target_oid_list), len(baseline_oid_list)
    if not file_hashes or len_A == 0 or len_B == 0:
        return modified_target_exes, unmatched_target_oids, failed_target_exes

    ########################################################################
    # STEP 2: Build cost (distance) matrix based on TLSH diff
    ########################################################################
    similarity_matrix = np.full((len_A, len_B), 9999)  # Large finite padding
    for i, oid in enumerate(target_oid_list):
        for j, baseline_oid in enumerate(baseline_oid_list):
            hashA = file_hashes.get(oid)
            hashB = file_hashes.get(baseline_oid)
            if hashA and hashB:
                tlsh_distance = tlsh.diff(hashA, hashB)  # Lower = better match
                similarity_matrix[i, j] = tlsh_distance

    ########################################################################
    # STEP 3: Handle Unequal Lists in the Cost Matrix
    ########################################################################
    max_size = max(len_A, len_B)

    if len_A < max_size:
        padding = np.full((max_size - len_A, len_B), 9999)
        similarity_matrix = np.vstack([similarity_matrix, padding])
        target_oid_list += [f"DUMMY_A_{i}" for i in range(max_size - len_A)]

    if len_B < max_size:
        padding = np.full((max_size, max_size - len_B), 9999)
        similarity_matrix = np.hstack([similarity_matrix, padding])
        baseline_oid_list += [f"DUMMY_B_{i}" for i in range(max_size - len_B)]

    ########################################################################
    # STEP 4: Apply Hungarian (linear_sum_assignment) on the TLSH distance
    ########################################################################
    row_ind, col_ind = linear_sum_assignment(similarity_matrix)

    ########################################################################
    # STEP 5: Assign Matches
    ########################################################################
    for i, j in zip(row_ind, col_ind):
        oid = target_oid_list[i]
        baseline_oid = baseline_oid_list[j]
        best_score = similarity_matrix[i, j]

        if "DUMMY" not in oid and "DUMMY" not in baseline_oid:
            modified_target_exes[oid] = {
                "baseline_oid": baseline_oid,
                "similarity": best_score
            }
            unmatched_target_oids.discard(oid)
            unmatched_baseline_oids.discard(baseline_oid)
    return modified_target_exes, unmatched_target_oids, failed_target_exes

def file_matches(target_oids, baseline_oids):
    if target_oids and baseline_oids:
        matches = list(target_oids.intersection(baseline_oids))
        return matches, target_oids.difference(baseline_oids), baseline_oids.difference(target_oids)
    else:
        return [], target_oids, baseline_oids
    

def separate_uniq_repeated(oid_list: dict):
    # 1) Gather all functions from this list of OIDs
    func_to_oids = defaultdict(set)
    for oid in oid_list:
        funcs = api.retrieve("function_tlsh", oid)
        if funcs:
            for func in funcs:
                func_to_oids[func].add(oid)

    # 2) Build a results dict with "unique" / "repeated" per OID
    results = {}
    for oid in oid_list:
        results[oid] = {'funcs': {}, "rep_funcs": {}, "empty_funcs": {}}
        funcs = api.retrieve("function_tlsh", oid)
        if funcs:
            for func in funcs:
                if funcs[func]['tlsh hash'] != None:
                    if len(func_to_oids[func]) == 1:
                        results[oid]['funcs'][func] = funcs[func]
                    else:
                        results[oid]["rep_funcs"][func] = funcs[func]
                else:
                    results[oid]['empty_funcs'][func] = funcs[func]
    return results

def separate_oids(oids):
    executables, non_executables = set(), set()
    for oid in oids:
        file_category = api.get_field("categorize", oid, oid)
        if file_category == "executable":
            executables.add(oid)
        else:
            non_executables.add(oid)
    return executables, non_executables

def get_num_funcs(oids):
    results = {}
    for oid in oids:
        functions = api.get_field('ghidra_disasm', oid, "functions")
        if functions:
            results[oid] = {'Num_functions': len(functions)}
        else:
            results[oid] = 0
    return results