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
    # Get the target exe details and its associated baseline OID
    target_exe = modified_target_exes[oid]
    baseline_oid = target_exe['baseline_oid']

    # Retrieve function pairing results between the target and baseline
    pair_results = api.retrieve("pair_functions", [oid, baseline_oid])
    modified_funcs = pair_results['modified_funcs']
    lifted_matched = pair_results['lifted_matched_funcs']

    # Initialize keys in the target exe dictionary
    target_exe.update({
        'matched_funcs': pair_results['matched_funcs'],
        'lifted_matched_funcs': {},
        'structurally_modified_funcs': {},
        'operand_modified_funcs': {},
        'unmatched_funcs': pair_results['unmatched_funcs'],
        'unmatched_baseline_funcs': pair_results['unmatched_baseline_funcs']
    })

    # Helper to add function info along with its diff features into a target dictionary.
    def add_func_info(target_dict, func_addr, func, diff_features):
        target_dict[func_addr] = {
            **diff_features,
            'func_name': func['func_name'],
            'baseline_func_name': func['baseline_func_name'],
            'similarity': func['similarity'],
            'baseline_file': func['baseline_file']
        }

    # Process lifted matched functions
    for func_addr, func in lifted_matched.items():
        diff_features = api.retrieve("function_diff_features", [oid, baseline_oid], {"functionA": func['func_name'], "functionB": func['baseline_func_name']})
        # If all diff features are zero, consider the match as lifted
        if all(value == 0 for value in diff_features.values()):
            target_exe['lifted_matched_funcs'][func_addr] = func
        else:
            # NOTE: In the original code, func was wrapped in a list. Here we assume a dict is expected.
            modified_funcs[func_addr] = func

    # Process modified functions to classify them into operand or structurally modified.
    for func_addr, func in modified_funcs.items():
        diff_features = api.retrieve("function_diff_features", [oid, baseline_oid],{"functionA": func['func_name'], "functionB": func['baseline_func_name']})
        # If all differences (except for 'modified_operand_instr') are zero, classify as operand modified.
        if all(value == 0 for key, value in diff_features.items() if key != 'modified_operand_instr'):
            add_func_info(target_exe['operand_modified_funcs'], func_addr, func, diff_features)
        else:
            add_func_info(target_exe['structurally_modified_funcs'], func_addr, func, diff_features)

    return modified_target_exes

def get_all_functions(oids):
    functions = []
    for oid in oids:
        funcs = api.retrieve("function_representations", oid)
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
    for target_oid in target_oid_list:
        disasm_result = api.retrieve('ghidra_disasm', target_oid)
        if disasm_result is None or disasm_result == {} or disasm_result["original_blocks"] == {}:
            failed_target_exes.append(target_oid)
            unmatched_target_oids.discard(target_oid)
        else:
            filtered_oid_list.append(target_oid)
            
    target_oid_list = filtered_oid_list

    filtered_baseline_oid_list = []
    for baseline_oid in baseline_oid_list:
        disasm_result = api.retrieve('ghidra_disasm', baseline_oid)
        if disasm_result is None or disasm_result == {} or disasm_result["original_blocks"] == {}:
            failed_baseline_exes.append(baseline_oid)
            unmatched_baseline_oids.discard(baseline_oid)
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

    # Process target_oid_list
    for target_oid in target_oid_list[:]:  # Iterate over a copy to modify the original safely
        tlsh_hash = api.get_field("tlshash", target_oid, 'hash')
        if not tlsh_hash or tlsh_hash == "TNULL":
            target_oid_list.remove(target_oid)
            unmatched_target_oids.discard(target_oid)
            failed_target_exes.append(target_oid)
        else:
            file_hashes[target_oid] = tlsh_hash

    # Process baseline_oid_list
    for baseline_oid in baseline_oid_list[:]:  # Iterate over a copy to modify the original safely
        tlsh_hash = api.get_field("tlshash", baseline_oid, 'hash')
        if not tlsh_hash or tlsh_hash == "TNULL":
            baseline_oid_list.remove(baseline_oid)
            unmatched_baseline_oids.discard(baseline_oid)
        else:
            file_hashes[baseline_oid] = tlsh_hash


    # Recompute lengths after removing invalid TLSH files
    len_A, len_B = len(target_oid_list), len(baseline_oid_list)
    if not file_hashes or len_A == 0 or len_B == 0:
        return modified_target_exes, unmatched_target_oids, failed_target_exes

    ########################################################################
    # STEP 2: Build cost (distance) matrix based on TLSH diff
    ########################################################################
    similarity_matrix = np.full((len_A, len_B), 9999)  # Large finite padding
    for i, target_oid in enumerate(target_oid_list):
        for j, baseline_oid in enumerate(baseline_oid_list):
            hashA = file_hashes.get(target_oid)
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
        target_oid = target_oid_list[i]
        baseline_oid = baseline_oid_list[j]
        best_score = similarity_matrix[i, j]

        if "DUMMY" not in target_oid and "DUMMY" not in baseline_oid:
            modified_target_exes[target_oid] = {
                "baseline_oid": baseline_oid,
                "similarity": best_score
            }
            unmatched_target_oids.discard(target_oid)
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
        funcs = api.retrieve("function_representations", oid)
        if funcs:
            for func in funcs:
                func_to_oids[func].add(oid)

    # 2) Build a results dict with "unique" / "repeated" per OID
    results = {}
    for oid in oid_list:
        results[oid] = {'funcs': {}, "rep_funcs": {}, "empty_funcs": {}}
        funcs = api.retrieve("function_representations", oid)
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
        num_funcs = 0
        funcs = api.retrieve("function_representations", oid)
        if funcs:
            for func in funcs:
                if funcs[func]['tlsh hash'] != None:
                    num_funcs += 1
        results[oid] = {'Num_functions': num_funcs}
    return results