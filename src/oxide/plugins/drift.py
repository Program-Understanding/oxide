from oxide.core.oxide import api
import csv
import os
from tabulate import tabulate
import pandas as pd
import datetime
import time
from typing import Dict, Any, List, Tuple, Set, Optional

from oxide.core import progress, api

def compare_collections(args, opts):
    if len(args) < 2:
        print("ERROR: Enter two collections to compare")
        return

    # Validate and pick the two collections
    valid, invalid = api.valid_oids(args)
    if len(valid) < 2:
        print(f"ERROR: Invalid collections: {invalid}")
        return
    target_collection, baseline_collection = valid[0], valid[1]

    # Retrieve per-file classification (including full diff under "diff")
    pair_files_results = api.retrieve("pair_files", [target_collection, baseline_collection])

    # 1) Build counts for all categories except modified executables
    output: Dict[str, Any] = {}
    for category, items in pair_files_results.items():
        if category != "MODIFIED_EXECUTABLES":
            output[category] = len(items)

    # 2) For modified executables, separate unmodified vs modified functions
    modified = pair_files_results.get("MODIFIED_EXECUTABLES", {})
    function_summary: Dict[str, Dict[str, Any]] = {}

    for (t_oid, b_oid), info in modified.items():
        bindiff_full = info.get("diff", {})
        func_matches = bindiff_full.get("function_matches", {})

        sorted_pairs = sorted(
            func_matches.items(),
            key=lambda kv: kv[1]['similarity']
        )
        print(sorted_pairs)
        bindiff_rankings = [ key for key, _ in sorted_pairs ]
        rank_map = { key: idx for idx, key in enumerate(bindiff_rankings) }

        unmodified_count = 0
        structurally_modified_details: Dict[Tuple[str, str], Any] = {}
        operand_modified_details: Dict[Tuple[str, str], Any] = {}

        for (_addr_t, _addr_b), match_info in func_matches.items():
            name_t_func = match_info["functions"]["primary"]["name"]
            name_b_func = match_info["functions"]["secondary"]["name"]


            # call analyzer for detailed diff features
            feat = api.retrieve(
                "function_diff_features",
                [t_oid, b_oid],
                {"target": _addr_t, "baseline": _addr_b}
            )

            # mark as unmodified if no features or all feature values are zero
            if not feat or all(v == 0 for v in feat.values()):
                unmodified_count += 1
            else:
                # check if the *only* non‐zero feature is modified_operand_instr
                nonzero_keys = [k for k,v in feat.items() if k != 'bindiff_similarity' and k != 'bindiff_ranking' and v != 0]
                if nonzero_keys == ['modified_operand_instr']:
                    feat['name_target_func'] = name_t_func
                    feat['name_baseline_func'] = name_b_func
                    feat['bindiff_similarity'] = match_info['similarity']
                    feat['bindiff_ranking'] = rank_map[(_addr_t, _addr_b)] + 1
                    operand_modified_details[(_addr_t, _addr_b)] = feat
                else:
                    feat['name_target_func'] = name_t_func
                    feat['name_baseline_func'] = name_b_func
                    feat['bindiff_similarity'] = match_info['similarity']
                    feat['bindiff_ranking'] = rank_map[(_addr_t, _addr_b)] + 1
                    structurally_modified_details[(_addr_t, _addr_b)] = feat

        function_summary[(t_oid, b_oid)] = {
            "baseline_filenames": api.get_names_from_oid(b_oid),
            "target_filenames": api.get_names_from_oid(t_oid),
            "unmatched_target": bindiff_full.get("unmatched_primary"),
            "unmatched_baseline": bindiff_full.get("unmatched_secondary"),
            "unmodified_count": unmodified_count,
            "structurally_modified": structurally_modified_details,
            "operand_modified": operand_modified_details,
        }

    # 3) Attach the function summary to output
    output["FUNCTION_DIFFS"] = function_summary

    return output

exports = [compare_collections]