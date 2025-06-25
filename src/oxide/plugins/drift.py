from oxide.core.oxide import api
from typing import Dict, Any, List, Tuple

from oxide.core import progress, api

def compare_collections(args, opts):
    if len(args) < 2:
        print("ERROR: Enter two collections to compare")
        return

    view = opts.get("view", None)

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
    function_summary: Dict[Tuple[str, str], Dict[str, Any]] = {}

    for (t_oid, b_oid), info in modified.items():
        bindiff_full = info.get("diff", {})
        func_matches = bindiff_full.get("function_matches", {})

        # prepare ranking map
        sorted_pairs = sorted(
            func_matches.items(),
            key=lambda kv: kv[1]['similarity']
        )
        bindiff_rankings = [key for key, _ in sorted_pairs]
        rank_map = {key: idx for idx, key in enumerate(bindiff_rankings)}

        # initialize counters and containers
        unmodified_count = 0
        structurally_modified_details: Dict[Tuple[str, str], Any] = {}
        modified_details: Dict[Tuple[str, str], Any] = {}

        # process each function match
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
                # metadata common to both buckets
                meta_data = {
                    'name_target_func': name_t_func,
                    'name_baseline_func': name_b_func,
                    'bindiff_similarity': match_info['similarity'],
                    'bindiff_ranking': rank_map[(_addr_t, _addr_b)] + 1,
                }

                # classify based on func_calls or basic_blocks
                if feat.get('func_calls', 0) != 0 or feat.get('basic_blocks', 0) != 0:
                    structurally_modified_details[(_addr_t, _addr_b)] = {
                        'features': feat,
                        'info': meta_data
                    }
                else:
                    modified_details[(_addr_t, _addr_b)] = {
                        'features': feat,
                        'info': meta_data
                    }

        # compute triage statistics for this pair
        total_pairs = len(func_matches)
        total_bindiff_mods = sum(
            1 for m in func_matches.values() if m.get('similarity', 1.0) < 1.0
        )
        structural_count = len(structurally_modified_details)
        reduction_binDiff = (
            100 * (1 - structural_count / total_bindiff_mods)
            if total_bindiff_mods else 0.0
        )
        reduction_all_pairs = (
            100 * (1 - structural_count / total_pairs)
            if total_pairs else 0.0
        )

        # assemble summary for this file-pair
        function_summary[(t_oid, b_oid)] = {
            "filenames": {
                "baseline": api.get_names_from_oid(b_oid),
                "target": api.get_names_from_oid(t_oid)
            },
            "function_classification": {
                "unmatched_target": len(bindiff_full.get("unmatched_primary", [])),
                "unmatched_baseline": len(bindiff_full.get("unmatched_secondary", [])),
                "unmodified_count": unmodified_count,
                "structurally_modified": len(structurally_modified_details),
                "modified": len(modified_details),
            },
            "results": {
                "total_pairs": total_pairs,
                "bindiff_candidates": total_bindiff_mods,
                "structural_count": structural_count,
                "search_space_reduction_pct": reduction_binDiff,
                "search_space_reduction_over_all_pairs_pct": reduction_all_pairs,
            }
        }

    # 3) Attach the function summary to output
    output["FUNCTION_DIFFS"] = function_summary

    # 4) Aggregate across all file-pairs using nested "results"
    total_pairs_all = sum(
        stats["results"]["total_pairs"] for stats in function_summary.values()
    )
    total_bindiff_all = sum(
        stats["results"]["bindiff_candidates"] for stats in function_summary.values()
    )
    total_structural_all = sum(
        stats["results"]["structural_count"] for stats in function_summary.values()
    )
    overall_reduction_binDiff = (
        100 * (1 - total_structural_all / total_bindiff_all)
        if total_bindiff_all else 0.0
    )
    overall_reduction_all_pairs = (
        100 * (1 - total_structural_all / total_pairs_all)
        if total_pairs_all else 0.0
    )
    output["AGGREGATED_FUNCTION_DIFFS"] = {
        "total_pairs_all": total_pairs_all,
        "total_bindiff_candidates": total_bindiff_all,
        "total_structurally_modified": total_structural_all,
        "overall_search_space_reduction_pct": f"{overall_reduction_binDiff}%",
        "overall_search_space_reduction_over_all_pairs_pct": f"{overall_reduction_all_pairs}%",
    }

    # 5) Return based on view option
    if view and view in output:
        return output[view]
    return output

exports = [compare_collections]