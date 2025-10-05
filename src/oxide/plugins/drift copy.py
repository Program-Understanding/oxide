from oxide.core.oxide import api
from typing import Dict, Any, List, Tuple
import csv

from oxide.core import progress, api

NAME = "DRIFT"

from typing import Any, Dict, Tuple

def full_comparison(args: Any, opts: Dict[str, Any]) -> Dict[str, Any]:
    if len(args) < 2:
        print("ERROR: Enter two collections to compare")
        return {}

    valid, invalid = api.valid_oids(args)
    if len(valid) < 2:
        print(f"ERROR: Invalid collections: {invalid}")
        return {}
    target_collection, baseline_collection = valid[:2]

    if api.local_exists(NAME, f"compare_{target_collection}_{baseline_collection}"):
        return api.local_retrieve(NAME, f"compare_{target_collection}_{baseline_collection}")

    # Retrieve per-file classification (including full diff under "diff")
    pair_files_results = api.retrieve("pair_files", [target_collection, baseline_collection])

    # initialize counts
    total_unmatched_target = sum(
        len(api.get_field("ghidra_disasm", m, "functions") or [])
        for m in pair_files_results.get("UNMATCHED_TARGET_EXECUTABLES", {})
    )

    total_unmatched_baseline = sum(
        len(api.get_field("ghidra_disasm", m, "functions") or [])
        for m in pair_files_results.get("UNMATCHED_BASELINE_EXECUTABLES", {})
    )

    total_matched = 0
    total_modified = 0
    total_structural = 0

    modified = pair_files_results.get("MODIFIED_EXECUTABLES", {})
    modified_file_diffs: Dict[Tuple[str, str], Any] = {}

    for (t_oid, b_oid), info in modified.items():
        bindiff_full = info.get("diff", {})
        func_matches = bindiff_full.get("function_matches", {})

        sorted_pairs = sorted(
            func_matches.items(),
            key=lambda kv: kv[1]['similarity']
        )
        rank_map = {key: idx for idx, (key, _) in enumerate(sorted_pairs)}

        unmodified = []
        structurally_modified = {}
        modified_details = {}

        for (addr_t, addr_b), match_info in func_matches.items():
            sim = match_info['similarity']
            if sim >= 1.0:
                unmodified.append((addr_t, addr_b))
                continue

            feat = api.retrieve(
                "function_diff_features",
                [t_oid, b_oid],
                {"target": addr_t, "baseline": addr_b}
            ) or {}

            if all(v == 0 for v in feat.values()):
                unmodified.append((addr_t, addr_b))
                continue

            meta = {
                'name_target_func':   match_info["functions"]["primary"]["name"],
                'name_baseline_func': match_info["functions"]["secondary"]["name"],
                'bindiff_similarity': sim,
                'bindiff_ranking':    rank_map[(addr_t, addr_b)] + 1,
            }

            # structural if any non-zero control-flow or call-edge feature
            if (feat.get('basic_blocks', 0) != 0 or
                feat.get('fc_add_existing', 0) != 0 or
                feat.get('fc_add_new', 0) != 0 or
                feat.get('fc_removed_existing', 0) != 0 or
                feat.get('fc_removed_deleted', 0) != 0):
                structurally_modified[(addr_t, addr_b)] = {
                    'features': feat, 'info': meta
                }
            else:
                modified_details[(addr_t, addr_b)] = {
                    'features': feat, 'info': meta
                }

        total_pairs = len(func_matches)
        bindiff_ct = sum(
            1 for m in func_matches.values() if m['similarity'] < 1.0
        )
        structural_ct = len(structurally_modified)

        reduction_bindiff = (
            100 * (1 - structural_ct / bindiff_ct)
            if bindiff_ct else 0.0
        )
        reduction_all = (
            100 * (1 - structural_ct / total_pairs)
            if total_pairs else 0.0
        )

        modified_file_diffs[(t_oid, b_oid)] = {
            'filenames': {
                'target': api.get_names_from_oid(t_oid),
                'baseline': api.get_names_from_oid(b_oid)
            },
            'function_classification': {
                'unmatched_target':   bindiff_full.get('unmatched_primary', []),
                'unmatched_baseline': bindiff_full.get('unmatched_secondary', []),
                'unmodified_count':   unmodified,
                'structurally_modified': structurally_modified,
                'modified':              modified_details
            },
            'results': {
                'total_pairs': total_pairs,
                'bindiff_candidates': bindiff_ct,
                'structural_count': structural_ct,
                'added': len(bindiff_full.get('unmatched_primary', [])),
                'removed': len(bindiff_full.get('unmatched_secondary', [])),
                'search_space_reduction_pct': reduction_bindiff,
                'search_space_reduction_over_all_pairs_pct': reduction_all
            }
        }

        total_unmatched_target += len(bindiff_full.get('unmatched_primary', []))
        total_unmatched_baseline += len(bindiff_full.get('unmatched_secondary', []))
        total_matched += len(unmodified)
        total_modified += len(modified_details)
        total_structural += len(structurally_modified)

    function_classification_totals = {
        'unmatched_target': total_unmatched_target,
        'unmatched_baseline': total_unmatched_baseline,
        'unmodified_count': total_matched,
        'structurally_modified': total_structural,
        'modified': total_modified
    }

    results = {
        'PAIR_FILES_RESULTS': pair_files_results,
        'FUNCTION_CLASSIFICATION_TOTALS': function_classification_totals,
        'FUNCTION_DIFFS': modified_file_diffs
    }

    api.local_store(NAME, f"compare_{target_collection}_{baseline_collection}", results)

    return results


def compare_collections(args, opts) -> Dict[str, Any]:
    view = opts.get("view", None)

    # 1) Get raw data + diffs
    data = full_comparison(args, opts)
    if not data:
        return {}

    pair_files = data["PAIR_FILES_RESULTS"]
    function_summary = data["FUNCTION_DIFFS"]

    # 2) Compute category counts
    file_classification_counts = {
        cat: len(items)
        for cat, items in pair_files.items()
    }

    function_classifications = {}
    for file in function_summary:
        function_classifications[file] = {}
        for type in function_summary[file]['function_classification']:
            if type == 'modified' or type == 'structurally_modified':
                function_classifications[file][type] = function_summary[file]['function_classification'][type]
            else:
                function_classifications[file][type] = len(function_summary[file]['function_classification'][type])
            
    
    # 3) Compute aggregated function-diff stats
    total_pairs_all      = sum(s["results"]["total_pairs"]            for s in function_summary.values())
    total_bindiff_all    = sum(s["results"]["bindiff_candidates"]     for s in function_summary.values())
    total_structural_all = sum(s["results"]["structural_count"]       for s in function_summary.values())
    total_added = sum(s["results"]["added"] for s in function_summary.values())
    total_removed = sum(s["results"]["removed"] for s in function_summary.values())

    overall_reduction_bindiff = (
        100 * (1 - total_structural_all / total_bindiff_all)
        if total_bindiff_all else 0.0
    )

    aggregated = {
        "total_added": total_added,
        "total_removed": total_removed,
        "total_pairs_all": total_pairs_all,
        "total_bindiff_candidates": total_bindiff_all,
        "total_structurally_modified": total_structural_all,
        "overall_search_space_reduction_pct": overall_reduction_bindiff,
    }

    # 4) Final output
    output = {
        "FILE_CLASSIFICATIONS": file_classification_counts,
        "FUNCTION_CLASSIFICATIONS": function_classifications,
        "AGGREGATED_FUNCTION_DIFFS": aggregated
    }

    # 5) Honor the view shortcut
    if view and view in output:
        return output[view]
    return output

def get_structurally_modified(args, opts):
    view = opts.get("view", None)

    # 1) Get raw data + diffs
    data = full_comparison(args, opts)
    if not data:
        return {}
    
    results = {}
    for file in data['FUNCTION_DIFFS']:
        results[file] = {
            'structurally_modified': data['FUNCTION_DIFFS'][file]['function_classification']['structurally_modified'],
            'modified': data['FUNCTION_DIFFS'][file]['function_classification']['modified']
        }

    return results


def compare_all_collections(args, opts):
    entries = []
    # openwrt_collections = [
    # '22.03.0', '22.03.1', '22.03.2', '22.03.3',
    # '22.03.4', '22.03.5', '22.03.6', '22.03.7',
    # '23.05.2', '23.05.3', '23.05.4', '23.05.5',
    # '24.10.0', '24.10.1', '24.10.2'
# ]
    wago_collections = ['03.10.08', '03.10.10', '03.10.08-clean', '03.10.10-backdoor']


    # Get a map of collection name to CID
    colname_to_cid = {
        api.get_colname_from_oid(cid): cid
        for cid in api.collection_cids()
    }

    for i in range(1, len(wago_collections)):
        target_name   = wago_collections[i]
        baseline_name = wago_collections[i - 1]

        if target_name in colname_to_cid and baseline_name in colname_to_cid:
            tgt_cid = colname_to_cid[target_name]
            bln_cid = colname_to_cid[baseline_name]

            print(f"Comparing {target_name} → {baseline_name}")
            result = compare_collections([tgt_cid, bln_cid], opts)
            agg = result["AGGREGATED_FUNCTION_DIFFS"]
            file_classification = result['FILE_CLASSIFICATIONS']

            # Collect one row per comparison
            row = {
                "target":   target_name,
                "baseline": baseline_name,
                **agg,
                **file_classification
            }
            entries.append(row)

    # Dump to CSV
    csv_path = opts.get("csv_path", "compare_all_collections.csv")
    if entries:
        fieldnames = list(entries[0].keys())
        with open(csv_path, "w", newline="") as csvfile:
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(entries)
        print(f"Results written to {csv_path}")

    return entries


exports = [full_comparison, compare_collections, compare_all_collections, get_structurally_modified]