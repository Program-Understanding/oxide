from oxide.core.oxide import api, progress
from typing import Dict, Any, Tuple, Callable, Optional, List
import csv
from typing import Any, Dict
import pandas as pd
import matplotlib.pyplot as plt

from oxide.core import oxide as oxide


NAME = "DRIFT"

# ----------------------------------------
# Feature Filter Rules
# ----------------------------------------
rules = {
    "Call_OR_Control_Modified": {
        "or": [
            "bb_nodes",
            "bb_edges",
            "fc_add_existing",
            "fc_add_new",
            "fc_removed_existing",
            "fc_removed_deleted",
        ]
    },
    "Control_Call_Modified": {
        "and": [
            ["bb_nodes", "bb_edges"],  # This will be handled as OR in a nested check
            [
                "fc_add_existing",
                "fc_add_new",
                "fc_removed_existing",
                "fc_removed_deleted",
            ],
        ]
    },
    "Call_Modified": {
        "or": [
            "fc_add_existing",
            "fc_add_new",
            "fc_removed_existing",
            "fc_removed_deleted",
        ]
    },
    "Control_Modified": {
        "or": [
            "bb_nodes",
            "bb_edges",
        ]
    },
}

# ----------------------------------------
# Entry‐Point Functions
# ----------------------------------------


def compare_collections(args: Any, opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Top‐level entry: classify files and functions between two collections.
    Supports `view` to return a specific subsection and
    `feature_thresholds` to filter modified functions by feature counts.
    """
    view = opts.get("view")
    filter_name = opts.get("filter")

    # 1) run or retrieve the raw comparison
    data = full_comparison(args, opts)
    if not data:
        return {}

    pair_files_results = data["PAIR_FILES_RESULTS"]
    raw_function_diffs = data["FUNCTION_DIFFS"]

    # 2) extract optional filtering rules
    if filter_name in rules:
        filter_rules = rules[filter_name]
    else:
        filter_rules = None
    # 3) summarize files
    file_classification = classify_file_counts(pair_files_results)

    # 4) summarize functions (applies filter and returns per-file and total)
    per_file_fc, total_fc = summarize_function_classifications(
        raw_function_diffs, filter_rules, filter_name
    )

    # 5) assemble output
    output = {
        "FILE_CLASSIFICATIONS": file_classification,
        "FUNCTION_CLASSIFICATION": {"PER_FILE": per_file_fc, "TOTAL": total_fc},
    }
    return output.get(view, output)


def full_comparison(args: Any, opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Entry for computing or retrieving a cached comparison.
    Returns:
      - PAIR_FILES_RESULTS: raw pairing output
      - FUNCTION_DIFFS:      per-file function diff details
    """
    if len(args) < 2:
        print("ERROR: Enter two collections to compare")
        return {}
    valid, invalid = api.valid_oids(args)
    if len(valid) < 2:
        print(f"ERROR: Invalid collections: {invalid}")
        return {}
    target, baseline = valid[:2]

    cache_key = f"compare_{target}_{baseline}"
    if api.local_exists(NAME, cache_key):
        return api.local_retrieve(NAME, cache_key)

    pair_files_results = api.retrieve("pair_files", [target, baseline])
    function_diffs = analyze_function_diffs(pair_files_results)

    results = {
        "PAIR_FILES_RESULTS": pair_files_results,
        "FUNCTION_DIFFS": function_diffs,
    }
    api.local_store(NAME, cache_key, results)
    return results


def compare_all_collections(args: Any, opts: Dict[str, Any]) -> Any:
    entries_file = opts["entries"]  # Path to text file with sequence of comparisons.
    series_file: Optional[str] = opts.get("entries")
    pairs = read_series_file(series_file)
    if len(pairs) < 2:
        raise ValueError("entries file must list at least two versions (one per line)")

    # Optional: print or log to verify
    print(f"Loaded {len(pairs)} entries from {entries_file}")

    colname_to_cid = {
        api.get_colname_from_oid(cid): cid for cid in api.collection_cids()
    }
    rows = []

    for idx, (target, baseline) in enumerate(pairs, 1):
        print(f"{api.get_colname_from_oid(target)} -> {api.get_colname_from_oid(baseline)}")
        res = compare_collections([target, baseline], opts)

        # extract totals
        func_totals = res["FUNCTION_CLASSIFICATION"]["TOTAL"]
        file_totals = res["FILE_CLASSIFICATIONS"]

        # merge into single flat dict
        row = {
            "target": target,
            "baseline": baseline,
            **func_totals,  # e.g. {'Matched': 92, 'Modified': 70, ...}
            **file_totals,  # e.g. {'Matched': 5, 'Added': 3, ...}
        }
        rows.append(row)

    # dump CSV
    path = opts.get("csv_path", "compare_all_collections.csv")
    if rows:
        fields = list(rows[0].keys())
        with open(path, "w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fields)
            writer.writeheader()
            writer.writerows(rows)
        print(f"Results written to {path}")

        # now build DataFrame
        df = pd.DataFrame(rows).set_index("target")

        # assume the same classification categories for both functions and files
        # adjust these lists to match your actual keys
        func_categories = list(res["FUNCTION_CLASSIFICATION"]["TOTAL"].keys())
        file_categories = list(res["FILE_CLASSIFICATIONS"].keys())

        # --- Plot 1: Function classifications ---
        ax1 = df[func_categories].plot(kind="bar", stacked=True, figsize=(10, 6))
        ax1.set_title("Function Classification per Version")
        ax1.set_xlabel("Target Version")
        ax1.set_ylabel("Number of Functions")
        plt.tight_layout()
        plt.savefig(opts.get("func_chart_path", "function_classification.png"))
        plt.close(ax1.figure)

        # --- Plot 2: File classifications ---
        ax2 = df[file_categories].plot(kind="bar", stacked=True, figsize=(10, 6))
        ax2.set_title("File Classification per Version")
        ax2.set_xlabel("Target Version")
        ax2.set_ylabel("Number of Files")
        plt.tight_layout()
        plt.savefig(opts.get("file_chart_path", "file_classification.png"))
        plt.close(ax2.figure)

    return rows


exports = [full_comparison, compare_collections, compare_all_collections]

# ----------------------------------------
# Helper Functions (Not Entry Points)
# ----------------------------------------


def filter_modified_by_threshold(function_diffs, filter_rules, filter_name):
    if isinstance(filter_rules, dict):
        and_keys = filter_rules.get("and", []) or []
        or_keys = filter_rules.get("or", []) or []
    elif isinstance(filter_rules, (list, tuple, set)):
        and_keys, or_keys = [], list(filter_rules)
    else:
        raise ValueError("feature_rules must be a list or dict with 'and'/'or' keys")

    def _any_nonzero(keys, feats):
        # keys may be a list of strings OR a single string
        if isinstance(keys, (list, tuple, set)):
            return any(_any_nonzero(k, feats) for k in keys)
        return feats.get(keys, 0) != 0

    def entry_pass(entry):
        feats = entry.get("features", {})

        # AND: each item can be a str OR a list-of-str meaning OR-group
        if and_keys:
            ok_and = all(
                (
                    _any_nonzero(k, feats)
                    if isinstance(k, (list, tuple, set))
                    else feats.get(k, 0) != 0
                )
                for k in and_keys
            )
            if not ok_and:
                return False

        # OR: classic behavior (any nonzero)
        if or_keys and not any(feats.get(k, 0) != 0 for k in or_keys):
            return False

        return True

    filtered = {}
    for key, diff in function_diffs.items():
        fc = diff["function_classification"].copy()
        original = fc.get("modified", [])
        passed = [m for m in original if entry_pass(m)]
        fc["modified"] = [m for m in original if not entry_pass(m)]
        fc[filter_name] = passed

        nd = diff.copy()
        nd["function_classification"] = fc
        filtered[key] = nd
    return filtered


def analyze_function_diffs(
    pair_files_results: Dict[str, Any],
) -> Dict[Tuple[str, str], Any]:
    """
    For every modified pair, classify functions and package per-pair results.
    """
    modified = pair_files_results.get("MODIFIED_EXECUTABLES", {})
    diffs: Dict[Tuple[str, str], Any] = {}

    print("DIFF FUNCTIONS")
    count = 1
    for (t_oid, b_oid), info in modified.items():
        print(f"PAIR {count} of {len(modified.items())}")
        if api.local_exists(NAME, f"file_diff_{t_oid}_{b_oid}"):
            fc = api.local_retrieve(NAME, f"file_diff_{t_oid}_{b_oid}")
        else:
            fc = classify_function_diffs(t_oid, b_oid, info.get("diff", {}))
            api.local_store(NAME, f"file_diff_{t_oid}_{b_oid}", fc)
        diffs[(t_oid, b_oid)] = {
            "filenames": {
                "target": api.get_names_from_oid(t_oid),
                "baseline": api.get_names_from_oid(b_oid),
            },
            "function_classification": fc,
        }
        count += 1
    return diffs


def classify_function_diffs(
    t_oid: str, b_oid: str, bindiff_full: Dict[str, Any]
) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    """
    For a single file-pair, returns:
      - function_classification: dict with lists of
          unmatched_target, unmatched_baseline, matched, modified
    """
    func_matches = bindiff_full.get("function_matches", {})
    ranked_pairs = sorted(func_matches.items(), key=lambda kv: kv[1]["similarity"])
    rank_map = {key: idx + 1 for idx, (key, _) in enumerate(ranked_pairs)}

    unmatched_target = list(bindiff_full.get("unmatched_primary", []))
    unmatched_baseline = list(bindiff_full.get("unmatched_secondary", []))
    matched = []
    modified = []

    funcs_t = api.get_field("ghidra_disasm", t_oid, "functions") or {}
    funcs_b = api.get_field("ghidra_disasm", b_oid, "functions") or {}

    name_t = {off: meta.get("name") for off, meta in funcs_t.items()}
    name_b = {off: meta.get("name") for off, meta in funcs_b.items()}

    p = progress.Progress(len(func_matches.items()))
    for (addr_t, addr_b), info in func_matches.items():

        sim = info["similarity"]
        meta = {
            "name_target_func": name_t.get(addr_t),
            "name_baseline_func": name_b.get(addr_b),
            "bindiff_similarity": sim,
            "bindiff_ranking": rank_map[(addr_t, addr_b)],
        }
        if sim >= 1.0:
            matched.append((addr_t, addr_b))
        else:
            feat = (
                api.retrieve(
                    "function_diff_features",
                    [t_oid, b_oid],
                    {"target": addr_t, "baseline": addr_b},
                )
                or {}
            )
            modified.append({"pair": (addr_t, addr_b), "features": feat, "info": meta})
        p.tick()

    function_classification = {
        "unmatched_target": unmatched_target,
        "unmatched_baseline": unmatched_baseline,
        "matched": matched,
        "modified": modified,
    }
    return function_classification


def classify_file_counts(pair_files_results: Dict[str, Any]) -> Dict[str, int]:
    """
    Count files per category (matched, modified, etc.).
    """
    return {cat: len(oids) for cat, oids in pair_files_results.items()}


def summarize_function_classifications(
    function_diffs: Dict[Tuple[str, str], Any],
    filter_rules: Any = None,
    filter_name: Any = None,
) -> Tuple[Dict[Tuple[str, str], Any], Dict[str, int]]:
    """
    Per-pair summary counts for:
      - unmatched_target
      - unmatched_baseline
      - matched
      - modified (post-filter, if any)
      - <filter_name> (if provided)

    Returns (per_file_summary, total_summary).
    """
    per_file: Dict[Tuple[str, str], Any] = {}
    total_ut = total_ub = total_mat = total_mod = total_filt = 0

    for key, diff in function_diffs.items():
        # get a fresh copy of classifications
        fc = diff["function_classification"].copy()

        # apply filter if requested
        if filter_rules and filter_name:
            single = {key: diff}
            fd = filter_modified_by_threshold(single, filter_rules, filter_name)
            fc = fd[key]["function_classification"]

        # count each category
        ut = len(fc.get("unmatched_target", []))
        ub = len(fc.get("unmatched_baseline", []))
        mat = len(fc.get("matched", []))
        mod = len(fc.get("modified", []))
        filt = len(fc.get(filter_name, [])) if filter_name else 0

        # record per-file
        entry = {
            "unmatched_target": ut,
            "unmatched_baseline": ub,
            "matched": mat,
            "modified": fc.get("modified", []),
        }
        if filter_name:
            entry[filter_name] = fc.get(filter_name, [])
        per_file[key] = entry

        # accumulate totals
        total_ut += ut
        total_ub += ub
        total_mat += mat
        total_mod += mod
        total_filt += filt

    # build total summary
    total: Dict[str, int] = {
        "unmatched_target": total_ut,
        "unmatched_baseline": total_ub,
        "matched": total_mat,
        "modified": total_mod,
    }
    if filter_name:
        total[filter_name] = total_filt

    return per_file, total


def aggregate_function_stats(
    function_diffs: Dict[Tuple[str, str], Any],
) -> Dict[str, float]:
    """
    Roll up metrics into global aggregates.
    """
    total_pairs = sum(d["results"]["total_pairs"] for d in function_diffs.values())
    total_candidates = sum(
        d["results"]["bindiff_candidates"] for d in function_diffs.values()
    )
    total_added = sum(d["results"]["added"] for d in function_diffs.values())
    total_removed = sum(d["results"]["removed"] for d in function_diffs.values())
    return {
        "total_pairs_all": total_pairs,
        "total_bindiff_candidates": total_candidates,
        "total_added": total_added,
        "total_removed": total_removed,
    }

def read_series_file(path: str, sep: str = ",") -> List[Tuple[str, str]]:
    """
    Read a series file where each non-comment line defines a pair of collections.

    Example line format (default sep=","):
        coll_old, coll_new

    Returns:
        List of (cid_left, cid_right) tuples.
    """
    pairs: List[Tuple[str, str]] = []

    with open(path, "r", encoding="utf-8") as f:
        for raw_ln in f:
            ln = raw_ln.strip()
            if not ln or ln.startswith("#"):
                continue

            parts = [p.strip() for p in ln.split(sep)]
            if len(parts) != 2:
                raise ValueError(
                    f"Line {raw_ln!r} does not contain exactly two collections "
                    f"separated by {sep!r}"
                )

            left_name, right_name = parts
            cid_left = oxide.api.get_cid_from_name(left_name)
            cid_right = oxide.api.get_cid_from_name(right_name)
            pairs.append((cid_left, cid_right))

    return pairs

def retrieve_function_instructions(file, func):
    """
    Retrieve function instructions for a specific function by its name.
    """
    function_data = api.retrieve('function_representations', file, {'lift_addrs': False})
    if func in function_data:
        return function_data[func].get('fun_instructions')
    
    return None