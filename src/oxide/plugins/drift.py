from oxide.core.oxide import api
import csv
import os
from tabulate import tabulate
import pandas as pd
import datetime
import time
from typing import Dict, Any, List, Tuple, Set, Optional

from oxide.core import progress, api

def calculate_statistics(report, target_oids):
    """Calculate statistics for each category in the report."""
    return {
        'MATCHED EXECUTABLES': calculate_stats(report["MATCHED_EXECUTABLES"], target_oids),
        'MATCHED NON-EXECUTABLE': calculate_stats(report['MATCHED_NON_EXECUTABLES'], target_oids),
        'MODIFIED EXECUTABLES': calculate_stats(report['MODIFIED_EXECUTABLES'], target_oids),
        'UNMATCHED EXECUTABLES': calculate_stats(report['UNMATCHED_EXECUTABLES'], target_oids),
        'UNMATCHED NON-EXECUTABLES': calculate_stats(report['UNMATCHED_NON_EXECUTABLES'], target_oids),
        'FAILED EXECUTABLES': calculate_stats(report['FAILED_EXECUTABLES'], target_oids)
    }


def print_triage_results(triage_results, target_collection, baseline_collection):
    title = f"{api.get_colname_from_oid(target_collection)} Compared to {api.get_colname_from_oid(baseline_collection)}"

    columns = [
        "Category",
        "Total",
    ]

    rows = []
    for key, number in triage_results[target_collection].items():
        rows.append([key, number])

    df = pd.DataFrame(rows, columns=columns)

    print(title)
    print(tabulate(df, headers='keys', tablefmt='psql', showindex=False))


def print_failed_executable(report):
    print("\n========================== FAILED EXECUTABLES ==========================")
    for file in report['FAILED_EXECUTABLES']:
        print(f"\nFailed Executable - File ID: {file}")

        names = api.get_names_from_oid(file)
        df = pd.DataFrame(names, columns=["Potential File Names"])

        print(tabulate(df, headers='keys', tablefmt='psql', showindex=False))


def print_modified_executables(report, file):
    print("\n================== MODIFIED EXECUTABLES ==================")
    if file:
        print_category_w_baseline({file: report['MODIFIED_EXECUTABLES'][file]})
    else:
        print_category_w_baseline(report['MODIFIED_EXECUTABLES'])
        save_csv_report(report)


def print_unmatched_executables(report, file):
    print("\n================== UNMATCHED EXECUTABLES ==================")
    if file:
        print_category_w_baseline({file: report['UNMATCHED_EXECUTABLES'][file]})
    else:
        for file in report['UNMATCHED_EXECUTABLES']:
            names = api.get_names_from_oid(file)
            df = pd.DataFrame(names, columns=["Potential File Names"])

            print(f"\nExecutable: {file}")
            print(tabulate(df, headers="keys", tablefmt="psql", showindex=False))


def print_unmatched_non_executables(report):
    print("\n================== UNMATCHED NON-EXECUTABLES ==================")

    for file in report['UNMATCHED_NON_EXECUTABLES']:
        names = api.get_names_from_oid(file)
        df = pd.DataFrame(names, columns=["Potential File Names"])

        print(f"\nNon-Executable: {file}")
        print(tabulate(df, headers="keys", tablefmt="psql", showindex=False))


def print_category_w_baseline(report_subset):
    for file_id, file_report in report_subset.items():
        baseline_file_id = file_report['baseline_oid']
        similarity = file_report['similarity']
        if baseline_file_id:
            print_table_match(file_id, baseline_file_id, similarity)

        print_func_matches(file_report)

        # Print structurally_modified_funcs table
        if 'structurally_modified_funcs' in file_report and len(file_report['structurally_modified_funcs']) > 0:
            print_structurally_modified_features(file_report)

        # Print operand_modified_funcs table
        if 'operand_modified_funcs' in file_report and len(file_report['operand_modified_funcs']) > 0:
            print_operand_modified_features(file_report)

        # Print unmatched_target_funcs table (renamed)
        if 'unmatched_target_funcs' in file_report and len(file_report['unmatched_target_funcs']) > 0:
            print_unmatched_funcs(file_report)
        print("\n")


def save_csv_report(report, output_dir="drift_reports"):
    os.makedirs(output_dir, exist_ok=True)

    # Lists to store data for each report type
    file_pairing_rows = []
    file_classification = {
        'Matched': [],
        'Modified': [],
        'Unmatched': {},
        'Removed': {}
    }

    func_class_rows = []

    # File Classification
    file_classification["Matched"] = report['MATCHED_EXECUTABLES']
    for file_id in report['UNMATCHED_EXECUTABLES']:
        # Retrieve file names (assumes api.get_names_from_oid exists)
        file_names = list(api.get_names_from_oid(file_id))
        if len(file_names) > 1:
            file_name_info = f"{len(file_names)} Associated Target File Names"
        else:
            file_name_info = file_names[0] if file_names else "Unknown"

        file_classification['Unmatched'][file_id] = file_name_info
        file_classification['Removed'][file_id] = file_name_info

    for file_id, file_report in report['MODIFIED_EXECUTABLES'].items():
        file_classification["Modified"].append(file_id)

        # --- File match info --- 
        baseline_file_id = file_report.get('baseline_oid')
        if baseline_file_id:
            func_class_rows.append({
                'Target File': file_id,
                'Baseline File': baseline_file_id,
                'Matched': len(file_report.get("matched_funcs", {})),
                "Modified": len(file_report.get("structurally_modified_funcs", {})),
                'Unmatched': len(file_report.get("unmatched_target_funcs", {}))
            })

            # Retrieve file names
            file_names = list(api.get_names_from_oid(file_id))
            if len(file_names) > 1:
                file_name_info = f"{len(file_names)} Associated File Names"
            else:
                file_name_info = file_names[0] if file_names else "Unknown"

            baseline_file_names = list(api.get_names_from_oid(baseline_file_id))
            if len(baseline_file_names) > 1:
                baseline_file_name_info = f"{len(baseline_file_names)} Associated File Names"
            else:
                baseline_file_name_info = baseline_file_names[0] if baseline_file_names else "Unknown"

            file_pairing_rows.append({
                "File ID": file_id,
                "Baseline File ID": baseline_file_id,
                "File Names": file_name_info,
                "Baseline File Names": baseline_file_name_info,
            })

    # --- Write file pairing data to CSV ---
    if file_pairing_rows:
        df = pd.DataFrame(file_pairing_rows)
        df.to_csv(os.path.join(output_dir, "file_pairing.csv"), index=False)

    if func_class_rows:
        df = pd.DataFrame(func_class_rows)
        df.to_csv(os.path.join(output_dir, "function_classification.csv"), index=False)

    print(f"Reports saved to directory: {output_dir}")


def print_structurally_modified_features(file_report):
    columns = [
        "Function",
        "Baseline Function",
        "Score",
        "BBs +/-",
        "Instr +",
        "Instr -",
        "Instr Opcode Mod",
        "Instr Operand Mod",
        "Func Calls +/-"
    ]

    rows = []
    for func, func_report in file_report['structurally_modified_funcs'].items():
        basic_blocks = func_report.get('basic_blocks', 0)
        instr_added = func_report.get('added_instr', 0)
        instr_removed = func_report.get('removed_instr', 0)
        instr_modified_opcode = func_report.get('modified_opcode_instr', 0)
        instr_modified_operand = func_report.get('modified_operand_instr', 0)
        func_calls = func_report.get('func_calls', 0)

        rows.append([
            func_report['func_name'],
            func_report['baseline_func_name'],
            func_report['similarity'],
            basic_blocks,
            instr_added,
            instr_removed,
            instr_modified_opcode,
            instr_modified_operand,
            func_calls
        ])

    df = pd.DataFrame(rows, columns=columns)

    numeric_cols = [
        "BBs +/-",
        "Instr +",
        "Instr -",
        "Instr Opcode Mod",
        "Instr Operand Mod",
        "Func Calls +/-"
    ]
    df["Total"] = df[numeric_cols].sum(axis=1)
    df.sort_values(by="Total", ascending=False, inplace=True)
    df.drop(columns="Total", inplace=True)

    print(f"{len(file_report['structurally_modified_funcs'])} Structurally-Modified Functions:")
    print(tabulate(df, headers='keys', tablefmt='psql', showindex=False))


def print_operand_modified_features(file_report):
    columns = [
        "Function",
        "Baseline Function",
        "Score",
        "BBs +/-",
        "Instr +",
        "Instr -",
        "Instr Opcode Mod",
        "Instr Operand Mod",
        "Func Calls +/-"
    ]

    rows = []
    for func, func_report in file_report['operand_modified_funcs'].items():
        basic_blocks = func_report.get('basic_blocks', 0)
        instr_added = func_report.get('added_instr', 0)
        instr_removed = func_report.get('removed_instr', 0)
        instr_modified_opcode = func_report.get('modified_opcode_instr', 0)
        instr_modified_operand = func_report.get('modified_operand_instr', 0)
        func_calls = func_report.get('func_calls', 0)

        rows.append([
            func_report['func_name'],
            func_report['baseline_func_name'],
            func_report['similarity'],
            basic_blocks,
            instr_added,
            instr_removed,
            instr_modified_opcode,
            instr_modified_operand,
            func_calls
        ])

    df = pd.DataFrame(rows, columns=columns)

    numeric_cols = [
        "BBs +/-",
        "Instr +",
        "Instr -",
        "Instr Opcode Mod",
        "Instr Operand Mod",
        "Func Calls +/-"
    ]
    df["Total"] = df[numeric_cols].sum(axis=1)
    df.sort_values(by="Total", ascending=False, inplace=True)
    df.drop(columns="Total", inplace=True)

    print(f"{len(file_report['operand_modified_funcs'])} Operand Modified Functions:")
    print(tabulate(df, headers='keys', tablefmt='psql', showindex=False))


def print_func_matches(file_report):
    print(f"{len(file_report['matched_funcs'])} Exact Function Matches")
    print(f"{len(file_report['lifted_matched_funcs'])} Lifted-Function Matches")


def print_unmatched_funcs(file_report):
    num_unmatched = len(file_report['unmatched_target_funcs'])
    print(f"{num_unmatched} Unmatched Functions:")

    for func, details in file_report['unmatched_target_funcs'].items():
        print(details)


def print_table_match(file_id, baseline_file_id, similarity):
    # Retrieve file names for both file IDs
    file_names = list(api.get_names_from_oid(file_id))
    if len(file_names) > 1:
        file_name_info = f"{len(file_names)} Associated File Names"
    else:
        file_name_info = f"File Name: {file_names[0]}"

    baseline_file_names = list(api.get_names_from_oid(baseline_file_id))
    if len(baseline_file_names) > 1:
        baseline_file_name_info = f"{len(baseline_file_names)} Associated Baseline File Names"
    else:
        baseline_file_name_info = f"Baseline File Name: {baseline_file_names[0]}"

    # Create table data with two columns: one for the file and one for the baseline_file
    table_data = [
        [f"File: {file_id}", f"Baseline File: {baseline_file_id}"],
        [file_name_info, baseline_file_name_info],
        [f"Similarity Score: {similarity}", ""]
    ]

    # Print the table using tabulate
    print(tabulate(table_data, tablefmt="grid"))


def print_compare_functions(report, file_oid, function):
    for mod_func, func_data in report['MODIFIED_EXECUTABLES'][file_oid]['structurally_modified_funcs'].items():
        if function == func_data['func_name']:
            u_diff = api.retrieve(
                "function_unified_diff",
                [file_oid, func_data['baseline_file']],
                {"function": func_data['func_name'], "baseline_function": func_data['baseline_func_name']}
            )
            for line in u_diff['unified_diff']:
                print(line)
    for mod_func, func_data in report['MODIFIED_EXECUTABLES'][file_oid]['operand_modified_funcs'].items():
        if function == func_data['func_name']:
            u_diff = api.retrieve(
                "function_unified_diff",
                [file_oid, func_data['baseline_file']],
                {"function": func_data['func_name'], "baseline_function": func_data['baseline_func_name']}
            )
            for line in u_diff['unified_diff']:
                print(line)

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

def compare_collections_series(args, opts):
    collections = get_collections(args, opts)
    parsed_collections = []
    for target_collection in collections:
        product, target_version = split_collection(api.get_colname_from_oid(target_collection))
        version_tuple = tuple(map(int, target_version.split('.')))
        parsed_collections.append((target_collection, product, target_version, version_tuple))
    parsed_collections.sort(key=lambda x: x[3])

    baseline_collection = None
    baseline_version = None
    triage_results = {}
    file_pairing_accuracy = {}
    p = progress.Progress(len(collections))

    for target_collection, product, target_version, version_tuple in parsed_collections:
        start_time = time.time()
        report = get_report(target_collection, baseline_collection)
        end_time = time.time()

        # file_pairing_accuracy[target_version] = get_file_pairing_accuracy(
        #     report, target_version, baseline_version, baseline_collection
        # )
        # triage_results[target_version] = get_triage_results(
        #     report, target_version, baseline_version
        # )

        # triage_results[target_version]['time(s)'] = end_time - start_time
        # baseline_version = target_version
        # baseline_collection = target_collection
        p.tick()

    time_stamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    dump_to_csv(triage_results, f'drift_reports/compare_collections_series/{time_stamp}/triage_results.csv')
    dump_to_csv(file_pairing_accuracy, f'drift_reports/compare_collections_series/{time_stamp}/file_pairing_accuracy.csv')


def import_product(args, opts):
    dir_path = args[0]
    if len(args) == 2:
        product_name = args[1]
    else:
        product_name = None

    if not os.path.isdir(dir_path):
        raise ShellSyntaxError("Enter a valid directory with firmware from devices")

    def import_sample(sample_name, sample_path):
        oids, new_files = (
            api.import_directory(sample_path) if os.path.isdir(sample_path)
            else api.import_file(sample_path)
        )
        api.create_collection(sample_name, oids, oids)

    parent_directory_name = os.path.basename(os.path.abspath(dir_path))

    for sample in os.listdir(dir_path):
        sample_path = os.path.join(dir_path, sample)
        if product_name:
            sample_name = f"{parent_directory_name}-v{sample}"
        else:
            sample_name = sample
        import_sample(sample_name, sample_path)

def evaluate_all(args, opts):
    repo_path = opts['repo_path']

    # Import all of the files
    oids = api.import_directory("path/to/dir")
    api.create_collection("Collection_name", oids)

    # Analyze all pairs

    # Compare results to ground truth

    # Print results

exports = [
    compare_collections,
    import_product,
    compare_collections_series
]


############################
### SUPPORTING FUNCTIONS ###
############################


def get_collections(args=None, opts=None):
    """
    Process collections based on provided arguments or a filter.

    Parameters:
        args (list or None): List of arguments to validate and expand OIDs.
        opts (dict or None): Options that may include a 'filter'.

    Returns:
        list: A list of processed collections.
    """
    opts = opts or {}
    collections = []

    if args:
        valid, invalid = api.valid_oids(args)
        collections = valid
    else:
        filter_value = opts.get('filter')
        if filter_value:
            all_collections = api.collection_cids()
            for collection in all_collections:
                collection_name = api.get_colname_from_oid(collection)
                if collection_name.startswith(filter_value):
                    collections.append(collection)
            if not collections:
                print("No collection matches for filter")
                return []
        else:
            for c in api.collection_cids():
                collections.append(c)

    return collections


def split_collection(input_string: str) -> Tuple[str, Optional[str]]:
    parts = input_string.rsplit('-v', maxsplit=1)
    if len(parts) == 2:
        return parts[0], parts[1]
    else:
        return parts[0], None


def calculate_stats(part, total):
    if isinstance(part, (list, dict, set)):
        count = len(part)
        pct = f"{round((count / len(total)) * 100, 2)}%" if len(total) > 0 else "0%"
        return count, pct
    return 0, "0%"


def dump_to_csv(data_dict, filename):
    if not data_dict:
        print(f"No data to dump for {filename}")
        return

    first_value = next(iter(data_dict.values()))
    if isinstance(first_value, dict):
        headers = list(first_value.keys())
        rows = list(data_dict.values())
    else:
        headers = ['key', 'value']
        rows = [{'key': k, 'value': v} for k, v in data_dict.items()]

    os.makedirs(os.path.dirname(filename), exist_ok=True)
    with open(filename, 'w', newline='') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=headers)
        writer.writeheader()
        writer.writerows(rows)


def get_file_pairing_accuracy(files_report, target_version, baseline_version, baseline_collection, output_dir="drift_reports"):
    os.makedirs(output_dir, exist_ok=True)

    TP = FP = FN = 0

    if baseline_collection:
        baseline_col_file_names = get_all_file_names(baseline_collection)
    else:
        baseline_col_file_names = []

    for file_id, file_report in files_report['MODIFIED_EXECUTABLES'].items():
        baseline_file_id = file_report.get('baseline_oid')
        if baseline_file_id:
            file_names = list(api.get_names_from_oid(file_id))
            baseline_file_names = list(api.get_names_from_oid(baseline_file_id))

            if any(name in baseline_file_names for name in file_names):
                TP += 1
            else:
                if any(name in baseline_col_file_names for name in file_names):
                    FN += 1
                else:
                    FP += 1

    precision = TP / (TP + FP) if (TP + FP) > 0 else 0
    recall = TP / (TP + FN) if (TP + FN) > 0 else 0
    f1 = 2 * (precision * recall) / (precision + recall) if (precision + recall) > 0 else 0

    return {
        'Version': target_version,
        'Baseline Version': baseline_version,
        'TP': TP,
        'FP': FP,
        'FN': FN,
        'Precision': precision,
        'Recall': recall,
        'F1': f1
    }


def get_file_classification_accuracy(report, baseline_collection):
    TP = FP = FN = TN = 0

    if baseline_collection:
        baseline_col_file_names = get_all_file_names(baseline_collection)
    else:
        baseline_col_file_names = []

    TN += len(report['MATCHED_EXECUTABLES'])

    for file_id in report['UNMATCHED_EXECUTABLES']:
        file_names = list(api.get_names_from_oid(file_id))
        if any(name in baseline_col_file_names for name in file_names):
            FP += 1
        else:
            TP += 1

    for file_id, file_report in report['MODIFIED_EXECUTABLES'].items():
        baseline_file_id = file_report.get('baseline_oid')
        if baseline_file_id:
            file_names = list(api.get_names_from_oid(file_id))
            baseline_file_names = list(api.get_names_from_oid(baseline_file_id))

            if any(name in baseline_file_names for name in file_names):
                TN += 1
            else:
                FN += 1

    return TP, FP, FN, TN


def get_triage_results(report, target_version, baseline_version):
    matched_file = 0
    matched_function = 0
    lifted_matched_function = 0
    structurally_modified = 0
    modified_operand = 0
    unmatched = 0

    for file, file_results in report['MATCHED_EXECUTABLES'].items():
        matched_file += file_results.get("Num_functions", 0)

    for file, file_results in report['UNMATCHED_EXECUTABLES'].items():
        unmatched += file_results.get("Num_functions", 0)

    for file, file_results in report['MODIFIED_EXECUTABLES'].items():
        matched_function += len(file_results['matched_funcs'])
        lifted_matched_function += len(file_results['lifted_matched_funcs'])
        structurally_modified += len(file_results['structurally_modified_funcs'])
        modified_operand += len(file_results['operand_modified_funcs'])
        unmatched += len(file_results['unmatched_target_funcs'])

    return {
        'Target': target_version,
        'Baseline': baseline_version,
        'Matched Executables': len(report["MATCHED_EXECUTABLES"]),
        'Matched Non-Executables': len(report['MATCHED_NON_EXECUTABLES']),
        'Modified Executables': len(report['MODIFIED_EXECUTABLES']),
        'Unmatched Executables': len(report['UNMATCHED_EXECUTABLES']),
        'Unmatched Non-Executables': len(report['UNMATCHED_NON_EXECUTABLES']),
        'Failed Executables': len(report['FAILED_EXECUTABLES']),
        'File-Matched Functions': matched_file,
        'Matched Functions': matched_function,
        'Lifted-Matched Function': lifted_matched_function,
        'Operand Modified Functions': modified_operand,
        'Structurally Modified Functions': structurally_modified,
        'Unmatched Functions': unmatched,
    }


def get_triage_function_results(report):
    results = {}

    for file, file_results in report['MODIFIED_EXECUTABLES'].items():
        results[file] = {
            'File': file,
            'Matched': len(file_results['matched_funcs']),
            'Lifted-Matched': len(file_results['lifted_matched_funcs']),
            'Operand-Modified': len(file_results['operand_modified_funcs']),
            'Structurally-Modified': len(file_results['structurally_modified_funcs']),
            'Unmatched': len(file_results['unmatched_target_funcs'])
        }

    return results


def get_all_file_names(collection):
    file_names = []
    oids = api.expand_oids(collection)
    for oid in oids:
        file_names += list(api.get_names_from_oid(oid))
    return file_names


def get_report(target_collection, baseline_collection):
    collection_tags = api.get_tags(target_collection)
    if collection_tags is None:
        collection_tags = {}
        api.apply_tags(target_collection, collection_tags)

    if not collection_tags or not collection_tags.get("DRIFT_DATA") or not collection_tags["DRIFT_DATA"].get(baseline_collection):
        if not collection_tags.get("DRIFT_DATA"):
            collection_tags["DRIFT_DATA"] = {}

        report = api.retrieve("pair_files", [target_collection, baseline_collection])
        collection_tags['DRIFT_DATA'][baseline_collection] = report
        api.apply_tags(target_collection, collection_tags)
    else:
        report = collection_tags['DRIFT_DATA'][baseline_collection]

    return report
