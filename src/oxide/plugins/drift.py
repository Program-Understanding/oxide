
from oxide.core.oxide import api
import csv
import os 
from tabulate import tabulate
import csv
import pandas as pd
import os
import datetime
import time

from oxide.core import progress, api

info = """
=============================
DRIFT Plugin for Oxide
=============================

This plugin provides a suite of commands for importing, analyzing, and comparing 
collections within the Oxide reverse engineering framework. It is specifically 
designed to triage a firmware sample against a baseline firmware sample at both the file and function level.

AVAILABLE COMMANDS
--------------------------------------------------------------------------------
compare_collections
--------------------------------------------------------------------------------
Compare two collections and generate or retrieve a DRIFT_DATA report capturing:
  - File-level matches, modifications, and failures
  - Function-level matches, modifications (structural and operand), and unmatched functions

Usage Examples:
  - compare_collections &target &baseline
  - compare_collections &target &baseline --view=modified
  - compare_collections &target &baseline file --view=modified
  - compare_collections &target &baseline file --function=function_name

Options:
  --view=<mode>     View mode: stats | unmatched | modified | failed
  --function=<name> Compare a specific function (requires a file)
  --force           Re-run comparison even if report already exists

Output:
  - Summary statistics
  - Unified diffs for selected functions
  - CSV reports written to `drift_reports/compare_collections/`

--------------------------------------------------------------------------------
compare_collections_series
--------------------------------------------------------------------------------
Compare a time-ordered sequence of collections for a given product. Reports:
  - File pairing accuracy (Precision, Recall, F1)
  - Function-level triage summaries
  - Elapsed time per comparison

Usage:
  - compare_collections_series --filter=<product_prefix>

Output:
  - CSV reports written to `drift_reports/compare_collections_series/`

--------------------------------------------------------------------------------
import_product
--------------------------------------------------------------------------------
Import multiple firmware samples for a single product. Each subdirectory is treated 
as a versioned sample and stored as an Oxide collection.

Usage:
  - import_product "/path/to/product_dir"

Naming:
  - Collection names follow the format: <product>-v<sample_name>
"""
print(info)

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
        f"Total",
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


def print_category_w_baseline(report):
    for file_id, report in report.items():
        baseline_file_id = report['baseline_oid']
        similarity = report['similarity']
        if baseline_file_id:
            print_table_match(file_id, baseline_file_id, similarity)

        print_func_matches(report)
        
        # Print structurally_modified_funcs table
        if 'structurally_modified_funcs' in report and len(report['structurally_modified_funcs']) > 0:
            print_structurally_modified_features(report)

        # Print operand_modified_funcs table
        if 'operand_modified_funcs' in report and len(report['operand_modified_funcs']) > 0:
            print_operand_modified_features(report)
        
        # Print unmatched_funcs table
        if 'unmatched_funcs' in report and len(report['unmatched_funcs']) > 0:
            print_unmatched_funcs(report)
        print("\n")

def save_csv_report(report, output_dir="drift_reports"):
    os.makedirs(output_dir, exist_ok=True)
    
    # Lists to store data for each report type
    file_pairing_rows = []
    file_classification = {
        'Matched': [],
        'Modified': [],
        "Unmatched": {},
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
    for file_id, report in report['MODIFIED_EXECUTABLES'].items():
        file_classification["Modified"].append(file_id)

        # --- File match info --- 
        baseline_file_id = report.get('baseline_oid')
        if baseline_file_id:

            func_class_rows.append({
                'Target File': file_id,
                'Baseline File': baseline_file_id,
                'Matched': len(report.get("matched_funcs", {})),
                "Modified": len(report.get("structurally_modified_funcs", {})),
                'Unmatched': len(report.get("unmatched_funcs", {}))
            })

            # Retrieve file names (assumes api.get_names_from_oid exists)F
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


def print_structurally_modified_features(report):
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

    # Collect data rows from the report
    rows = []
    for func, func_report in report['structurally_modified_funcs'].items():
        basic_blocks = func_report['basic_blocks'] or 0
        instr_added = func_report['added_instr'] or 0
        instr_removed = func_report['removed_instr'] or 0
        instr_modified_opcode = func_report['modified_opcode_instr'] or 0
        instr_modified_operand = func_report['modified_operand_instr'] or 0
        func_calls = func_report['func_calls'] or 0



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

    print(f"{len(report['structurally_modified_funcs'])} Structurally-Modified Functions:")
    print(tabulate(df, headers='keys', tablefmt='psql', showindex=False))

def print_operand_modified_features(report):
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

    # Collect data rows from the report
    rows = []
    for func, func_report in report['operand_modified_funcs'].items():
        basic_blocks = func_report['basic_blocks'] or 0
        instr_added = func_report['added_instr'] or 0
        instr_removed = func_report['removed_instr'] or 0
        instr_modified_opcode = func_report['modified_opcode_instr'] or 0
        instr_modified_operand = func_report['modified_operand_instr'] or 0
        func_calls = func_report['func_calls'] or 0



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

    print(f"{len(report['operand_modified_funcs'])} Operand Modified Functions:")
    print(tabulate(df, headers='keys', tablefmt='psql', showindex=False))

def print_func_matches(report):
    print(f"{len(report['matched_funcs'])} Exact Function Matches")
    print(f"{len(report['lifted_matched_funcs'])} Lifted-Function Matches")

def print_unmatched_funcs(report):
    num_unmatched = len(report['unmatched_funcs'])
    print(f"{num_unmatched} Unmatched Functions:")

    for func, details in report['unmatched_funcs'].items():
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
    for mod_func in report['MODIFIED_EXECUTABLES'][file_oid]['structurally_modified_funcs']:
        if function == report['MODIFIED_EXECUTABLES'][file_oid]['structurally_modified_funcs'][mod_func]['func_name']:
            func_comparator = report['MODIFIED_EXECUTABLES'][file_oid]['structurally_modified_funcs'][mod_func]
            u_diff = api.retrieve("function_unified_diff", [file_oid, func_comparator['baseline_file']], {"function": func_comparator['func_name'], "baseline_function": func_comparator['baseline_func_name']})

            for line in u_diff['unified_diff']:
                print(line)     
    for mod_func in report['MODIFIED_EXECUTABLES'][file_oid]['operand_modified_funcs']:
        if function == report['MODIFIED_EXECUTABLES'][file_oid]['operand_modified_funcs'][mod_func]['func_name']:
            func_comparator = report['MODIFIED_EXECUTABLES'][file_oid]['operand_modified_funcs'][mod_func]
            u_diff = api.retrieve("function_unified_diff", [file_oid, func_comparator['baseline_file']], {"function": func_comparator['func_name'], "baseline_function": func_comparator['baseline_func_name']})

            for line in u_diff['unified_diff']:
                print(line)     

def compare_collections(args, opts):
    if len(args) < 2:
        print("ERROR: Enter two collections to compare")
        return

    view = opts.get('view', None)

    file = None
    function = opts.get('function', None)

    valid, invalid = api.valid_oids(args)
    target_collection, baseline_collection = valid[0], valid[1]

    if len(valid) == 3:
        file = valid[2]

    report = get_report(target_collection, baseline_collection)

    triage_results = {}
    triage_results[target_collection] = get_triage_results(report, target_collection, baseline_collection)
    time_stamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    dump_to_csv(triage_results , f'drift_reports/compare_collections/{target_collection}/{time_stamp}/triage_results.csv')

    triage_function_results = {}
    triage_function_results = get_triage_function_results(report)
    dump_to_csv(triage_function_results, f'drift_reports/compare_collections/{target_collection}/{time_stamp}/function_triage_results.csv')

    # Calculate statistics
    # stats = calculate_statistics(report, api.expand_oids(target_collection))
    if view == "stats":
        print_triage_results(triage_results, target_collection, baseline_collection)
    elif view == "unmatched":
        print_triage_results(triage_results, target_collection, baseline_collection)
        print_unmatched_executables(report, file)
    elif view == "modified":
        print_triage_results(triage_results, target_collection, baseline_collection)
        print_modified_executables(report, file)
    elif view == "failed":
        print_triage_results(triage_results, target_collection, baseline_collection)
        print_failed_executable()
    else:
        print_triage_results(triage_results, target_collection, baseline_collection)

    if file and function:
        print_compare_functions(report, file, function)

def compare_collections_series(args, opts):
    # Assume get_collections returns a list of collection IDs
    collections = get_collections(args, opts)
    parsed_collections = []
    for target_collection in collections:
        product, target_version = split_collection(api.get_colname_from_oid(target_collection))
        version_tuple = tuple(map(int, target_version.split('.')))
        parsed_collections.append((target_collection, product, target_version, version_tuple))
    # Sort by version tuple
    parsed_collections.sort(key=lambda x: x[3])
    baseline_collection = None

    triage_results = {}
    file_pairing_accuracy = {}

    # Keep track of the baseline version
    baseline_version = None

    p = progress.Progress(len(collections))
    for target_collection, product, target_version, version_tuple in parsed_collections:
        # Record the start time for generating the report
        start_time = time.time()
        report = get_report(target_collection, baseline_collection)
        end_time = time.time()
        
        file_pairing_accuracy[target_version] = get_file_pairing_accuracy(
            report, target_version, baseline_version, baseline_collection)
        triage_results[target_version] = get_triage_results(
            report, target_version, baseline_version)
        
        triage_results[target_version]['time(s)'] = end_time - start_time

        baseline_version = target_version
        baseline_collection = target_collection
        p.tick()
    
    # Dump the dictionaries to CSV files.
    time_stamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    dump_to_csv(triage_results, f'drift_reports/compare_collections_series/{time_stamp}/triage_results.csv')
    dump_to_csv(file_pairing_accuracy, f'drift_reports/compare_collections_series/{time_stamp}/file_pairing_accuracy.csv')

def import_product(args, opts):
    dir_path = args[0]

    # Check if the provided path is a valid directory
    if not os.path.isdir(dir_path):
        raise ShellSyntaxError("Enter a valid directory with firmware from devices")

    def import_sample(sample_name, sample_path):
        """Helper function to import a directory or file and create a collection."""
        oids, new_files = (
            api.import_directory(sample_path) if os.path.isdir(sample_path)
            else api.import_file(sample_path)
        )
        api.create_collection(sample_name, oids, oids)

    # Get the parent directory name
    parent_directory_name = os.path.basename(os.path.abspath(dir_path))

    # Iterate over samples in the directory and import them
    for sample in os.listdir(dir_path):
        sample_path = os.path.join(dir_path, sample)
        # Create the sample_name as "parent_directory-directory_name"
        sample_name = f"{parent_directory_name}-v{sample}"
        import_sample(sample_name, sample_path)

exports = [
    compare_collections, 
    import_product, 
    compare_collections_series]

############################
### SUPPORTING FUNCTIONS ###
############################

def get_collections(args=None, opts=None):
    """
    Process collections based on provided arguments or a filter.

    Parameters:
        api (object): The API object that provides necessary methods.
        args (list or None): List of arguments to validate and expand OIDs.
        opts (dict or None): Options that may include a 'force' filter.

    Returns:
        list: A list of processed collections.
    """
    # Default options to an empty dictionary if None
    opts = opts or {}

    collections = []

    if args:
        valid, invalid = api.valid_oids(args)
        collections = valid
    else:
        # Handle case when no arguments are provided
        filter_value = opts.get('filter')
        if filter_value:
            # Retrieve all collection CIDs
            all_collections = api.collection_cids()
            for collection in all_collections:
                # Get collection name and check the filter
                collection_name = api.get_colname_from_oid(collection)
                if collection_name.startswith(filter_value):
                    collections.append(collection)
            
            if not collections:
                # Print a message and return empty list if no matches
                print("No collection matches for filter")
                return []
        else:
            # Default case: retrieve all collection CIDs
            for c in api.collection_cids():
                collections.append(c)

    return collections

def split_collection(input_string):
    # Split the string on the rightmost occurrence of '-'
    parts = input_string.rsplit('-v', maxsplit=1)
    
    # Check if the delimiter was found and return both parts
    if len(parts) == 2:
        return parts[0], parts[1]
    else:
        return parts[0], None  # Return None if the delimiter is not found

def calculate_stats(part, total):
    if part is not int:
        return len(part), f"{round((len(part) / len(total)) * 100, 2)}%"

def dump_to_csv(data_dict, filename):
    if not data_dict:
        print(f"No data to dump for {filename}")
        return

    # Check if the first value is a dict or not
    first_value = next(iter(data_dict.values()))
    if isinstance(first_value, dict):
        headers = list(first_value.keys())
        rows = list(data_dict.values())
    else:
        # For simple values, use 'key' and 'value' as headers
        headers = ['key', 'value']
        rows = [{'key': k, 'value': v} for k, v in data_dict.items()]
    
    # Ensure directory exists
    os.makedirs(os.path.dirname(filename), exist_ok=True)
    
    with open(filename, 'w', newline='') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=headers)
        writer.writeheader()
        writer.writerows(rows)


def get_file_pairing_accuracy(files_report, target_version, baseline_version, baseline_collection, output_dir="drift_reports"):
    os.makedirs(output_dir, exist_ok=True)

    result = {}

    TP = 0
    FP = 0
    FN = 0

    if baseline_collection:
        baseline_col_file_names = get_all_file_names(baseline_collection)
    else:
        baseline_col_file_names = []

    for file_id, report in files_report['MODIFIED_EXECUTABLES'].items():
        # --- File match info --- 
        baseline_file_id = report.get('baseline_oid')
        if baseline_file_id:
            # Retrieve file names (assumes api.get_names_from_oid exists)
            file_names = list(api.get_names_from_oid(file_id))
            baseline_file_names = list(api.get_names_from_oid(baseline_file_id))

            # Check if at least one element in file_names is in baseline_file_names.
            if any(name in baseline_file_names for name in file_names):
                TP += 1
            else:
                # Check if a pair exists
                if any(name in baseline_col_file_names for name in file_names):
                    FN += 1
                else:
                    FP += 1

    # Calculate precision, recall and F1 score safely (handle division by zero)
    precision = TP / (TP + FP) if (TP + FP) > 0 else 0
    recall = TP / (TP + FN) if (TP + FN) > 0 else 0
    f1 = 2 * (precision * recall) / (precision + recall) if (precision + recall) > 0 else 0

    result = {
        'Version': target_version,
        'Baseline Version': baseline_version,
        'TP': TP,
        'FP': FP,
        'FN': FN,
        'Precision': precision,
        'Recall': recall,
        'F1': f1
    }

    return result

def get_file_classification_accuracy(report, baseline_collection):
    TP = 0
    FP = 0
    FN = 0
    TN = 0

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

    for file_id, report in report['MODIFIED_EXECUTABLES'].items():
        baseline_file_id = report.get('baseline_oid')
        if baseline_file_id:
            file_names = list(api.get_names_from_oid(file_id))
            baseline_file_names = list(api.get_names_from_oid(baseline_file_id))

            # Check if at least one element in file_names is in baseline_file_names.
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
    matched_file = 0
    total_funcs = 0

    results = {}

    for file, file_results in report['MATCHED_EXECUTABLES'].items():
        matched_file += file_results.get("Num_functions", 0)
    
    for file, file_results in report['UNMATCHED_EXECUTABLES'].items():
        unmatched += file_results.get("Num_functions", 0)

    for file, file_results in report['MODIFIED_EXECUTABLES'].items():
        matched_function += len(file_results['matched_funcs'])
        lifted_matched_function += len(file_results['lifted_matched_funcs'])
        structurally_modified += len(file_results['structurally_modified_funcs'])
        modified_operand += len(file_results['operand_modified_funcs'])
        unmatched += len(file_results['unmatched_funcs'])

    results = {
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
            'Structuraly Modified Functions': structurally_modified,
            'Unmatched Functions': unmatched,
        }

    return results

def get_triage_function_results(report):
    results = {}

    for file, file_results in report['MODIFIED_EXECUTABLES'].items():
        results[file] = {}
        results[file]['File'] = file
        results[file]['Matched'] = len(file_results['matched_funcs'])
        results[file]['Lifted-Matched'] = len(file_results['lifted_matched_funcs'])
        results[file]['Operand-Modified'] = len(file_results['operand_modified_funcs'])
        results[file]['Structurally-Modified'] = len(file_results['structurally_modified_funcs'])   
        results[file]['Unmatched'] = len(file_results['unmatched_funcs'])

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
        report = collection_tags['DRIFT_DATA'].get(baseline_collection)

    return report