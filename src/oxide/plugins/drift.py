
from oxide.core.oxide import api
import pprint
import csv
import os 
import concurrent.futures
import os
import shutil
import tlsh
from tabulate import tabulate
import csv
from collections import defaultdict
import pandas as pd
import time
from scipy.optimize import linear_sum_assignment
import os
import pandas as pd
import numpy as np


from oxide.core import progress, api

info = """
=============================
DRIFT Plugin
=============================

This plugin provides a series of commands that perform analyze and compare 
collections (and the files within them) in the Oxide framework.

COMMANDS:
--------------------------------------------------------------------------------
compare_collections
--------------------------------------------------------------------------------
- Compares two collections.
- Generates or retrieves a DRIFT_DATA report detailing stats, new files,
  modified files, and failed files.
- Common Usage:
    - compare_collections &collection &baseline_collection
    - compare_collections &collection &baseline_collection --view=modified
    - compare_collections &collection &baseline_collection file --view=modified
    - compare_collections &collection &baseline_collection file --function=function_name
- Notable Options:
    - force: "COMPARE" re-runs the comparison if data already exists
    - view: "stats", "new", "modified", "failed"
    - function: Allows drilling down to a specific function comparison

--------------------------------------------------------------------------------
import_product
--------------------------------------------------------------------------------
- Imports a directory structure (e.g., firmware images) for a single product. 
  Each subdirectory/file is imported as its own collection named 
  "parent_directory---sample_name".
- Common Usage:
    - import_product "/path/to/product_directory"

--------------------------------------------------------------------------------
import_dataset
--------------------------------------------------------------------------------
- Similar to import_product, but designed for multiple products. Each product 
  directory can have multiple versions/subdirectories.
- Common Usage:
    - import_dataset "/path/to/dataset_root"

--------------------------------------------------------------------------------
analyze_collections
--------------------------------------------------------------------------------
- Performs the pre-processing and analysis pass for the given collections.
- Common Usage:
    - analyze_collections
    - analyze_collections &collection
- Notable Options:
    - force: Re-analyzes or re-tags as specified.
"""
print(info)

pp = pprint.PrettyPrinter()

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

def print_statistics(report, stats, target_collection, baseline_collection):
    title = f"{api.get_colname_from_oid(target_collection)} Compared to {api.get_colname_from_oid(baseline_collection)}"

    columns = [
        "Category",
        f"# of {api.get_colname_from_oid(target_collection)} Files",
        f"% of {api.get_colname_from_oid(target_collection)} Files",
    ]

    rows = []
    for key, (total, percentage) in stats.items():
        rows.append([key, total, percentage])
    
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


def print_category_w_baseline(report, files_report):
    for file_id, report in files_report.items():
        baseline_file_id = report['baseline_oid']
        similarity = report['similarity']
        if baseline_file_id:
            print_table_match(file_id, baseline_file_id, similarity)

        # Print func_matches table
        if 'matched_funcs' in report and len(report['matched_funcs']) > 0:
            print_func_matches(report)
        
        # Print modified_funcs table
        if 'modified_funcs' in report and len(report['modified_funcs']) > 0:
            # print_modified_funcs_table(report)
            print_modified_funcs_features(report)
        
        # Print unmatched_funcs table
        if 'unmatched_funcs' in report and len(report['unmatched_funcs']) > 0:
            print_unmatched_funcs(report)
        print("\n")

def save_csv_report(report, files_report, output_dir="csv_reports"):
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
    file_classification["Matched"] = files_report['MATCHED_EXECUTABLES']
    for file_id in files_report['UNMATCHED_EXECUTABLES']:
        # Retrieve file names (assumes api.get_names_from_oid exists)
        file_names = list(api.get_names_from_oid(file_id))
        if len(file_names) > 1:
            file_name_info = f"{len(file_names)} Associated File Names"
        else:
            file_name_info = file_names[0] if file_names else "Unknown"

        file_classification['Unmatched'][file_id] = file_name_info
    for file_id in files_report['REMOVED_EXECUTABLES']:
        # Retrieve file names (assumes api.get_names_from_oid exists)
        file_names = list(api.get_names_from_oid(file_id))
        if len(file_names) > 1:
            file_name_info = f"{len(file_names)} Associated File Names"
        else:
            file_name_info = file_names[0] if file_names else "Unknown"

        file_classification['Removed'][file_id] = file_name_info
    for file_id, report in files_report['MODIFIED_EXECUTABLES'].items():
        file_classification["Modified"].append(file_id)

        # --- File match info --- 
        baseline_file_id = report.get('baseline_oid')
        if baseline_file_id:

            func_class_rows.append({
                'Target File': file_id,
                'Baseline File': baseline_file_id,
                'Matched': len(report.get("matched_funcs", {})),
                "Modified": len(report.get("modified_funcs", {})),
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


def print_modified_funcs_features(report):
    columns = [
        "Function",
        "Baseline Function",
        "Score",
        "BBs +/-",
        "Instr +",
        "Instr -",
        "Instr Mod",
        "Func Calls +/-"
    ]

    # Collect data rows from the report
    rows = []
    for func, func_report in report['modified_funcs'].items():
        basic_blocks       = func_report['basic_blocks']       or 0
        instr_added        = func_report['added_instr']        or 0
        instr_removed      = func_report['removed_instr']      or 0
        instr_modified     = func_report['modified_instr']     or 0
        func_calls         = func_report['func_calls']         or 0



        rows.append([
            func_report['func_name'],
            func_report['baseline_func_name'],
            func_report['similarity'],
            basic_blocks,
            instr_added,
            instr_removed,
            instr_modified,
            func_calls
        ])

    df = pd.DataFrame(rows, columns=columns)

    numeric_cols = [
        "BBs +/-",
        "Instr +",
        "Instr -",
        "Instr Mod",
        "Func Calls +/-"
    ]
    df["Total"] = df[numeric_cols].sum(axis=1)
    df.sort_values(by="Total", ascending=False, inplace=True)
    df.drop(columns="Total", inplace=True)

    print(f"{len(report['modified_funcs'])} Modified Functions:")
    print(tabulate(df, headers='keys', tablefmt='psql', showindex=False))

def print_func_matches(report):
    print(f"{len(report['matched_funcs'])} Exact Function Matches")

def print_unmatched_funcs(report):
    num_unmatched = len(report['unmatched_funcs'])
    print(f"{num_unmatched} Unmatched Functions:")

    rows = []
    for func, details in report['unmatched_funcs'].items():
        rows.append([details])

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
    for mod_func in report['MODIFIED_EXECUTABLES'][file_oid]['modified_funcs']:
        if function == report['MODIFIED_EXECUTABLES'][file_oid]['modified_funcs'][mod_func]['func_name']:
            func_comparator = report['MODIFIED_EXECUTABLES'][file_oid]['modified_funcs'][mod_func]
            print(func_comparator)
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

    # Calculate statistics
    stats = calculate_statistics(report, api.expand_oids(target_collection))
    if view == "stats":
        print_statistics(report, stats, target_collection, baseline_collection)
    elif view == "unmatched":
        print_statistics(report, stats, target_collection, baseline_collection)
        print_unmatched_executables(report, file)
    elif view == "modified":
        print_statistics(report, stats, target_collection, baseline_collection)
        print_modified_executables(report, file)
    elif view == "failed":
        print_statistics(report, stats, target_collection, baseline_collection)
        print_failed_executable()
    else:
        print_statistics(report, stats, target_collection, baseline_collection)

    if file and function:
        print_compare_functions(file, function)

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

    file_classification_results = {}
    file_pairing_accuracy = {}

    # Keep track of the baseline version
    baseline_version = None

    p = progress.Progress(len(collections))
    for target_collection, product, target_version, version_tuple in parsed_collections:
        report = get_report(target_collection, baseline_collection)

        file_pairing_accuracy[target_version] = get_file_pairing_accuracy(report, target_version, baseline_version, baseline_collection)
        file_classification_results[target_version] = get_triage_results(report, target_version, baseline_version)

        baseline_version = target_version
        baseline_collection = target_collection
        p.tick()
    
    # Dump the dictionaries to CSV files.
    dump_to_csv(file_classification_results, 'csv_reports/file/file_classification_results.csv')
    dump_to_csv(file_pairing_accuracy, 'csv_reports/file/file_pairing_accuracy.csv')

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
        sample_name = f"{sample}"
        import_sample(sample_name, sample_path)

def import_dataset(args, opts):
    dir_path = args[0]

    # Check if the provided path is a valid directory
    if not os.path.isdir(dir_path):
        raise ShellSyntaxError("Enter a valid directory with firmware from devices")
    
    results = {}

    def import_sample(sample_name, sample_path):
        """Helper function to import a directory or file and create a collection."""
        oids, new_files = (
            api.import_directory(sample_path) if os.path.isdir(sample_path)
            else api.import_file(sample_path)
        )
        result = api.create_collection(sample_name, oids, oids)
        results[sample_name] = result

    # Iterate over product directories in the given directory
    for product in os.listdir(dir_path):
        product_path = os.path.join(dir_path, product)

        # Skip if it's not a directory
        if not os.path.isdir(product_path):
            continue

        # Iterate over versions or samples within the product directory
        for sample in os.listdir(product_path):
            sample_path = os.path.join(product_path, sample)

            # Create the sample_name as "product_name-version_name"
            sample_name = f"{product}---{sample}"
            import_sample(sample_name, sample_path)

exports = [
    compare_collections, 
    import_product, 
    import_dataset, 
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

# Helper function to dump a dictionary of dictionaries to CSV.
def dump_to_csv(data_dict, filename):
    if not data_dict:
        print(f"No data to dump for {filename}")
        return
    # Assume each inner dictionary has the same keys; get headers from the first entry.
    headers = list(next(iter(data_dict.values())).keys())
    with open(filename, 'w', newline='') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=headers)
        writer.writeheader()
        for row in data_dict.values():
            writer.writerow(row)

def get_file_pairing_accuracy(files_report, target_version, baseline_version, baseline_collection, output_dir="csv_reports"):
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
    modified = 0
    unmatched = 0
    total_funcs = 0

    results = {}

    for file, results in report['MATCHED_EXECUTABLES'].items():
        num_functions = results.get("Num_functions", 0)
        total_funcs += num_functions
        unmatched += num_functions
    
    for file, results in report['UNMATCHED_EXECUTABLES'].items():
        num_functions = results.get("Num_functions", 0)
        unmatched += num_functions
        total_funcs += num_functions

    for file, results in report['MODIFIED_EXECUTABLES'].items():
        modified += len(results['modified_funcs'])
        unmatched += len(results['unmatched_funcs'])

        total_funcs += len(results['matched_funcs'])
        total_funcs += len(results['modified_funcs'])
        total_funcs += len(results['unmatched_funcs'])

    results = {
            'Target': target_version,
            'Baseline': baseline_version,
            'Matched Executables': len(report["MATCHED_EXECUTABLES"]),
            'Matched Non-Executables': len(report['MATCHED_NON_EXECUTABLES']),
            'Modified Executables': len(report['MODIFIED_EXECUTABLES']),
            'Unmatched Executables': len(report['UNMATCHED_EXECUTABLES']),
            'Unmatched Non-Executables': len(report['UNMATCHED_NON_EXECUTABLES']),
            'Failed Executables': len(report['FAILED_EXECUTABLES']),
            'Modified Functions': modified,
            'Unmatched Functions': unmatched,
            'Total Functions': total_funcs
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
        report = collection_tags['DRIFT_DATA'].get(baseline_collection)

    return report