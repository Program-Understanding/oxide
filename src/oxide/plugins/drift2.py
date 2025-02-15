
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
import numpy as np

import numpy as np
from sklearn.preprocessing import MinMaxScaler
from sklearn.metrics.pairwise import cosine_similarity
from scipy.optimize import linear_sum_assignment
from sklearn.preprocessing import StandardScaler, normalize
from sklearn.preprocessing import PowerTransformer, StandardScaler, normalize, RobustScaler


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
- Generates or retrieves a FRAMEWORK_DATA report detailing stats, new files,
  modified files, and failed files.
- Common Usage:
    - compare_collections &collection &ref_collection
    - compare_collections &collection &ref_collection --view=modified
    - compare_collections &collection &ref_collection file --view=modified
    - compare_collections &collection &ref_collection file --function=function_name
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

TIMEOUT_SHORT = 200
TIMEOUT_LONG = 500

class FileAnalyzer:
    def __init__(self, oid, force=None):
        self.oid = oid
        self.force = force
        self.tags = self.get_or_default_tags()

    def get_or_default_tags(self):
        """Retrieve existing tags or return an empty dictionary."""
        return api.get_tags(self.oid) or {}

    def tag_src_type(self):
        if "SRC_TYPE" not in self.tags or self.force == "SRC_TYPE":
            self.tags["SRC_TYPE"] = api.get_field("src_type", self.oid, "type").pop()

    def tag_extension(self):
        if "EXT" not in self.tags or self.force == "EXT":
            file_name = api.get_field("file_meta", self.oid, "names").pop()
            file_extension = os.path.splitext(file_name)[1][1:]
            self.tags["EXT"] = file_extension if file_extension else "None"

    def tag_file_category(self):
        if "FILE_CATEGORY" not in self.tags or self.force == "FILE_CATEGORY":
            self.tags["FILE_CATEGORY"] = api.get_field("categorize", self.oid, self.oid)

    def tag_function_tlsh(self):
        if "FUNC_TLSH" not in self.tags or self.force == "FUNC_TLSH":
            self.tags.get("FUNC_HASH", None)
            self.tags["FUNC_TLSH"] = api.retrieve("function_tlsh", self.oid, {"replace_addrs": True})

class CollectionComparator:
    def __init__(self, collection, ref_collection) -> None:
        self.collection = collection
        self.collection_tags = api.get_tags(self.collection)
        self.collection_oids = set(api.expand_oids(self.collection))
        self.collection_exes, self.collection_non_exes = self._separate_oids(self.collection_oids)
        self.collection_funcs = {}

        self.ref_collection = ref_collection
        if self.ref_collection:
            self.ref_collection_tags = api.get_tags(self.ref_collection)
            self.ref_collection_oids = set(api.expand_oids(self.ref_collection))
            self.ref_collection_exes, self.ref_collection_non_exec = self._separate_oids(self.ref_collection_oids)  
            self.ref_collection_funcs = {}
            self.all_ref_collection_funcs = self._get_all_functions(self.ref_collection_exes)
        else:       
            self.ref_collection_tags = []
            self.ref_collection_oids = []
            self.ref_collection_exes = []
            self.ref_collection_non_exec = []

        self.match_count = 0
        self.mismatch_count = 0

    def _separate_oids(self, oids):
        executables, non_executables = set(), set()
        for oid in oids:
            tags = api.get_tags(oid) or {}
            if tags.get("FILE_CATEGORY") == "executable":
                executables.add(oid)
            else:
                non_executables.add(oid)
        return executables, non_executables

    def _seperate_funcs(self):
        self.collection_funcs = separate_uniq_repeated(self.uniq_col_exes)
        self.ref_collection_funcs = separate_uniq_repeated(self.unmatched_ref_exes)

    # def _classify_files(self):
    #     """Pairs `oid` files with the best `ref_oid` files based on similarity scores, handling different list sizes."""
        
    #     self.modified_exes = {}
    #     self.unmatched_oids = set(self.uniq_col_exes)
    #     self.unmatched_ref_oids = set(self.unmatched_ref_exes)
    #     self.failed_exes = []

    #     oid_list = list(self.uniq_col_exes)
    #     ref_oid_list = list(self.unmatched_ref_exes)
    #     len_A, len_B = len(oid_list), len(ref_oid_list)

    #     # Step 1: Retrieve feature vectors for all files
    #     file_vectors = {}

    #     for oid in oid_list + ref_oid_list:
    #         vector = api.retrieve("file_vector", oid)
    #         if vector is None:
    #             self.failed_exes.append(oid)
    #             continue
    #         file_vectors[oid] = np.array(vector)

    #     if not file_vectors:
    #         return

    #     # Ensure all vectors have the same length
    #     max_length = max(len(v) for v in file_vectors.values())
    #     for k in file_vectors.keys():
    #         file_vectors[k] = np.pad(file_vectors[k], (0, max_length - len(file_vectors[k])), 'constant')

    #     # Create feature matrix in a well-defined order
    #     ordered_keys = oid_list + ref_oid_list
    #     feature_matrix = np.array([file_vectors[k] for k in ordered_keys])

    #     # Step 2: Normalize All Feature Vectors Together
    #     scaler = RobustScaler()
    #     scaled_matrix = scaler.fit_transform(feature_matrix)
    #     normalized_matrix = normalize(scaled_matrix, norm='l2')

    #     # Step 3: Compute Pairwise Similarity
    #     full_similarity = cosine_similarity(normalized_matrix)
    #     similarity_matrix = full_similarity[:len_A, len_A:]

    #     if similarity_matrix.size == 0:
    #         return

    #     # Step 4: Compute Adaptive Outlier-Based Threshold
    #     outlier_threshold = self.compute_outlier_threshold(similarity_matrix)

    #     # Step 5: Handle Unequal Lists with High Penalty Padding
    #     max_size = max(len_A, len_B)
    #     if len_A < max_size:
    #         padding = np.full((max_size - len_A, len_B), 1000)
    #         similarity_matrix = np.vstack([similarity_matrix, padding])
    #         oid_list += [f"DUMMY_A_{i}" for i in range(max_size - len_A)]
    #     if len_B < max_size:
    #         padding = np.full((max_size, max_size - len_B), 1000)
    #         similarity_matrix = np.hstack([similarity_matrix, padding])
    #         ref_oid_list += [f"DUMMY_B_{i}" for i in range(max_size - len_B)]

    #     # Step 6: Convert to Cost Matrix
    #     cost_matrix = np.where(similarity_matrix >= 0, 1 - similarity_matrix, 1000)

    #     # Step 7: Apply Hungarian Algorithm
    #     row_ind, col_ind = linear_sum_assignment(cost_matrix)

    #     # Step 8: Assign Matches
    #     for i, j in zip(row_ind, col_ind):
    #         oid, ref_oid = oid_list[i], ref_oid_list[j]
    #         best_score = similarity_matrix[i, j]

    #         if "DUMMY" not in oid and "DUMMY" not in ref_oid:
    #             if best_score < outlier_threshold:
    #                 print(f"Potential Addition/Removal: {oid} ↔ {ref_oid} (Score: {best_score})")
    #             else:
    #                 self.modified_exes[oid] = {"ref_oid": ref_oid, "similarity": best_score}
    #                 self.unmatched_oids.discard(oid)
    #                 self.unmatched_ref_oids.discard(ref_oid)


    def _classify_files(self):
        """Pairs `oid` files with the best `ref_oid` files based on TLSH similarity, handling different list sizes."""

        self.modified_exes = {}
        self.unmatched_oids = set(self.uniq_col_exes)
        self.unmatched_ref_oids = set(self.unmatched_ref_exes)
        self.failed_exes = []

        oid_list = list(self.uniq_col_exes)
        ref_oid_list = list(self.unmatched_ref_exes)
        len_A, len_B = len(oid_list), len(ref_oid_list)

        # Step 1: Retrieve TLSH Hashes for All Files
        file_hashes = {}

        for oid in oid_list + ref_oid_list:
            tlsh_hash = api.retrieve("file_tlsh", oid)
            if not tlsh_hash or tlsh_hash == "TNULL":  # Handle invalid hashes
                self.failed_exes.append(oid)
                continue
            file_hashes[oid] = tlsh_hash

        if not file_hashes:
            return

        # Create TLSH similarity matrix
        similarity_matrix = np.full((len_A, len_B), 1000)  # Initialize with high cost

        for i, oid in enumerate(oid_list):
            for j, ref_oid in enumerate(ref_oid_list):
                hashA = file_hashes.get(oid)
                hashB = file_hashes.get(ref_oid)

                if hashA and hashB:
                    tlsh_distance = tlsh.diff(hashA, hashB)
                    similarity_matrix[i, j] = tlsh_distance  # Lower distance = more similar

        # Step 3: Apply Hungarian Algorithm to Find Best Matches
        row_ind, col_ind = linear_sum_assignment(similarity_matrix)

        # Step 4: Assign Matches Based on TLSH Distance
        threshold = 50  # TLSH distance threshold (adjustable)
        
        for i, j in zip(row_ind, col_ind):
            oid, ref_oid = oid_list[i], ref_oid_list[j]
            tlsh_distance = similarity_matrix[i, j]

            if tlsh_distance < threshold:  # Lower values mean more similarity
                self.modified_exes[oid] = {
                    "ref_oid": ref_oid,
                    "similarity": tlsh_distance
                }
                self.unmatched_oids.discard(oid)
                self.unmatched_ref_oids.discard(ref_oid)
    
    def compute_outlier_threshold(self, similarity_matrix):
        """ Compute an adaptive threshold using IQR-based outlier detection. """
        valid_scores = similarity_matrix[similarity_matrix >= 0]  # Ignore dummy values

        if valid_scores.size < 5:  # Too few values to compute outliers reliably
            return 0.6  # Default threshold

        q1 = np.percentile(valid_scores, 25)
        q3 = np.percentile(valid_scores, 75)
        iqr = q3 - q1

        lower_bound = q1 - 1.5 * iqr  # Define lower outlier threshold

        return max(lower_bound, 0.4)  # Ensure it doesn't go below 0.4

    def _match_functions(self):
        oids = list(self.modified_exes.keys())
        for oid in oids:
            self._pair_modified_functions(oid)

    def _get_all_functions(self, oids):
        functions = []
        for oid in oids:
            funcs = api.get_tags(oid).get("FUNC_TLSH")
            if funcs:
                functions += funcs
        return functions

    def _pair_modified_functions(self, oid):
        """
        Identify modified functions by comparing them with reference functions and 
        classify them based on their match scores.
        """
        ref_oid = self.modified_exes[oid]['ref_oid']

        pair_results = api.retrieve("pair_functions", [oid, ref_oid])

        self.modified_exes[oid]['matched_funcs'] = pair_results['matched_funcs']
        self.modified_exes[oid]['modified_funcs'] = pair_results['modified_funcs']
        self.modified_exes[oid]['unmatched_funcs'] = pair_results['unmatched_funcs']

        for func_addr, func in self.modified_exes[oid]['modified_funcs'].items():
            diff_features = api.retrieve("function_diff_features", [oid, ref_oid], {"functionA": func['func_name'], "functionB": func['ref_func_name']})
            for feature, value in diff_features.items():
                self.modified_exes[oid]['modified_funcs'][func_addr][feature] = value

    def generate_report(self):
        """Generate report data for file matches."""
        self.matched_exes, self.uniq_col_exes, self.unmatched_ref_exes = file_matches(self.collection_exes, self.ref_collection_exes)
        self.matched_non_exes, self.uniq_col_non_exes, self.uniq_ref_non_exes = file_matches(self.collection_non_exes, self.ref_collection_non_exec)
        self._seperate_funcs()
        self._classify_files()
        self._match_functions()
        self.collection_report = {
            'EXECUTABLE_MATCHES': self.matched_exes,
            'NON_EXECUTABLE_MATCHES': self.matched_non_exes,
            'MODIFIED_EXECUTABLES': self.modified_exes,
            'UNMATCHED_EXECUTABLES': self.unmatched_oids,
            'UNMATCHED_NON_EXECUTABLES': self.uniq_col_non_exes,
            'FAILED_EXECUTABLES': self.failed_exes
        }

    def calculate_statistics(self):
        """Calculate statistics for each category in the report."""
        return {
            'MATCHED EXECUTABLES': calculate_stats(self.collection_report["EXECUTABLE_MATCHES"], self.collection_oids),
            'MATCHED NON-EXECUTABLE': calculate_stats(self.collection_report['NON_EXECUTABLE_MATCHES'], self.collection_oids),
            'MODIFIED EXECUTABLES': calculate_stats(self.collection_report['MODIFIED_EXECUTABLES'], self.collection_oids),
            'UNMATCHED EXECUTABLES': calculate_stats(self.collection_report['UNMATCHED_EXECUTABLES'], self.collection_oids),
            'UNMATCHED NON-EXECUTABLES': calculate_stats(self.collection_report['UNMATCHED_NON_EXECUTABLES'], self.collection_oids),
            'FAILED EXECUTABLES': calculate_stats(self.collection_report['FAILED_EXECUTABLES'], self.collection_oids)
        }
    
    def print_statistics(self, stats):
        title = f"{api.get_colname_from_oid(self.collection)} Compared to {api.get_colname_from_oid(self.ref_collection)}"

        columns = [
            "Category",
            f"# of {api.get_colname_from_oid(self.collection)} Files",
            f"% of {api.get_colname_from_oid(self.collection)} Files",
        ]

        rows = []
        for key, (total, percentage) in stats.items():
            rows.append([key, total, percentage])
        
        df = pd.DataFrame(rows, columns=columns)
        
        print(title)
        print(tabulate(df, headers='keys', tablefmt='psql', showindex=False))

    def print_pairing_results(self):
        # Prepare data structures
        results = []

        total_stats = {
            'pair_correct': 0,
            'pair_incorrect': 0,
            'classify_TP': 0,
            'classify_FP': 0,
            'classify_FN': 0,
            'classify_TN': 0,
        }

        # Iterate over files in the collection report
        for file_id, report in self.collection_report['MODIFIED_EXECUTABLES'].items():
            file_stats = {
                'pair_correct': 0,
                'pair_incorrect': 0,
                'classify_TP': 0,
                'classify_FP': 0,
                'classify_FN': 0,
                'classify_TN': 0,
            }

            ref_file_id = report['ref_oid']

            # Get sets of function names
            func_names = set(api.get_tags(file_id).get("FUNC_TLSH", {}).values())
            ref_func_names = set(api.get_tags(ref_file_id).get("FUNC_TLSH", {}).values())

            for func, func_report in report['matched_funcs'].items():
                file_stats['classify_TP'] += 1
                file_stats['pair_correct'] += 1

            # Process modified functions
            for func, func_report in report['modified_funcs'].items():
                if func in ref_func_names:
                    file_stats['classify_TP'] += 1
                else:
                    file_stats['classify_FP'] += 1

                if func == func_report['ref_func_name']:
                    file_stats['pair_correct'] += 1
                else:
                    file_stats['pair_incorrect'] += 1

            # Process unmatched functions
            for func, func_report in report['unmatched_funcs'].items():
                if func in func_names and func not in ref_func_names:
                    file_stats['classify_TN'] += 1
                else:
                    file_stats['classify_FN'] += 1

            # Update totals
            for key in total_stats:
                total_stats[key] += file_stats[key]

            # Calculate per-file metrics
            TP = file_stats['classify_TP']
            FP = file_stats['classify_FP']
            FN = file_stats['classify_FN']
            TN = file_stats['classify_TN']
            num_pairs = TP + FN
            classify_correct = TP + TN
            num_funcs = TP + FN + FP + TN

            precision = TP / (TP + FP) if (TP + FP) != 0 else 0.0
            recall = TP / (TP + FN) if (TP + FN) != 0 else 0.0
            accuracy = (TP + TN) / (TP + FP + TN + FN) if (TP + FP + TN + FN) != 0 else 0.0
            f1 = (2 * precision * recall) / (precision + recall) if (precision + recall) != 0 else 0.0

            # Collect row data for this file
            results.append({
                'file_id': file_id,
                '# Paired Correctly': file_stats['pair_correct'],
                '# of Function Pairs': num_pairs,
                '% Paired Correctly': (file_stats['pair_correct'] / num_pairs) * 100 if num_pairs else 0.0,
                '# Classified Correctly': classify_correct,
                '% Classified Correctly': (classify_correct / num_funcs) * 100 if num_funcs else 0.0,
                'Precision': precision,
                'Recall': recall,
                'Accuracy': accuracy,
                'F1': f1
            })

        # Build a DataFrame for per-file results
        file_stats_df = pd.DataFrame(results)

        # Compute totals and overall metrics

        total_TP = total_stats['classify_TP']
        total_FP = total_stats['classify_FP']
        total_FN = total_stats['classify_FN']
        total_TN = total_stats['classify_TN']
        total_pairs = total_TP + total_FN

        total_classify_correct = total_TP + total_TN
        total_classify_incorrect = total_FP + total_FN
        total_classify_total = total_classify_correct + total_classify_incorrect

        overall_precision = total_TP / (total_TP + total_FP) if (total_TP + total_FP) != 0 else 0.0
        overall_recall = total_TP / (total_TP + total_FN) if (total_TP + total_FN) != 0 else 0.0
        overall_accuracy = (total_TP + total_TN) / (total_TP + total_FP + total_TN + total_FN) if (total_TP + total_FP + total_TN + total_FN) != 0 else 0.0
        overall_f1 = (2 * overall_precision * overall_recall) / (overall_precision + overall_recall) if (overall_precision + overall_recall) != 0 else 0.0

        # Create a one-row DataFrame for the overall totals
        overall_row = pd.DataFrame([{
            'file_id': 'OVERALL',
            '# Paired Correctly': total_stats['pair_correct'],
            '# of Function Pairs': total_pairs,
            '% Paired Correctly': (total_stats['pair_correct'] / total_pairs) * 100 if total_pairs else 0.0,
            '# Classified Correctly': total_classify_correct,
            '% Classified Correctly': (total_classify_correct / total_classify_total) * 100 if total_classify_total else 0.0,
            'Precision': overall_precision,
            'Recall': overall_recall,
            'Accuracy': overall_accuracy,
            'F1': overall_f1
        }])

        # Separate pair stats and classify stats into different DataFrames
        pair_cols = ['file_id', '# Paired Correctly', '# of Function Pairs', '% Paired Correctly']
        classify_cols = ['file_id', '# Classified Correctly', '% Classified Correctly', 'Precision', 'Recall', 'Accuracy', 'F1']

        # Build per-file pair stats DataFrame
        pair_stats_df = file_stats_df[pair_cols].copy()
        # Build per-file classify stats DataFrame
        classify_stats_df = file_stats_df[classify_cols].copy()

        # Build overall row subsets
        pair_overall_row = overall_row[pair_cols].copy()
        classify_overall_row = overall_row[classify_cols].copy()
        
        print("\nPer-File")
        print("Pairing Stats")
        print(tabulate(pair_stats_df, headers='keys', tablefmt='psql', showindex=False))
        print("Classification Stats")
        print(tabulate(classify_stats_df, headers='keys', tablefmt='psql', showindex=False))

        print("\nOverall")
        print("Pairing Stats")
        print(tabulate(pair_overall_row, headers='keys', tablefmt='psql', showindex=False))
        print("Classification Stats")
        print(tabulate(classify_overall_row, headers='keys', tablefmt='psql', showindex=False))



    def print_failed_executable(self):
        print("\n========================== FAILED EXECUTABLES ==========================")
        for file in self.collection_report['FAILED_EXECUTABLES']:
            print(f"\nFailed Executable - File ID: {file}")

            names = api.get_names_from_oid(file)
            df = pd.DataFrame(names, columns=["Potential File Names"])

            print(tabulate(df, headers='keys', tablefmt='psql', showindex=False))

    def print_modified_executables(self, file):
        print("\n================== MODIFIED EXECUTABLES ==================")
        if file:
            self.print_category_w_ref({file: self.collection_report['MODIFIED_EXECUTABLES'][file]})
        else:
            self.print_category_w_ref(self.collection_report['MODIFIED_EXECUTABLES'])
            self.save_csv_report(self.collection_report['MODIFIED_EXECUTABLES'])

    def print_unmatched_executables(self, file):
        print("\n================== UNMATCHED EXECUTABLES ==================")
        if file:
            self.print_category_w_ref({file: self.collection_report['UNMATCHED_EXECUTABLES'][file]})
        else:
            for file in self.collection_report['UNMATCHED_EXECUTABLES']:
                names = api.get_names_from_oid(file)
                df = pd.DataFrame(names, columns=["Potential File Names"])
            
                print(f"\nExecutable: {file}")
                print(tabulate(df, headers="keys", tablefmt="psql", showindex=False))

    def print_unmatched_non_executables(self):
        print("\n================== UNMATCHED NON-EXECUTABLES ==================")
        
        for file in self.collection_report['UNMATCHED_NON_EXECUTABLES']:
            names = api.get_names_from_oid(file)
            df = pd.DataFrame(names, columns=["Potential File Names"])
        
            print(f"\nNon-Executable: {file}")
            print(tabulate(df, headers="keys", tablefmt="psql", showindex=False))

    
    def print_category_w_ref(self, files_report):
        for file_id, report in files_report.items():
            ref_file_id = report['ref_oid']
            similarity = report['similarity']
            if ref_file_id:
                self.print_table_match(file_id, ref_file_id, similarity)

            # Print func_matches table
            if 'matched_funcs' in report and len(report['matched_funcs']) > 0:
                self.print_func_matches(report)
            
            # Print modified_funcs table
            if 'modified_funcs' in report and len(report['modified_funcs']) > 0:
                # self.print_modified_funcs_table(report)
                self.print_modified_funcs_features(report)
            
            # Print unmatched_funcs table
            if 'unmatched_funcs' in report and len(report['unmatched_funcs']) > 0:
                self.print_unmatched_funcs(report)
            print("\n")


    def save_csv_report(self, files_report, output_dir="csv_reports"):
        os.makedirs(output_dir, exist_ok=True)
        
        # Lists to store data for each report type
        file_match_rows = []
        matched_funcs_rows = []
        modified_funcs_rows = []
        unmatched_funcs_rows = []
        
        for file_id, report in files_report.items():
            # --- File match info ---
            ref_file_id = report.get('ref_oid')
            similarity = report.get('similarity')
            if ref_file_id:
                # Retrieve file names (assumes api.get_names_from_oid exists)
                file_names = list(api.get_names_from_oid(file_id))
                if len(file_names) > 1:
                    file_name_info = f"{len(file_names)} Associated File Names"
                else:
                    file_name_info = file_names[0] if file_names else "Unknown"
                
                ref_file_names = list(api.get_names_from_oid(ref_file_id))
                if len(ref_file_names) > 1:
                    ref_file_name_info = f"{len(ref_file_names)} Associated Ref File Names"
                else:
                    ref_file_name_info = ref_file_names[0] if ref_file_names else "Unknown"
                
                file_match_rows.append({
                    "File ID": file_id,
                    "Ref File ID": ref_file_id,
                    "File Names": file_name_info,
                    "Ref File Names": ref_file_name_info,
                    "Similarity Score": similarity
                })
            
            # --- Matched functions summary ---
            if 'matched_funcs' in report and len(report['matched_funcs']) > 0:
                matched_funcs_rows.append({
                    "File ID": file_id,
                    "Exact Matched Funcs Count": len(report['matched_funcs'])
                })
            
            # --- Modified functions details ---
            if 'modified_funcs' in report and len(report['modified_funcs']) > 0:
                for func, func_report in report['modified_funcs'].items():
                    modified_funcs_rows.append({
                        "File ID": file_id,
                        "Function": func_report.get('func_name'),
                        "Ref Function": func_report.get('ref_func_name'),
                        "Score": func_report.get('similarity')
                })
        
            # --- Unmatched functions details ---
            if 'unmatched_funcs' in report and len(report['unmatched_funcs']) > 0:
                for func, details in report['unmatched_funcs'].items():
                    unmatched_funcs_rows.append({
                        "File ID": file_id,
                        "Unmatched Function": details
                    })
    
        # --- Write each section to its own CSV file ---
        if file_match_rows:
            df = pd.DataFrame(file_match_rows)
            df.to_csv(os.path.join(output_dir, "file_matches.csv"), index=False)
            
        if matched_funcs_rows:
            df = pd.DataFrame(matched_funcs_rows)
            df.to_csv(os.path.join(output_dir, "matched_funcs_summary.csv"), index=False)
            
        if modified_funcs_rows:
            df = pd.DataFrame(modified_funcs_rows)
            df.to_csv(os.path.join(output_dir, "modified_funcs.csv"), index=False)
            
        if unmatched_funcs_rows:
            df = pd.DataFrame(unmatched_funcs_rows)
            df.to_csv(os.path.join(output_dir, "unmatched_funcs.csv"), index=False)

        print(f"Reports saved to directory: {output_dir}")

    def print_modified_funcs_features(self, report):
        columns = [
            "Function",
            "Ref Function",
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
                func_report['ref_func_name'],
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

    def print_func_matches(self, report):
        print(f"{len(report['matched_funcs'])} Exact Function Matches")

    def print_unmatched_funcs(self, report):
        num_unmatched = len(report['unmatched_funcs'])
        print(f"{num_unmatched} Unmatched Functions:")

        columns = ["Function"]
        rows = []
        for func, details in report['unmatched_funcs'].items():
            rows.append([details])

        # df = pd.DataFrame(rows, columns=columns)
        # print(tabulate(df, headers='keys', tablefmt='psql', showindex=False))

    def print_table_match(self, file_id, ref_file_id, similarity):
        # Retrieve file names for both file IDs
        file_names = list(api.get_names_from_oid(file_id))
        if len(file_names) > 1:
            file_name_info = f"{len(file_names)} Associated File Names"
        else:
            file_name_info = f"File Name: {file_names[0]}"
            
        ref_file_names = list(api.get_names_from_oid(ref_file_id))
        if len(ref_file_names) > 1:
            ref_file_name_info = f"{len(ref_file_names)} Associated Ref File Names"
        else:
            ref_file_name_info = f"Ref File Name: {ref_file_names[0]}"
        
        # Create table data with two columns: one for the file and one for the ref_file
        table_data = [
            [f"File: {file_id}", f"Ref File: {ref_file_id}"],
            [file_name_info, ref_file_name_info],
            [f"Similarity Score: {similarity}", ""]
        ]
        
        # Print the table using tabulate
        print(tabulate(table_data, tablefmt="grid"))

    def print_compare_functions(self, file_oid, function):
        for mod_func in self.collection_report['MODIFIED_EXECUTABLES'][file_oid]['modified_funcs']:
            if function == self.collection_report['MODIFIED_EXECUTABLES'][file_oid]['modified_funcs'][mod_func]['func_name']:
                func_comparator = self.collection_report['MODIFIED_EXECUTABLES'][file_oid]['modified_funcs'][mod_func]
                print(func_comparator)
                u_diff = api.retrieve("function_unified_diff", [file_oid, func_comparator['ref_file']], {"function": func_comparator['func_name'], "ref_function": func_comparator['ref_func_name']})

                for line in u_diff['unified_diff']:
                    print(line)     

def file_pre_analysis(args, opts) -> None:
    collections = get_collections(args, opts)

    force = opts.get('force')

    count = 1
    for collection_num, collection in enumerate(collections, start=1):
        print(f"COLLECTION {collection_num} of {len(collections)}: {api.get_colname_from_oid(collection)}")
        oids = api.expand_oids(collection)
        p = progress.Progress(len(oids))

        for oid in oids:
            analyzer = FileAnalyzer(oid, force)
            analyzer.tag_src_type()
            analyzer.tag_extension()
            analyzer.tag_file_category()

            # Apply the tags to the OID
            api.apply_tags(oid, analyzer.tags)
            p.tick()
        count += 1


def collection_pre_analysis(args, opts) -> None:
    collections = get_collections(args, opts)

    p = progress.Progress(len(collections))
    for collection in collections:
        collection_tags = {}
        oids = api.expand_oids(collection)

        # Initialize data structures for device attributes
        collection_src_types = {}
        device_file_exts = {}
        device_file_category = {}

        for oid in oids:
            tags = api.get_tags(oid)
            if not tags:
                continue

            # Handle SRC_TYPE
            src_type = tags.get("SRC_TYPE")
            collection_src_types[src_type] = collection_src_types.get(src_type, 0) + 1

            # Handle File Extensions
            ext = tags.get("EXT")
            device_file_exts[ext] = device_file_exts.get(ext, 0) + 1

            # Handle File Category
            cat = tags.get("FILE_CATEGORY")
            if cat in device_file_category:
                device_file_category[cat]["COUNT"] += 1
                device_file_category[cat]["SRC_TYPES"].get(src_type, 0) + 1
                device_file_category[cat]["FILE_EXTS"].get(ext, 0) + 1
            else:
                device_file_category[cat] = {
                    "COUNT": 1,
                    "SRC_TYPES": {src_type: 1},
                    "FILE_EXTS": {ext: 1}
                }

        # Aggregate device tags
        collection_tags = {
            "SRC_TYPE": collection_src_types,
            "EXT": device_file_exts,
            "CATEGORY": device_file_category,
        }

        api.apply_tags(collection, collection_tags)
        p.tick()         

def file_analysis(args, opts) -> None:
    collections = get_collections(args, opts)

    force = opts.get('force', None)
    for collection in collections:
        collection_tags = api.get_tags(collection)
        total_exe = collection_tags.get('CATEGORY', {}).get('executable', {}).get('COUNT', 0)
        oids = api.expand_oids(collection)
        exe_count = 1
        
        print(f"COLLECTION: {api.get_colname_from_oid(collection)}")
        for oid in oids:
            analyzer = FileAnalyzer(oid, force)
            analyzer.get_or_default_tags()
            if analyzer.tags.get("FILE_CATEGORY") == "executable":
                print(f"Executable {exe_count} of {total_exe}") 
                try:
                    # Create a separate thread to handle the function call
                    future = concurrent.futures.ThreadPoolExecutor(max_workers=1).submit(
                        tag_disasm, oid, force, analyzer.tags)
                    analyzer.tags = future.result(timeout=TIMEOUT_LONG)  # Apply timeout
                except concurrent.futures.TimeoutError:
                    future.cancel()
                    _clean_up_disasm()
                    analyzer.tags["DISASM"] = {
                        "RESULT": "TIMEOUT",
                        "PASS": {},
                        "FAIL": {}
                    }
                
                if analyzer.tags.get("DISASM") == "PASS":
                    analyzer.tag_function_tlsh()
                exe_count += 1

                # Apply the tags to the OID
                api.apply_tags(oid, analyzer.tags)

def collection_analysis(args, opts):
    collections = get_collections(args, opts)

    p = progress.Progress(len(collections))
    for collection in collections:
        collection_tags = {}
        oids = api.expand_oids(collection)

        # Initialize data structures for device attributes
        collection_disasm = {}
        collection_func_tlsh = {}

        for oid in oids:
            tags = api.get_tags(oid)
            if not tags:
                continue

            if tags.get("DISASM"):
                # Check Framework Result
                disasm_result = tags["DISASM"]
                collection_disasm[disasm_result] = collection_disasm.get(disasm_result, 0) + 1

                if tags.get("FUNC_TLSH"):
                    for function in tags['FUNC_TLSH']:
                        collection_func_tlsh[function] = tags["FUNC_TLSH"][function]

        # Aggregate device tags
        collection_tags = {
            "DISASM": collection_disasm,
            "FUNC_TLSH": collection_func_tlsh,
        }

        api.apply_tags(collection, collection_tags)
        p.tick()

def compare_all_collections(args, opts):
    collections = get_collections(args, opts)

    force = opts.get('force', None)

    ref_collections = api.collection_cids()

    for collection in collections:
        print(f"COLLECTION: {api.get_colname_from_oid(collection)}")
        p2 = progress.Progress(len(ref_collections))
        for ref_collection in ref_collections:  
            collection_tags = api.get_tags(collection)
            if not (collection_tags.get("FRAMEWORK_DATA") and collection_tags["FRAMEWORK_DATA"].get(ref_collection)) or force == "COMPARE":
                analyzer = CollectionComparator(collection, ref_collection)   
                analyzer.generate_report()
                if collection_tags.get("FRAMEWORK_DATA"):
                    collection_tags['FRAMEWORK_DATA'][ref_collection] = analyzer.collection_report
                else:
                    collection_tags['FRAMEWORK_DATA'] = {}
                    collection_tags['FRAMEWORK_DATA'][ref_collection] = analyzer.collection_report
                api.apply_tags(collection, collection_tags)
            p2.tick()

def compare_collections(args, opts):
    if len(args) < 2:
        print("ERROR: Enter two collections to compare")
        return
    
    force = opts.get('force', None)
    view = opts.get('view', None)

    file = None
    function = opts.get('function', None)

    valid, invalid = api.valid_oids(args)
    collection, ref_collection = valid[0], valid[1]

    if len(valid) == 3:
        file = valid[2]

    # Retrieve initial data for collections
    collection_tags = api.get_tags(collection)

    if not collection_tags.get("FRAMEWORK_DATA") or not collection_tags["FRAMEWORK_DATA"].get(ref_collection) or force == "COMPARE":
        start_time = time.time()
        if not collection_tags.get("FRAMEWORK_DATA"):
            collection_tags["FRAMEWORK_DATA"] = {}
        analyzer = CollectionComparator(collection, ref_collection)   
        analyzer.generate_report()
        collection_tags['FRAMEWORK_DATA'][ref_collection] = analyzer.collection_report
        api.apply_tags(collection, collection_tags)
        end_time = time.time()
        elapsed = end_time - start_time
        print(f"Execution time: {elapsed:.4f} seconds")
    else:
        analyzer = CollectionComparator(collection, ref_collection)
        analyzer.collection_report = collection_tags["FRAMEWORK_DATA"].get(ref_collection)

    # Calculate statistics
    stats = analyzer.calculate_statistics()
    if view == "stats":
        analyzer.print_statistics(stats)
    elif view == "unmatched":
        analyzer.print_statistics(stats)
        analyzer.print_unmatched_executables(file)
        # analyzer.print_unmatched_non_executables()
    elif view == "modified":
        analyzer.print_statistics(stats)
        analyzer.print_modified_executables(file)
    elif view == "failed":
        analyzer.print_statistics(stats)
        analyzer.print_failed_executable()
    elif view == "accuracy":
        analyzer.print_pairing_results()
    else:
        analyzer.print_statistics(stats)

    if file and function:
        analyzer.print_compare_functions(file, function)

def compare_collections_series(args, opts):
    # Assume get_collections returns a list of collection IDs
    collections = get_collections(args, opts)
    force = opts.get('force', None)
    parsed_collections = []
    for collection in collections:
        product, version = split_collection(api.get_colname_from_oid(collection))
        version_tuple = tuple(map(int, version.split('.')))
        parsed_collections.append((collection, product, version, version_tuple))
    # Sort by version tuple
    parsed_collections.sort(key=lambda x: x[3])
    ref_collection = None
    # Open CSV file once and write header later.
    # We'll write the header after we have at least one 'stats' object.
    csv_filename = f"/home/nathan/Documents/{product}_file_changes.csv"
    fieldnames = None  # Will determine after first stats retrieval
    csv_file = open(csv_filename, mode='w', newline='')
    csv_writer = None
    # Keep track of the reference version
    ref_version = None
    times = {}
    try:
        p = progress.Progress(len(collections))
        for collection, product, version, version_tuple in parsed_collections:
            start_time = time.time()
            colname = api.get_colname_from_oid(collection)
            collection_tags = api.get_tags(collection)
            if not collection_tags.get("FRAMEWORK_DATA") or not collection_tags["FRAMEWORK_DATA"].get(ref_collection) or force == "COMPARE":
                if not collection_tags.get("FRAMEWORK_DATA"):
                    collection_tags["FRAMEWORK_DATA"] = {}
                analyzer = CollectionComparator(collection, ref_collection)   
                analyzer.generate_report()
                collection_tags['FRAMEWORK_DATA'][ref_collection] = analyzer.collection_report
                api.apply_tags(collection, collection_tags)
            else:
                analyzer = CollectionComparator(collection, ref_collection)
                analyzer.collection_report = collection_tags["FRAMEWORK_DATA"].get(ref_collection)
            file_stats = {
                'EXECUTABLE_MATCHES': len(analyzer.collection_report["EXECUTABLE_MATCHES"]),
                'NON_EXECUTABLE_MATCHES': len(analyzer.collection_report['NON_EXECUTABLE_MATCHES']),
                'MODIFIED_EXECUTABLES': len(analyzer.collection_report['MODIFIED_EXECUTABLES']),
                'UNMATCHED_EXECUTABLES': len(analyzer.collection_report['UNMATCHED_EXECUTABLES']),
                'UNMATCHED_NON_EXECUTABLES': len(analyzer.collection_report['UNMATCHED_NON_EXECUTABLES']),
                'FAILED_EXECUTABLES': len(analyzer.collection_report['FAILED_EXECUTABLES'])
            }
            # Initialize CSV writer on first iteration, now including a 'ref_version' column
            if csv_writer is None:
                fieldnames = ['version', 'ref_version'] + list(file_stats.keys())
                csv_writer = csv.DictWriter(csv_file, fieldnames=fieldnames)
                csv_writer.writeheader()
            # Write the transformed stats to the CSV file
            row_data = {
                'version': version,
                'ref_version': ref_version if ref_version is not None else 'None'
            }
            row_data.update(file_stats)
            csv_writer.writerow(row_data)
            # Update reference info for the next iteration
            ref_version = version
            ref_collection = collection
            times[str(colname)] = time.time() - start_time
            p.tick()
    finally:
        csv_file.close()
    # Write the times dictionary to a CSV file
    # Adjust the filename and path as needed
    with open('/home/nathan/Documents/compare_times.csv', 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        # Write header
        writer.writerow(['collection', 'time_elapsed'])
        # Write data
        for colname, elapsed_time in times.items():
            writer.writerow([colname, elapsed_time])

def get_collection_tags(args, opts):
    def print_collection_info(device, name, tags):
        """Helper function to format and print device information."""
        print("\n----------------------------------------------")
        print(f"CID - {device}\nCOLLECTION - {name}\nTAGS -")
        print("SRC_TYPE")
        pp.pprint(tags.get("SRC_TYPE"))
        print("FILE_CATEGORIES")
        pp.pprint(tags.get("CATEGORY"))
        print("COLLECTION_SIZE")
        pp.pprint(tags.get("SIZE"))
        print("DISASM RESULTS:")
        pp.pprint(tags.get("DISASM"))
        print("----------------------------------------------")

    collections = get_collections(args, opts)
    
    # Fetch and print information for each device
    for collection in collections:
        name = api.get_colname_from_oid(collection)
        tags = api.get_tags(collection)
        print_collection_info(collection, name, tags)
    
def get_file_tags(args, opts):
    # Process OIDs based on whether specific collections are provided
    collections = get_collections(args, opts)

    for collection in collections:
        oids = api.expand_oids(collection)
        for oid in oids:
            _print_file_tags(oid)

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

def analyze_collections(args, opts):
    file_pre_analysis(args, opts)
    collection_pre_analysis(args, opts)
    file_analysis(args, opts)
    collection_analysis(args, opts)

exports = [
    file_pre_analysis, 
    file_analysis, 
    collection_pre_analysis, 
    collection_analysis, 
    compare_all_collections, 
    get_file_tags, 
    get_collection_tags, 
    compare_all_collections, 
    compare_collections, 
    import_product, 
    import_dataset, 
    analyze_collections,
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

def tag_disasm(oid, force, tags):
    if "DISASM" not in tags or force == "DISASM":
        disasm_result = api.retrieve('ghidra_disasm', oid)
        if disasm_result is None or disasm_result == {} or disasm_result["original_blocks"] == {}:
            tags['DISASM'] = 'FAIL'
        else:
            tags['DISASM'] = 'PASS'
    return tags    

def split_collection(input_string):
    # Split the string on the rightmost occurrence of '-'
    parts = input_string.rsplit('-', maxsplit=1)
    
    # Check if the delimiter was found and return both parts
    if len(parts) == 2:
        return parts[0], parts[1]
    else:
        return parts[0], None  # Return None if the delimiter is not found

def separate_uniq_repeated(oid_list: dict):
    # 1) Gather all functions from this list of OIDs
    func_to_oids = defaultdict(set)
    for oid in oid_list:
        funcs = api.get_tags(oid).get("FUNC_TLSH", [])
        for func in funcs:
            func_to_oids[func].add(oid)

    # 2) Build a results dict with "unique" / "repeated" per OID
    results = {}
    for oid in oid_list:
        results[oid] = {'funcs': {}, "rep_funcs": {}, "empty_funcs": {}}
        funcs = api.get_tags(oid).get("FUNC_TLSH", [])
        for func in funcs:
            if funcs[func]['tlsh hash'] != None:
                if len(func_to_oids[func]) == 1:
                    results[oid]['funcs'][func] = funcs[func]
                else:
                    results[oid]["rep_funcs"][func] = funcs[func]
            else:
                results[oid]['empty_funcs'][func] = funcs[func]
    return results

def file_matches(oids, ref_oids):
    if oids and ref_oids:
        matches = list(oids.intersection(ref_oids))
        return matches, oids.difference(ref_oids), ref_oids.difference(oids)
    else:
        return [], oids, ref_oids

def calculate_stats(part, total):
    if part is not int:
        return len(part), f"{round((len(part) / len(total)) * 100, 2)}%"

def _print_file_tags(oid):
    tags = api.get_tags(oid)
    if tags and len(tags) > 1:
        print(f"\nid - {oid}\n \ntags -")
        pp.pprint(tags)

def _clean_up_disasm():
    # Define the base directory
    base_dir = api.scratch_dir

    # # File and directory patterns to delete
    file_patterns = [
        "ghidraBenchmarking_MainProcess.gpr",
        "ghidraBenchmarking_MainProcess.lock",
        "ghidraBenchmarking_MainProcess.lock~",
        "ghidraBenchmarking_MainProcess.rep"
    ]

    # Loop through the patterns and delete the files/directories
    for file_pattern in file_patterns:
        file_path = os.path.join(base_dir, file_pattern)
        if os.path.isdir(file_path):
            shutil.rmtree(file_path)  # Use rmtree to delete directories recursively
            print(f"Deleted directory: {file_path}")
        elif os.path.isfile(file_path):
            os.remove(file_path)  # Use remove to delete files
            print(f"Deleted file: {file_path}")
        else:
            print(f"File or directory not found: {file_path}")
    return