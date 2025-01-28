
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
from difflib import  unified_diff, SequenceMatcher
import pandas as pd
import time

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
        hashes = {}
        filtered_hashes = {}
        if "FUNC_TLSH" not in self.tags or self.force == "FUNC_TLSH":
            self.tags.get("FUNC_HASH", None)
            hashes = api.retrieve("function_tlsh", self.oid, {"replace_addrs": True})
        
            for function in hashes:
                if hashes[function].get('tlsh hash'):
                    filtered_hashes[hashes[function].get('tlsh hash')] = hashes[function]['name']
            self.tags["FUNC_TLSH"] = filtered_hashes

class CollectionComparator:
    def __init__(self, collection, ref_collection) -> None:
        self.collection = collection
        self.collection_tags = api.get_tags(self.collection)
        self.collection_oids = set(api.expand_oids(self.collection))
        self.collection_exec, self.collection_non_exec = self.separate_oids(self.collection_oids)

        self.ref_collection = ref_collection
        if self.ref_collection:
            self.ref_collection_tags = api.get_tags(self.ref_collection)
            self.ref_collection_oids = set(api.expand_oids(self.ref_collection))
            self.ref_collection_exec, self.ref_collection_non_exec = self.separate_oids(self.ref_collection_oids)  
        else:       
            self.ref_collection_tags = []
            self.ref_collection_oids = []
            self.ref_collection_exec = []
            self.ref_collection_non_exec = []

        self.match_count = 0
        self.mismatch_count = 0

    def separate_oids(self, oids):
        executables, non_executables = set(), set()
        for oid in oids:
            tags = api.get_tags(oid) or {}
            if tags.get("FILE_CATEGORY") == "executable":
                executables.add(oid)
            else:
                non_executables.add(oid)
        return executables, non_executables

    def calculate_stats(self, part, total):
        if part is not int:
            return len(part), f"{round((len(part) / len(total)) * 100, 2)}%"

    def file_matches(self, collection_oids, ref_collection_oids):
        if collection_oids and ref_collection_oids:
            matches = list(collection_oids.intersection(ref_collection_oids))
            return matches, collection_oids.difference(ref_collection_oids), ref_collection_oids.difference(collection_oids)
        else:
            return [], collection_oids, ref_collection_oids


    def _get_repeated_functions(self, collection_oids):
        unique_functions = {}
        repeated_functions = {}
        
        for oid in collection_oids:
            funcs = api.get_tags(oid).get("FUNC_TLSH")
            if funcs:
                for func in funcs:
                    if func in unique_functions:
                        repeated_functions[func] = funcs[func]
                    else:
                        unique_functions[func] = funcs[func]
        
        return repeated_functions


    def sort_files(self, collection_oids, reference_col_oids):
        results = {
            'UNMATCHED_EXECUTABLES': {},
            'MODIFIED_EXECUTABLES': {},
            'FAILED': []
        }

        ref_col_funcs = self._get_all_functions(reference_col_oids)
        repeated_col_funcs = self._get_repeated_functions(collection_oids)

        for oid in collection_oids:
            oid_result, ref_files = self._process_oid(oid,ref_col_funcs, repeated_col_funcs, reference_col_oids)

            if oid_result == "FAILED":
                results['FAILED'].append(oid)
            elif len(ref_files) == 1:
                results['MODIFIED_EXECUTABLES'][oid] = {
                    'REPORT': oid_result,
                    'REF_FILE_ID': next(iter(ref_files))
                }
            # New File
            else:
                results['UNMATCHED_EXECUTABLES'][oid] = {
                    'REPORT': oid_result,
                    'REF_FILE_ID': None
                }

        return results

    def _get_all_functions(self, oids):
        functions = []
        for oid in oids:
            funcs = api.get_tags(oid).get("FUNC_TLSH")
            if funcs:
                functions += funcs
        return functions

    def _process_oid(self, oid, ref_collection_funcs, repeated_funcs, reference_oids):
        oid_funcs = api.get_tags(oid).get("FUNC_TLSH")

        oid_result = {
            'func_matches': {},
            'modified_funcs': {},
            'unmatched_funcs': {}
        }
        potential_ref_files = []
        potential_ref_files_match = {}
        potential_ref_files_modified = {}

        if oid_funcs is None:
            return "FAILED", None

        oid_result, unmatched_funcs, potential_ref_files_match = self._get_function_matches(oid_funcs, ref_collection_funcs, repeated_funcs, reference_oids, oid_result)

        if len(potential_ref_files_match) == 1:
            ref_file = next(iter(potential_ref_files_match))
            ref_funcs = api.get_tags(ref_file).get("FUNC_TLSH", {})
            num_expected_new_funcs = len(oid_funcs) - len(ref_funcs)
            if num_expected_new_funcs < 0:
                num_expected_new_funcs = 0

            oid_result = self._find_modified_functions(oid, unmatched_funcs, potential_ref_files_match, oid_result, num_expected_new_funcs)
        else:
            oid_result, potential_ref_files_modified = self._find_closest_functions(oid, unmatched_funcs, reference_oids, oid_result)

        
        potential_ref_files = {**potential_ref_files_match, **potential_ref_files_modified}

        return oid_result, potential_ref_files

    def _get_function_matches(self, oid_funcs, ref_funcs, repeated_funcs, reference_oids, oid_result):
        potential_ref_files = {}
        unmatched_funcs = {}
        for func in oid_funcs:
            if func in repeated_funcs:
                continue
            else:
                if func in ref_funcs:
                    for ref_oid in reference_oids:
                        ref_oid_funcs = api.get_tags(ref_oid).get("FUNC_TLSH", [])
                        if func in ref_oid_funcs:
                            if ref_oid not in oid_result['func_matches']:
                                oid_result['func_matches'][ref_oid] = {}
                            oid_result['func_matches'][ref_oid][func] = {
                                'func_name': oid_funcs[func],
                                'ref_func_name': ref_oid_funcs[func]
                            }
                            if ref_oid not in potential_ref_files:
                                potential_ref_files[ref_oid] = 1
                            else:
                                potential_ref_files[ref_oid] = 1
                else:
                    unmatched_funcs[func] = oid_funcs[func]
        return oid_result, unmatched_funcs, potential_ref_files

    def _calculate_top_matches(self, func, func_name, ref_oids_to_check):
        """
        Calculate the top 5 matches for a given function across reference OIDs.
        """
        matches = []
        for ref_oid in ref_oids_to_check:
            ref_funcs = api.get_tags(ref_oid).get("FUNC_TLSH", {})
            for ref_func, ref_func_name in ref_funcs.items():
                similarity_score = tlsh.diff(func, ref_func)
                matches.append({'score': similarity_score, 'file': ref_oid, 'func': ref_func_name})

        # Return the top 5 matches sorted by similarity score
        return sorted(matches, key=lambda x: x['score'])[:5]

    def _find_best_function_match(self, file, func, top_matches):
        """
        Match a function's instructions with its top reference matches using SequenceMatcher.
        """
        best_score = 0
        best_match = {}
        for match in top_matches:
            ref_file = match['file']
            ref_func = match['func']

            func_comparator = FunctionComparator(file, func, ref_file, ref_func)
            match_score = func_comparator.match_score

            if match_score > best_score:
                best_score = match_score
                func_comparator._diff_features()
                best_match = func_comparator.__dict__

        return best_match

    def _find_modified_functions(self, file_oid, oid_funcs, ref_oids, oid_result, num_expected_new_funcs):
        """
        Identify modified functions by comparing them with reference functions and 
        classify them based on their match scores.
        """
        func_matches = []

        for func, func_name in oid_funcs.items():
            # Calculate top matches for the function using TLSH
            top_matches = self._calculate_top_matches(func, func_name, ref_oids)

            # Find the best match for the function
            best_match = self._find_best_function_match(file_oid, func_name, top_matches)

            # Append the match data for sorting later
            func_matches.append((func_name, best_match))

        # Sort all functions by match score in descending order
        func_matches.sort(key=lambda x: x[1]['match_score'], reverse=True)

        # Classify functions into modified and unmatched based on the threshold
        modified_funcs = func_matches[:len(func_matches) - num_expected_new_funcs]
        unmatched_funcs = func_matches[len(func_matches) - num_expected_new_funcs:]

        # Populate the oid_result with modified and unmatched functions
        for func_name, best_match in modified_funcs:
            oid_result['modified_funcs'][func_name] = best_match

        for func_name, best_match in unmatched_funcs:
            oid_result['unmatched_funcs'][func_name] = best_match

        return oid_result
    
    def _find_closest_functions(self, file_oid, oid_funcs, ref_oids, oid_result):
        """
        Identify closest function match by comparing them with reference functions.
        """
        reference_files = {}
        for func, func_name in oid_funcs.items():
            # Calculate top matches for the function using TLSH
            top_matches = self._calculate_top_matches(func, func_name, ref_oids)

            # Find the best match using difflib
            best_match = self._find_best_function_match(file_oid, func_name, top_matches)

            if best_match['ref_file'] in reference_files:
                reference_files[best_match['ref_file']] += 1
            else:
                reference_files[best_match['ref_file']] = 1

            oid_result['unmatched_funcs'][func_name] = best_match

        return oid_result, reference_files

    def generate_file_report(self):
        """Generate report data for file matches."""
        matched_execs, uniq_col_execs, uniq_ref_execs = self.file_matches(self.collection_exec, self.ref_collection_exec)
        matched_non_execs, uniq_col_non_execs, _ = self.file_matches(self.collection_non_exec, self.ref_collection_non_exec)
        sorted_files = self.sort_files(uniq_col_execs, uniq_ref_execs)
        self.collection_report = {
            'EXECUTABLE_MATCHES': matched_execs,
            'NON_EXECUTABLE_MATCHES': matched_non_execs,
            'MODIFIED_EXECUTABLES': sorted_files['MODIFIED_EXECUTABLES'],
            'UNMATCHED_EXECUTABLES': sorted_files['UNMATCHED_EXECUTABLES'],
            'UNMATCHED_NON_EXECUTABLES': uniq_col_non_execs,
            'FAILED_EXECUTABLES': sorted_files['FAILED']
        }

    def calculate_statistics(self):
        """Calculate statistics for each category in the report."""
        return {
            'MATCHED EXECUTABLES': self.calculate_stats(self.collection_report["EXECUTABLE_MATCHES"], self.collection_oids),
            'MATCHED NON-EXECUTABLE': self.calculate_stats(self.collection_report['NON_EXECUTABLE_MATCHES'], self.collection_oids),
            'MODIFIED EXECUTABLES': self.calculate_stats(self.collection_report['MODIFIED_EXECUTABLES'], self.collection_oids),
            'UNMATCHED EXECUTABLES': self.calculate_stats(self.collection_report['UNMATCHED_EXECUTABLES'], self.collection_oids),
            'UNMATCHED NON-EXECUTABLES': self.calculate_stats(self.collection_report['UNMATCHED_NON_EXECUTABLES'], self.collection_oids),
            'FAILED EXECUTABLES': self.calculate_stats(self.collection_report['FAILED_EXECUTABLES'], self.collection_oids)
        }

    def print_matching_results(self):
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
        for file_id, data in self.collection_report['MODIFIED_EXECUTABLES'].items():
            file_stats = {
                'pair_correct': 0,
                'pair_incorrect': 0,
                'classify_TP': 0,
                'classify_FP': 0,
                'classify_FN': 0,
                'classify_TN': 0,
            }
            report = data['REPORT']
            ref_file_id = data['REF_FILE_ID']

            # Get sets of function names
            func_names = set(api.get_tags(file_id).get("FUNC_TLSH", {}).values())
            ref_func_names = set(api.get_tags(ref_file_id).get("FUNC_TLSH", {}).values())
            paired_funcs = func_names & ref_func_names
            new_funcs = func_names - ref_func_names

            # Process function matches
            for func_match in report['func_matches'].values():
                for match in func_match:
                    file_stats['classify_TP'] += 1
                    if func_match[match]['func_name'] == func_match[match]['ref_func_name']:
                        file_stats['pair_correct'] += 1
                    else:
                        file_stats['pair_incorrect'] += 1

            # Process modified functions
            for func, func_report in report['modified_funcs'].items():
                if func in paired_funcs:
                    file_stats['classify_TP'] += 1
                else:
                    file_stats['classify_FP'] += 1

                if func == func_report['ref_func']:
                    file_stats['pair_correct'] += 1
                else:
                    file_stats['pair_incorrect'] += 1

            # Process unmatched functions
            for func, func_report in report['unmatched_funcs'].items():
                if func in new_funcs:
                    file_stats['classify_TN'] += 1
                else:
                    file_stats['classify_FN'] += 1

                if func == func_report['ref_func']:
                    file_stats['pair_correct'] += 1
                else:
                    file_stats['pair_incorrect'] += 1

            # Update totals
            for key in total_stats:
                total_stats[key] += file_stats[key]

            # Calculate per-file metrics
            pair_total = file_stats['pair_correct'] + file_stats['pair_incorrect']
            TP = file_stats['classify_TP']
            FP = file_stats['classify_FP']
            FN = file_stats['classify_FN']
            TN = file_stats['classify_TN']
            classify_correct = TP + TN
            classify_incorrect = FP + FN
            classify_total = classify_correct + classify_incorrect

            precision = TP / (TP + FP) if (TP + FP) != 0 else 0.0
            recall = TP / (TP + FN) if (TP + FN) != 0 else 0.0
            accuracy = (TP + TN) / (TP + FP + TN + FN) if (TP + FP + TN + FN) != 0 else 0.0
            f1 = (2 * precision * recall) / (precision + recall) if (precision + recall) != 0 else 0.0

            # Collect row data for this file
            results.append({
                'file_id': file_id,
                '# Paired Correctly': file_stats['pair_correct'],
                '# of Function Pairs': pair_total,
                '% Paired Correctly': (file_stats['pair_correct'] / pair_total) * 100 if pair_total else 0.0,
                'Modified Functions': TP + FN,
                'New Functions': FP + TN,
                '# Classified Correctly': classify_correct,
                '% Classified Correctly': (classify_correct / classify_total) * 100 if classify_total else 0.0,
                'Precision': precision,
                'Recall': recall,
                'Accuracy': accuracy,
                'F1': f1
            })

        # Build a DataFrame for per-file results
        file_stats_df = pd.DataFrame(results)

        # Compute totals and overall metrics
        total_pair_total = total_stats['pair_correct'] + total_stats['pair_incorrect']
        total_TP = total_stats['classify_TP']
        total_FP = total_stats['classify_FP']
        total_FN = total_stats['classify_FN']
        total_TN = total_stats['classify_TN']

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
            '# of Function Pairs': total_pair_total,
            '% Paired Correctly': (total_stats['pair_correct'] / total_pair_total) * 100 if total_pair_total else 0.0,
            'Modified Functions': total_TP + total_FN,
            'New Functions': total_FP + total_TN,
            '# Classified Correctly': total_classify_correct,
            '% Classified Correctly': (total_classify_correct / total_classify_total) * 100 if total_classify_total else 0.0,
            'Precision': overall_precision,
            'Recall': overall_recall,
            'Accuracy': overall_accuracy,
            'F1': overall_f1
        }])

        # Separate pair stats and classify stats into different DataFrames
        pair_cols = ['file_id', '# Paired Correctly', '# of Function Pairs', '% Paired Correctly']
        classify_cols = ['file_id', 'Modified Functions', 'New Functions', '# Classified Correctly', '% Classified Correctly', 'Precision', 'Recall', 'Accuracy', 'F1']

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

    def print_unmatched_executables(self, file):
        print("\n================== UNMATCHED EXECUTABLES ==================")
        if file:
            self.print_category_w_ref({file: self.collection_report['UNMATCHED_EXECUTABLES'][file]})
        else:
            self.print_category_w_ref(self.collection_report['UNMATCHED_EXECUTABLES'])

    def print_unmatched_non_executables(self):
        print("\n================== UNMATCHED NON-EXECUTABLES ==================")
        
        for file in self.collection_report['UNMATCHED_NON_EXECUTABLES']:
            names = api.get_names_from_oid(file)
            df = pd.DataFrame(names, columns=["Potential File Names"])
        
            print(f"\nNon-Executable: {file}")
            print(tabulate(df, headers="keys", tablefmt="psql", showindex=False))

    def print_category_w_ref(self, files_report):
        for file_id, data in files_report.items():
            ref_file_id = data['REF_FILE_ID']
            if ref_file_id:
                self.print_table_match(file_id, ref_file_id)
            
            report = data['REPORT']
            # Print func_matches table
            if 'func_matches' in report and len(report['func_matches']) > 0:
                self.print_func_matches(report)
            
            # Print modified_funcs table
            if 'modified_funcs' in report and len(report['modified_funcs']) > 0:
                # self.print_modified_funcs_table(report)
                self.print_modified_funcs_features(report)
            
            # Print unmatched_funcs table
            if 'unmatched_funcs' in report and len(report['unmatched_funcs']) > 0:
                self.print_unmatched_funcs(report)
            print("\n")

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
            instr_modified     = func_report['modified_isntr']     or 0
            func_calls         = func_report['func_calls']         or 0



            rows.append([
                func,
                func_report['ref_func'],
                func_report['match_score'],
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
        ref_file, func_matches = next(iter(report['func_matches'].items()))
        for match in func_matches:
            if func_matches[match]['func_name'] == func_matches[match]['ref_func_name']:
                self.match_count += 1
            else:
                self.mismatch_count += 1
        print(f"{len(func_matches)} Exact Function Matches")

    def print_unmatched_funcs(self, report):
        num_unmatched = len(report['unmatched_funcs'])
        print(f"{num_unmatched} Unmatched Functions:")

        columns = ["Function", "Closest Match File", "Closest Match Function", "Score"]
        rows = []
        for func, details in report['unmatched_funcs'].items():
            rows.append([func, details['ref_file'], details['ref_func'], details['match_score']])

        df = pd.DataFrame(rows, columns=columns)
        df.sort_values(by="Score", ascending=False, inplace=True)
        print(tabulate(df, headers='keys', tablefmt='psql', showindex=False))

    def print_table_match(self, file_id, ref_file_id):
        file_names = list(api.get_names_from_oid(file_id))
        ref_file_names = list(api.get_names_from_oid(ref_file_id))

        # Join all file names with a comma + space
        file_names_str = ", ".join(file_names) if file_names else ""
        ref_file_names_str = ", ".join(ref_file_names) if ref_file_names else ""

        # Print in the requested format
        print(f"File: {file_id}")
        print(f"File Names: {file_names_str}")
        print(f"Ref File: {ref_file_id}")
        print(f"Ref File Names: {ref_file_names_str}")

    def print_compare_functions(self, file_oid, function):
        for mod_func in self.collection_report['MODIFIED_EXECUTABLES'][file_oid]['REPORT']['modified_funcs']:
            if function == mod_func:

                func_comparator = self.collection_report['MODIFIED_EXECUTABLES'][file_oid]['REPORT']['modified_funcs'][mod_func]

                u_diff = unified_diff(func_comparator['func_insts'], func_comparator['ref_func_insts'], n=0)

                for line in u_diff:
                    print(line)     

class FunctionComparator:
    def __init__(self, file, func, ref_file, ref_func):
        self.file = file
        self.func = func
        self.func_insts = self._retrieve_function_instructions(self.file, self.func)
        self.num_func_bb = None
        self.num_func_calls = None

        self.ref_file = ref_file
        self.ref_func = ref_func
        self.ref_func_insts = self._retrieve_function_instructions(self.ref_file, self.ref_func)
        self.num_ref_func_bb = None
        self.num_ref_func_calls = None

        self.seq_matcher = SequenceMatcher(None, self.func_insts, self.ref_func_insts)

        self.match_score = round(self.seq_matcher.ratio(), 4)

        # Variables to track features
        self.basic_blocks = None
        self.added_instr = None
        self.removed_instr = None
        self.modified_isntr = None
        self.func_calls = None
        self.op_code_changes = None
    
    def _retrieve_function_instructions(self, file, func):
        """
        Retrieve function instructions for a specific function by its name.
        """
        function_data = api.retrieve('function_tlsh', file, {'replace_addrs': True})
        for func_id, details in function_data.items():
            if details.get('name') == func:
                return details.get('modified_fun_instructions', None)
        return None
    
    def _diff_features(self):
        # Control Flow
        self.num_func_bb, self.num_func_calls = self._get_bb(self.file, self.func)
        self.num_ref_func_bb, self.num_ref_func_calls = self._get_bb(self.ref_file, self.ref_func)

        if self.num_func_bb - self.num_ref_func_bb != 0:
            self.basic_blocks = self.num_func_bb - self.num_ref_func_bb

        if self.num_func_calls - self.num_ref_func_calls != 0:
            self.func_calls = self.num_func_calls - self.num_ref_func_calls

        self.added_instr, self.removed_instr, self.modified_isntr, = self._instruction_changes()

    def _get_bb(self, file, func):
        file_disasm = api.retrieve('ghidra_disasm', file)
        for func_addr in file_disasm['functions']:
            if file_disasm['functions'][func_addr]['name'] == func:
                call_mappings = api.get_field("call_mapping", file, func_addr)
                function_calls = len(call_mappings['calls_to'])
                num_bb = len(file_disasm['functions'][func_addr]['blocks'])
                return function_calls, num_bb
        return None
    
    def _instruction_changes(self):
        u_diff = unified_diff(self.func_insts, self.ref_func_insts, n=0)

        # Initialize counters
        lines_added = 0
        lines_removed = 0
        total_lines_added = 0
        total_lines_removed = 0
        total_lines_modified = 0

        # Process the diff
        for line in u_diff:
            if line.startswith("---") or line.startswith("+++"):
                # Skip file headers
                continue
            
            if line.startswith("-"):
                lines_removed += 1
            elif line.startswith("+"):
                lines_added += 1
            elif line.startswith("@@"):
                if lines_added == lines_removed:
                    total_lines_modified += lines_added
                else:
                    total_lines_added += lines_added
                    total_lines_removed += lines_removed
                lines_added = 0
                lines_removed = 0
                continue
            else:
                continue

            if lines_added == lines_removed:
                total_lines_modified += lines_added

        return total_lines_added, total_lines_removed, total_lines_modified

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
                analyzer.generate_file_report()
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
        analyzer.generate_file_report()
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
        analyzer.print_matching_results()
    else:
        analyzer.print_statistics(stats)

    if file and function:
        analyzer.print_compare_functions(file, function)

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
        sample_name = f"{parent_directory_name}---{sample}"
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
    analyze_collections]

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
    # Split the string at the occurrence of "---"
    parts = input_string.split('---', maxsplit=1)
    
    # Check if the delimiter was found and return both parts
    if len(parts) == 2:
        return parts[0], parts[1]
    else:
        return parts[0], None  # Return None if the delimiter is not found

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