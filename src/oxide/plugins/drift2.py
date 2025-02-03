
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
from collections import defaultdict
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

    def _classify_files(self):
        self.modified_exes = {}
        self.unmatched_exes = {}
        self.failed_exes = []

        for oid in self.uniq_col_exes:
            result, num_matched_funcs = self._match_oid(oid)

            if result:
                if result == "FAILED":
                    self.failed_exes.append(oid)
                else:
                    self.modified_exes[oid] = {
                        'ref_oid': result, 
                        'func_matches': num_matched_funcs,
                        'modified_funcs': {},
                        'unmatched_funcs': {}
                        }
                    self.unmatched_ref_exes.remove(result)

            else:
                self.unmatched_exes[oid] = {
                    'ref_oid': None, 
                    'func_matches': 0,
                    'modified_funcs': {},
                    'unmatched_funcs': {}
                    }
        
    def _handle_unmatched_exes(self):
        if len(self.unmatched_ref_exes) > len(self.unmatched_exes):
            oids = list(self.unmatched_exes.keys())
            most_matches = {}

            for oid in oids:
                count = {}
                matches = self._find_closest_functions(oid)
                for match in matches:
                    ref_file = matches[match]['ref_file']
                    count[ref_file] = count.get(ref_file, 0) + 1  # Increment count

                if count:
                    best = max(count, key=count.get)  # Get ref_file with highest count
                    most_matches[oid] = {
                        'file': best,
                        'count': count[best]
                    }

            # Find the best matching ref_oid
            best_match = {}

            for ref_oid in self.unmatched_ref_exes:
                candidates = [(oid, data['count']) for oid, data in most_matches.items() if data['file'] == ref_oid]
                if candidates:
                    # Pick the one with the highest count
                    best_match[ref_oid] = max(candidates, key=lambda x: x[1])[0]

            for match in best_match:
                self.modified_exes[best_match[match]] = {
                    'ref_oid': match, 
                    'func_matches': 0,
                    'modified_funcs': {},
                    'unmatched_funcs': {}
                    }

    def _match_functions(self):
        oids = list(self.modified_exes.keys())
        p = progress.Progress(len(oids))
        for oid in oids:
            self._pair_modified_functions(oid)
            p.tick()

    def _get_all_functions(self, oids):
        functions = []
        for oid in oids:
            funcs = api.get_tags(oid).get("FUNC_TLSH")
            if funcs:
                functions += funcs
        return functions

    def _match_oid(self, oid):
        uniq_funcs = self.collection_funcs[oid]['funcs']
        rep_funcs = self.collection_funcs[oid]['rep_funcs']

        if uniq_funcs is None and rep_funcs is None:
            return "FAILED"

        results = self._get_function_matches(uniq_funcs)

        if len(results) == 1:
            ref_oid = next(iter(results))
            for match in results[ref_oid]:
                self.collection_funcs[oid]['funcs'].pop(match)
                self.ref_collection_funcs[ref_oid]['funcs'].pop(match)
            return ref_oid, results[ref_oid]
        else:
            print(results)
            input()
            return None, None

    def _get_function_matches(self, oid_funcs):
        results = {}
        for func in oid_funcs:
            for ref_oid in self.unmatched_ref_exes:
                ref_oid_funcs = self.ref_collection_funcs[ref_oid]['funcs']
                if func in ref_oid_funcs:
                    if ref_oid not in results:
                        results[ref_oid] = {func: oid_funcs[func]}
                    else:
                        results[ref_oid][func] = oid_funcs[func]
        return results

    def _find_top_matches_from_oids(self, func, ref_oids):
        """
        Calculate the top 5 matches for a given function across reference OIDs.
        Supports ref_oids as a single ref_oid or a list of ref_oids.
        """
        matches = []

        # Ensure ref_oids is a list for uniform processing
        if not isinstance(ref_oids, list):
            ref_oids = [ref_oids]

        # Iterate over each ref_oid
        for ref_oid in ref_oids:
            ref_funcs = api.get_tags(ref_oid).get("FUNC_TLSH", {})
            for ref_func, ref_func_name in ref_funcs.items():
                similarity_score = tlsh.diff(func, ref_func)
                matches.append({'score': similarity_score, 'file': ref_oid, 'func': ref_func, 'func_name': ref_func_name})

        # Return the top 5 matches sorted by similarity score
        return sorted(matches, key=lambda x: x['score'])[:5]

    def _find_top_matches_from_funcs(self, func, ref_oid, ref_funcs):
        """
        Calculate the top 5 matches for a given function across reference OIDs.
        Supports ref_oids as a single ref_oid or a list of ref_oids.
        """
        matches = []
        for ref_func, ref_func_name in ref_funcs.items():
            similarity_score = tlsh.diff(func, ref_func)
            matches.append({'score': similarity_score, 'file': ref_oid, 'func': ref_func, 'func_name': ref_func_name})

        # Return the top 5 matches sorted by similarity score
        return sorted(matches, key=lambda x: x['score'])[:5]

    def _find_best_function_match(self, file, func, func_name, top_matches):
        """
        Match a function's instructions with its top reference matches using SequenceMatcher.
        """
        best_match = {
            'ratio_score': 0,
            'file': None,
            'func_name': None,
            'ref_file': None,
            'ref_func_name': None
        }
        for match in top_matches:
            ref_file = match['file']
            ref_func = match['func']
            ref_func_name = match['func_name']

            func_comparator = api.retrieve("function_ratio_score", [file, ref_file], {"function": func_name, "ref_function": ref_func_name})
            ratio_score = func_comparator['ratio_score']

            if ratio_score > best_match['ratio_score']:
                best_match['ratio_score'] = ratio_score
                best_match['file'] = file
                best_match['func'] = func
                best_match['func_name'] = func_name
                best_match['ref_file'] = ref_file
                best_match['ref_func'] = ref_func
                best_match['ref_func_name'] = ref_func_name
                # func_comparator._diff_features()
                # best_match = func_comparator.__dict__

        diff_features = api.retrieve("function_diff_features", [file, ref_file], {"function": func_name, "ref_function": ref_func_name}) 
        for feature in diff_features:
            best_match[feature] = diff_features[feature]

        return best_match

    def _pair_modified_functions(self, oid):
        """
        Identify modified functions by comparing them with reference functions and 
        classify them based on their match scores.
        """
        paired_funcs = []
        unpaired_funcs = []

        ref_oid = self.modified_exes[oid]['ref_oid']

        # Retrieve and merge function dictionaries
        funcs = {**self.collection_funcs[oid]['funcs'], **self.collection_funcs[oid]['rep_funcs']}
        ref_funcs = {**self.ref_collection_funcs[ref_oid]['funcs'], **self.ref_collection_funcs[ref_oid]['rep_funcs']}

        # Handle Added Function Scenario
        if len(funcs) > len(ref_funcs):
            for ref_func, ref_func_name in ref_funcs.items():
                # Calculate top matches for the function using TLSH
                top_matches = self._find_top_matches_from_funcs(ref_func, oid, funcs)

                # Find the best match for the function
                ref_best_match = self._find_best_function_match(ref_oid, ref_func, ref_func_name, top_matches)

                best_match = self._find_best_function_match(ref_best_match['ref_file'], ref_best_match['ref_func'], ref_best_match['ref_func_name'], [{'file': ref_oid, 'func': ref_func, 'func_name': ref_func_name}])

                # Append the match data for sorting later
                paired_funcs.append((ref_best_match['ref_func_name'], best_match))
                del funcs[best_match['func']]   

            for func in funcs:
                unpaired_funcs.append((func, funcs[func]))
            

        else:
            for func, func_name in funcs.items():
                # Calculate top matches for the function using TLSH
                top_matches = self._find_top_matches_from_funcs(func, ref_oid, ref_funcs)

                # Find the best match for the function
                best_match = self._find_best_function_match(oid, func, func_name, top_matches)

                # Append the match data for sorting later
                paired_funcs.append((func_name, best_match))

        # Sort all functions by match score in descending order
        paired_funcs.sort(key=lambda x: x[1]['ratio_score'], reverse=True)

        # Populate the oid_result with modified and unmatched functions
        for func_name, best_match in paired_funcs:
            self.modified_exes[oid]['modified_funcs'][func_name] = best_match
        for func, func_name in unpaired_funcs:
            self.modified_exes[oid]['unmatched_funcs'][func] = func_name
    
    def _find_closest_functions(self, oid):
        """
        Identify modified functions by comparing them with reference functions and 
        classify them based on their match scores.
        """
        func_matches = []

        funcs = api.get_tags(oid).get("FUNC_TLSH", {})

        for func, func_name in funcs.items():
            # Calculate top matches for the function using TLSH
            top_matches = self._find_top_matches_from_oids(func, self.unmatched_ref_exes)

            # Find the best match for the function
            best_match = self._find_best_function_match(oid, func_name, top_matches)

            # Append the match data for sorting later
            func_matches.append((func_name, best_match))

        # Sort all functions by match score in descending order
        func_matches.sort(key=lambda x: x[1]['ratio_score'], reverse=True)

        return func_matches

    def generate_report(self):
        """Generate report data for file matches."""
        self.matched_exes, self.uniq_col_exes, self.unmatched_ref_exes = file_matches(self.collection_exes, self.ref_collection_exes)
        self.matched_non_exes, self.uniq_col_non_exes, self.uniq_ref_non_exes = file_matches(self.collection_non_exes, self.ref_collection_non_exec)
        self._seperate_funcs()
        self._classify_files()
        self._handle_unmatched_exes()
        self._match_functions()
        self.collection_report = {
            'EXECUTABLE_MATCHES': self.matched_exes,
            'NON_EXECUTABLE_MATCHES': self.matched_non_exes,
            'MODIFIED_EXECUTABLES': self.modified_exes,
            'UNMATCHED_EXECUTABLES': self.unmatched_exes,
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
            'modified_funcs': 0,
            'unmatched_funcs': 0
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
                'modified_funcs': len(report['modified_funcs']),
                'unmatched_funcs': len(report['unmatched_funcs'])
            }

            ref_file_id = report['ref_oid']

            # Get sets of function names
            func_names = set(api.get_tags(file_id).get("FUNC_TLSH", {}).values())
            ref_func_names = set(api.get_tags(ref_file_id).get("FUNC_TLSH", {}).values())
            print(len(func_names))
            print(len(ref_func_names))
            # Process modified functions
            for func, func_report in report['modified_funcs'].items():
                if func in ref_func_names:
                    file_stats['classify_TP'] += 1
                else:
                    print("fp ", func)
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
            num_modified = TP + FN
            num_unmatched = FP + TN
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
                '# of Function Pairs': num_modified,
                '% Paired Correctly': (file_stats['pair_correct'] / num_modified) * 100 if num_modified else 0.0,
                'Modified Functions': num_modified,
                'New Functions': num_unmatched,
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
        total_modified = total_TP + total_FN
        total_unmatched = total_FP + total_TN

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
            '# of Function Pairs': total_modified,
            '% Paired Correctly': (total_stats['pair_correct'] / total_modified) * 100 if total_modified else 0.0,
            'Modified Functions': total_modified,
            'New Functions': total_unmatched,
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
        for file_id, report in files_report.items():
            ref_file_id = report['ref_oid']
            if ref_file_id:
                self.print_table_match(file_id, ref_file_id)
            
            
            report = data['REPORT']

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
            instr_modified     = func_report['modified_instr']     or 0
            func_calls         = func_report['func_calls']         or 0



            rows.append([
                func,
                func_report['ref_func_name'],
                func_report['ratio_score'],
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
        print(f"{len(report['func_matches'])} Exact Function Matches")

    def print_unmatched_funcs(self, report):
        num_unmatched = len(report['unmatched_funcs'])
        print(f"{num_unmatched} Unmatched Functions:")

        columns = ["Function"]
        rows = []
        for func, details in report['unmatched_funcs'].items():
            rows.append([details])

        df = pd.DataFrame(rows, columns=columns)
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
    def __init__(self, file, func, func_name, ref_file, ref_func, ref_func_name):
        self.file = file
        self.func = func
        self.func_name = func_name
        self.func_insts = self._retrieve_function_instructions(self.file, self.func_name)
        self.num_func_bb = None
        self.num_func_calls = None

        self.ref_file = ref_file
        self.ref_func = ref_func
        self.ref_func_name = ref_func_name
        self.ref_func_insts = self._retrieve_function_instructions(self.ref_file, self.ref_func_name)
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
        self.num_func_bb, self.num_func_calls = self._get_bb(self.file, self.func_name)
        self.num_ref_func_bb, self.num_ref_func_calls = self._get_bb(self.ref_file, self.ref_func_name)

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
        results[oid] = {'funcs': {}, "rep_funcs": {}}
        funcs = api.get_tags(oid).get("FUNC_TLSH", [])
        for func in funcs:
            if len(func_to_oids[func]) == 1:
                results[oid]['funcs'][func] = funcs[func]
            else:
                results[oid]["rep_funcs"][func] = funcs[func]
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