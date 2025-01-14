
from oxide.core.oxide import api
import pprint
import csv
import os 
import concurrent.futures
import os
import shutil
import tlsh
from prettytable import PrettyTable
from threading import Event
import multiprocessing
import csv
import time

from oxide.core import progress, api


print("DRIFT")
info = """
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

    def tag_size(self):
        if "SIZE" not in self.tags or self.force == "SIZE":
            meta = api.retrieve("file_meta", self.oid)
            self.tags["SIZE"] = meta["size"]

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


    # Searches for files where all of the functions are found in the ref collection
    def sort_files(self, collection_oids, reference_collection_oids):
        results = {
            'NEW_EXECUTABLES': {},
            'MODIFIED_EXECUTABLES': {},
            'FAILED': []
        }

        ref_collection_funcs = self._get_all_functions(reference_collection_oids)

        repeated_collection_funcs = self._get_repeated_functions(collection_oids)

        for oid in collection_oids:
            oid_result, ref_files = self._process_oid(oid, ref_collection_funcs, repeated_collection_funcs, reference_collection_oids)

            # Failed File
            if oid_result == "FAILED":
                results['FAILED'].append(oid)
            # Modified File
            elif len(ref_files) == 1:
                results['MODIFIED_EXECUTABLES'][oid] = {
                    'REPORT': oid_result,
                    'REF_FILE_ID': next(iter(ref_files))
                }
            # New File
            else:
                results['NEW_EXECUTABLES'][oid] = oid_result

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
            'new_funcs': {}
        }
        potential_ref_files = []
        potential_ref_files_match = []
        potential_ref_files_modified = []

        if oid_funcs is None:
            return "FAILED", None

        oid_result, unmatched_funcs, potential_ref_files_match = self._get_function_matches(oid_funcs, ref_collection_funcs, repeated_funcs, reference_oids, oid_result)

        if len(potential_ref_files_match) == 1:
            oid_result = self._find_modified_functions(unmatched_funcs, potential_ref_files_match[0], oid_result, is_single_ref=True)
        else:
            oid_result = self._find_modified_functions(unmatched_funcs, reference_oids, oid_result, is_single_ref=False)

        
        potential_ref_files = list(set(potential_ref_files_match + potential_ref_files_modified))

        return oid_result, potential_ref_files

    def _get_function_matches(self, oid_funcs, ref_funcs, repeated_funcs, reference_oids, oid_result):
        potential_ref_files = []
        unmatched_funcs = {}
        for func in oid_funcs:
            if func in repeated_funcs:
                continue
            else:
                if func in ref_funcs:
                    for ref_oid in reference_oids:
                        ref_oid_funcs = api.get_tags(ref_oid).get("FUNC_TLSH", [])
                        if func in ref_oid_funcs:
                            oid_result['func_matches'][ref_oid] = oid_result['func_matches'].get(ref_oid, 0) + 1
                            if ref_oid not in potential_ref_files:
                                potential_ref_files.append(ref_oid)
                else:
                    unmatched_funcs[func] = oid_funcs[func]
        return oid_result, unmatched_funcs, potential_ref_files

    def _find_modified_functions(self, oid_funcs, ref_oids, oid_result, is_single_ref):
        potential_ref_files = []
        for func in oid_funcs:
            func_name = oid_funcs[func] 

            best_match = {
                'score': 390,
                'file': None,
                'func': None
            }

            ref_oids_to_check = [ref_oids] if is_single_ref else ref_oids
            for ref_oid in ref_oids_to_check:
                ref_oid_funcs = api.get_tags(ref_oid).get("FUNC_TLSH", [])
                for ref_func in ref_oid_funcs:
                    ref_func_name = ref_oid_funcs[ref_func]
                    similarity_score = tlsh.diff(func, ref_func)
                    if similarity_score < best_match['score']:
                        best_match.update({'score': similarity_score, 'file': ref_oid, 'func': ref_func_name})

            if best_match['score'] < 150:
                oid_result['modified_funcs'][func_name] = best_match
            else:
                oid_result['new_funcs'][func_name] = best_match
        return oid_result
    
    def export_modified_files_report(self, save_path):
        modified_files = self.report['MODIFIED_EXECUTABLES']
        
        # Define the columns we want in our CSVNNoneone0
        modified_file_fieldnames = ["File", "Ref File", "Function Matches", "Modified Functions", "New Functions"]
        
        # Open a CSV file for writing
        with open(f'{save_path}/modified_files_report.csv', 'w', newline='') as csvfile:
            writer = csv.DictWriter(csvfile, fieldnames=modified_file_fieldnames)
            writer.writeheader()  # Write the header row
            
            # Iterate through each file in the modified files report
            for file in modified_files:
                file_result = {
                    "File": file,
                    "Ref File": modified_files[file]['REF_FILE_ID'],
                    "Function Matches": modified_files[file]['REPORT']['func_matches'][modified_files[file]['REF_FILE_ID']],
                    "Modified Functions": len(modified_files[file]['REPORT']['modified_funcs']),
                    "New Functions": len(modified_files[file]['REPORT']['new_funcs'])
                }
                writer.writerow(file_result)

    def generate_file_report(self):
        """Generate report data for file matches."""
        matched_execs, uniq_col_execs, uniq_ref_execs = self.file_matches(self.collection_exec, self.ref_collection_exec)
        matched_non_execs, uniq_col_non_execs, _ = self.file_matches(self.collection_non_exec, self.ref_collection_non_exec)
        sorted_files = self.sort_files(uniq_col_execs, uniq_ref_execs)
        self.report = {
            'EXECUTABLE_MATCHES': matched_execs,
            'NON_EXECUTABLE_MATCHES': matched_non_execs,
            'MODIFIED_EXECUTABLES': sorted_files['MODIFIED_EXECUTABLES'],
            'NEW_EXECUTABLES': sorted_files['NEW_EXECUTABLES'],
            'NEW_NON_EXECUTABLES': uniq_col_non_execs,
            'FAILED_EXECUTABLES': sorted_files['FAILED']
        }


    def calculate_statistics(self):
        """Calculate statistics for each category in the report."""
        return {
            'MATCHED EXECUTABLES': self.calculate_stats(self.report["EXECUTABLE_MATCHES"], self.collection_oids),
            'MATCHED NON-EXECUTABLE': self.calculate_stats(self.report['NON_EXECUTABLE_MATCHES'], self.collection_oids),
            'MODIFIED EXECUTABLES': self.calculate_stats(self.report['MODIFIED_EXECUTABLES'], self.collection_oids),
            'NEW EXECUTABLES': self.calculate_stats(self.report['NEW_EXECUTABLES'], self.collection_oids),
            'NEW NON-EXECUTABLES': self.calculate_stats(self.report['NEW_NON_EXECUTABLES'], self.collection_oids),
            'FAILED EXECUTABLES': self.calculate_stats(self.report['FAILED_EXECUTABLES'], self.collection_oids)
        }


    def print_statistics(self, stats):
        table = PrettyTable()
        table.title = f"{api.get_colname_from_oid(self.collection)} Compared to {api.get_colname_from_oid(self.ref_collection)}"
        table.align = 'l'
        table.field_names = ["Category", f"# of {api.get_colname_from_oid(self.collection)} Files", f"% of {api.get_colname_from_oid(self.collection)} Files"]
        for key, (total, percentage) in stats.items():
            table.add_row([key, total, percentage])
        print(table)

    def print_failed_executable(self):
        print("\n========================== FAILED EXECUTABLES ==========================")
        for file in self.report['FAILED_EXECUTABLES']:
            # Create a new table for each file
            table = PrettyTable()
            table.title = f"Failed Executable - File ID: {file}"
            table.field_names = ["Potential File Names"]
            
            # Call the API and handle if it returns a set
            names = api.get_names_from_oid(file)
            for name in names:
                table.add_row([name])
            print(table)

    def print_modified_executables(self):
        print("\n================== MODIFIED EXECUTABLES ==================")
        self.print_category_w_ref(self.report['MODIFIED_EXECUTABLES'])

    def print_new_executables(self):
        print("\n================== NEW EXECUTABLES ==================")
        self.print_category(self.report['NEW_EXECUTABLES'])

    def print_new_non_executables(self):
        print("\n================== NEW NON-EXECUTABLES ==================")
        for file in self.report['NEW_NON_EXECUTABLES']:
            # Create a new table for each file
            table = PrettyTable()
            table.title = f"NEW NON-EXECUTABLES - File ID: {file}"
            table.field_names = ["Potential File Names"]
            
            # Call the API and handle if it returns a set
            names = api.get_names_from_oid(file)
            for name in names:
                table.add_row([name])
            print(table)

    def print_category(self, files_report):
        for file_id, report in files_report.items():
            self.print_table(file_id)

            # Print func_matches table
            if 'func_matches' in report and len(report['func_matches']) > 0:
                self.print_func_matches(report)
            
            # Print modified_funcs table
            if 'modified_funcs' in report and len(report['modified_funcs']) > 0:
                self.print_modified_funcs(report)
            
            # Print new_funcs table
            if 'new_funcs' in report and len(report['new_funcs']) > 0:
                self.print_new_funcs(report)
            print("\n")

    def print_category_w_ref(self, files_report):
        for file_id, data in files_report.items():
            ref_file_id = data['REF_FILE_ID']
            self.print_table_match(file_id, ref_file_id)
            
            report = data['REPORT']
            # Print func_matches table
            if 'func_matches' in report and len(report['func_matches']) > 0:
                self.print_func_matches(report)
            
            # Print modified_funcs table
            if 'modified_funcs' in report and len(report['modified_funcs']) > 0:
                self.print_modified_funcs(report)
            
            # Print new_funcs table
            if 'new_funcs' in report and len(report['new_funcs']) > 0:
                self.print_new_funcs(report)
            print("\n")

    def print_modified_funcs(self, report):
        table = PrettyTable()
        table.align = 'l'
        table.title = f"MODIFIED FUNCTIONS: {len(report['modified_funcs'])} Functions"
        table.field_names = ["Function", "Reference File", "Reference Function", "Score"]
        correct = 0
        incorrect = 0
        for func, details in report['modified_funcs'].items():
            table.add_row([func, details['file'], details['func'], details['score']])
            if func == details['func']:
                correct += 1
            else:
                incorrect += 1
        print(table)
        print(f"CORRECT: {correct}")
        print(f"INCORRECT: {incorrect}")


    def print_func_matches(self, report):
        table = PrettyTable()
        table.align = 'l'
        table.title = "EXACT FUNCTION MATCHES"
        table.field_names = ["Reference File", "# of Exact Function Matches"]
        for func, matches in report['func_matches'].items():
            table.add_row([func, matches])
        print(table)

    def print_new_funcs(self, report):
        table = PrettyTable()
        table.align = 'l'
        table.title = f"NEW FUNCTIONS: {len(report['new_funcs'])} Functions"
        table.field_names = ["Function", "Closest Match File", "Closest Match Function", "Score"]
        correct = 0
        incorrect = 0
        for func, details in report['new_funcs'].items():
            table.add_row([func, details['file'], details['func'], details['score']])
            if func == details['func']:
                correct += 1
            else:
                incorrect += 1
        print(table)
        print(f"CORRECT: {correct}")
        print(f"INCORRECT: {incorrect}")

    def print_table_match(self, file_id, ref_file_id):
        table = PrettyTable()
        table.align = 'l'
        table.title = f"File: {file_id} | Reference File: {ref_file_id}"
        table.field_names = ["Potential File Names", "Potential Reference File Names"]
        file_names = list(api.get_names_from_oid(file_id))
        ref_file_names = list(api.get_names_from_oid(ref_file_id))

        # Determine the maximum length to handle differing lengths of file_names and ref_file_names
        max_length = max(len(file_names), len(ref_file_names))

        # Pad the shorter list with empty strings to avoid index errors during iteration
        file_names += [""] * (max_length - len(file_names))
        ref_file_names += [""] * (max_length - len(ref_file_names))

        # Populate the table
        for file_name, ref_file_name in zip(file_names, ref_file_names):
            table.add_row([file_name, ref_file_name])

        print(table)

    def print_table(self, file_id):
        table = PrettyTable()
        table.align = 'l'
        table.title = f"File: {file_id}"
        table.field_names = ["Potential File Names"]
        file_names = list(api.get_names_from_oid(file_id))
        for name in file_names:
            table.add_row([name])
        print(table)

    def print_compare_functions(self, file_oid, function):
        if 'modified_funcs' in self.report['MODIFIED_EXECUTABLES'][file_oid]['REPORT']:
            for mod_func in self.report['MODIFIED_EXECUTABLES'][file_oid]['REPORT']['modified_funcs']:
                if function == mod_func:
                    print(self.report['MODIFIED_EXECUTABLES'][file_oid]['REPORT']['modified_funcs'][function])
                    ref_file_oid = self.report['MODIFIED_EXECUTABLES'][file_oid]['REPORT']['modified_funcs'][function]['file']
                    ref_function = self.report['MODIFIED_EXECUTABLES'][file_oid]['REPORT']['modified_funcs'][function]['func']

                    function_tlsh = api.retrieve('function_tlsh', file_oid, {'replace_addrs': True})
                    for func in function_tlsh:
                        if function_tlsh[func]['name'] == function:
                            print(f"FUNCTION STRING: \n{function_tlsh[func]['fun_string']}")

                    function_tlsh = api.retrieve('function_tlsh', file_oid, {'replace_addrs': False})
                    for func in function_tlsh:
                        if function_tlsh[func]['name'] == function:
                            print("FUNCTION INSTRUCTIONS:")
                            for i in function_tlsh[func]['fun_instructions']:
                                print(i)
                    
                    function_tlsh = api.retrieve('function_tlsh', ref_file_oid, {'replace_addrs': True})
                    for func in function_tlsh:
                        if function_tlsh[func]['name'] == ref_function:
                            print(f"REF FUNCTION STRING: \n{function_tlsh[func]['fun_string']}")

                    function_tlsh = api.retrieve('function_tlsh', ref_file_oid, {'replace_addrs': False})
                    for func in function_tlsh:
                        if function_tlsh[func]['name'] == ref_function:
                            print("REF FUNCTION INSTRUCTIONS")
                            for i in function_tlsh[func]['fun_instructions']:
                                print(i)


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
            analyzer.tag_size()

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
        total_exe = collection_tags['CATEGORY'].get('executable', 0).get('COUNT')
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


def framework_analysis(args, opts):
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
                    collection_tags['FRAMEWORK_DATA'][ref_collection] = analyzer.report
                else:
                    collection_tags['FRAMEWORK_DATA'] = {}
                    collection_tags['FRAMEWORK_DATA'][ref_collection] = analyzer.report
                api.apply_tags(collection, collection_tags)
            p2.tick()

def compare_collection_series(args, opts):
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
                analyzer.generate_file_report()
                collection_tags['FRAMEWORK_DATA'][ref_collection] = analyzer.report
                api.apply_tags(collection, collection_tags)
            else:
                analyzer = CollectionComparator(collection, ref_collection)
                analyzer.report = collection_tags["FRAMEWORK_DATA"].get(ref_collection)

            file_stats = {
                'EXECUTABLE_MATCHES': len(analyzer.report["EXECUTABLE_MATCHES"]),
                'NON_EXECUTABLE_MATCHES': len(analyzer.report['NON_EXECUTABLE_MATCHES']),
                'MODIFIED_EXECUTABLES': len(analyzer.report['MODIFIED_EXECUTABLES']),
                'NEW_EXECUTABLES': len(analyzer.report['NEW_EXECUTABLES']),
                'NEW_NON_EXECUTABLES': len(analyzer.report['NEW_NON_EXECUTABLES']),
                'FAILED_EXECUTABLES': len(analyzer.report['FAILED_EXECUTABLES'])
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

def compare_collections(args, opts):
    if len(args) < 2:
        print("ERROR: Enter two collections to compare")
        return
    
    force = opts.get('force', None)
    view = opts.get('view', None)
    report = opts.get('report', None)

    file = None
    function = opts.get('function', None)

    valid, invalid = api.valid_oids(args)
    collection, ref_collection = valid[0], valid[1]

    if len(valid) == 3:
        file = valid[2]

    # Retrieve initial data for collections
    collection_tags = api.get_tags(collection)

    if not collection_tags.get("FRAMEWORK_DATA") or not collection_tags["FRAMEWORK_DATA"].get(ref_collection) or force == "COMPARE":
        if not collection_tags.get("FRAMEWORK_DATA"):
            collection_tags["FRAMEWORK_DATA"] = {}
        analyzer = CollectionComparator(collection, ref_collection)   
        analyzer.generate_file_report()
        collection_tags['FRAMEWORK_DATA'][ref_collection] = analyzer.report
        api.apply_tags(collection, collection_tags)
    else:
        analyzer = CollectionComparator(collection, ref_collection)
        analyzer.report = collection_tags["FRAMEWORK_DATA"].get(ref_collection)

    # Calculate statistics
    stats = analyzer.calculate_statistics()
    if view == "stats":
        analyzer.print_statistics(stats)
    elif view == "new":
        analyzer.print_statistics(stats)
        analyzer.print_new_executables()
        analyzer.print_new_non_executables()
    elif view == "modified":
        analyzer.print_statistics(stats)
        analyzer.print_modified_executables()
    elif view == "failed":
        analyzer.print_statistics(stats)
        analyzer.print_failed_executable()
    else:
        analyzer.print_statistics(stats)

    if file and function:
        analyzer.print_compare_functions(file, function)

    if report:
        analyzer.export_modified_files_report(report)
    
def get_cross_collection_analysis(args, opts):
    def process_and_print(executable_matches):
        """Print the executable_matches dictionary as a table using PrettyTable, sorted alphabetically."""
        # Get sorted row headers (collections)
        row_headers = sorted(executable_matches.keys())

        # Get sorted column headers (reference collections)
        column_headers = sorted(set(
            ref_col for matches in executable_matches.values() for ref_col in matches.keys()
        ))

        # Initialize PrettyTable
        table = PrettyTable()
        table.field_names = ["Collection"] + column_headers

        # Populate the table with rows
        for collection in row_headers:
            row = [collection]  # Start with the collection name
            row.extend(executable_matches[collection].get(col, 0) for col in column_headers)  # Fill columns in sorted order
            table.add_row(row)

        # Set alignment to left for better readability
        table.align = "l"

        # Print the table
        print(table)

    # Determine mode and retrieve collections
    collections = [api.valid_oids(args)[0]] if args else api.collection_cids()

    ref_collections = collections

    # Gather data for each collection
    executable_matches = {}
    for collection in collections:
        col_name = api.get_colname_from_oid(collection)
        executable_matches[col_name] = {}

        for ref_collection in ref_collections:
            ref_col_name = api.get_colname_from_oid(ref_collection)
            tags = api.get_tags(collection)
            data = tags['FRAMEWORK_DATA'][ref_collection]
            executable_matches[col_name][ref_col_name] = len(data.get('EXECUTABLE_MATCHES', []))

    # Create and print each DataFrame with titles
    process_and_print(executable_matches)


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

def import_samples(args, opts):
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

# Run pre-analysis passes
def pre_analysis(args, opts):
    file_pre_analysis(args, opts)
    collection_pre_analysis(args, opts)

def run_all(args, opts):
    file_pre_analysis(args, opts)
    collection_pre_analysis(args, opts)
    file_analysis(args, opts)
    collection_analysis(args, opts)

def run_framework(args, opts):
    collections = get_collections(args)

    parsed_collections = []
    for collection in collections:
        product, version = split_collection(api.get_colname_from_oid(collection))
        version_tuple = tuple(map(int, version.split('.')))
        parsed_collections.append((collection, product, version, version_tuple))

    # Sort by version tuple
    parsed_collections.sort(key=lambda x: x[3])

    for collection, product, version, version_tuple in parsed_collections:
        start_time = time.time()
        colname = api.get_colname_from_oid(collection)
        print(colname)

        # Convert to a list since your subsequent functions expect a list
        collection = [collection]

        print("---FILE PRE-ANALYSIS---")
        file_pre_analysis(collection, opts)

        print("---COLLECTION PRE-ANALYSIS---")
        collection_pre_analysis(collection, opts)

        print("---FILE ANALYSIS---")
        file_analysis(collection, opts)

        print("---COLLECTION ANALYSIS---")
        collection_analysis(collection, opts)


exports = [
    file_pre_analysis, 
    file_analysis, 
    collection_pre_analysis, 
    collection_analysis, 
    framework_analysis, 
    get_file_tags, 
    get_collection_tags, 
    framework_analysis, 
    get_cross_collection_analysis, 
    compare_collections, 
    compare_collection_series,
    import_samples, 
    import_dataset, 
    pre_analysis, 
    run_framework,
    run_all]

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