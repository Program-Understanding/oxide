
from oxide.core.oxide import api
import concurrent.futures
import tabulate
import prettytable
from pprint import pprint
import tlsh
import os

import logging
from oxide.core import progress, api

TIMEOUT_SHORT = 1000
TIMEOUT_LONG = 500

class FileAnalyzer:
    def __init__(self, oid, force):
        self.oid = oid
        self.force = force
        self.tags = {}
        self.collection_archs = {}

    def get_or_default_tags(self):
        """Retrieve existing tags or return an empty dictionary."""
        self.tags = api.get_tags(self.oid) or {}
    
    def tag_file_info(self):
        file_info = api.get_field("file_info", self.oid, self.oid)
        self.tags["CATEGORY"] = file_info["CATEGORY"]
        self.tags["SIZE"] = file_info["SIZE"]
        self.tags["SRC_TYPE"] = file_info["SRC_TYPE"]
        self.tags["NAMES"] = file_info["NAMES"]
        self.tags["EXT"] = file_info["EXT"]
    
    def get_archs(self):
        if "ARCHS" not in self.tags or self.force == "ARCHS":
            self.tags["ARCHS"] = api.get_field("possible_archs", self.oid, self.oid)

    def update_archs(self, collection_archs):
        for arch in collection_archs:
            if arch in self.tags["ARCHS"]:
                self.tags["ARCHS"][arch].add("COLLECTION")
            else:
                self.tags["ARCHS"][arch] = set(["COLLECTION"])

    def tag_function_tlsh(self):
        pass

class FrameworkAnalyzer:
    def __init__(self, collection, reference_collection) -> None:
        self.collection = collection
        self.collection_tags = api.get_tags(self.collection)
        self.collection_oids = set(api.expand_oids(self.collection))
        self.collection_exec, self.collection_non_exec = self._separate_oids(self.collection_oids)

        self.reference_collection = reference_collection
        self.reference_collection_tags = api.get_tags(self.reference_collection)
        self.reference_collection_oids = set(api.expand_oids(self.reference_collection))
        self.reference_exec, self.reference_non_exec = self._separate_oids(self.reference_collection_oids)

    def _separate_oids(self, oids):
        executables, non_executables = set(), set()
        for oid in oids:
            tags = api.get_tags(oid) or {}
            if tags.get("FILE_CATEGORY") == "executable":
                executables.add(oid)
            else:
                non_executables.add(oid)
        return executables, non_executables

    def _calculate_percentage(self, part, total):
        if isinstance(part, (set, list)) and isinstance(total, (set, list)):
            return len(part), f"{round((len(part) / len(total)) * 100, 2)}%"
        return 0, "0%"

    def get_file_matches(self, collection_oids, reference_oids):
        matches = list(collection_oids.intersection(reference_oids))
        unique_in_collection = collection_oids.difference(reference_oids)
        unique_in_reference = reference_oids.difference(collection_oids)
        return matches, unique_in_collection, unique_in_reference

    def _get_repeated_functions(self, functions):
        unique_functions = set()
        repeated_functions = set()
        for function in functions:
            if function in unique_functions:
                repeated_functions.add(function)
            else:
                unique_functions.add(function)
        return repeated_functions

    def sort_files(self, collection_oids, reference_oids):
        results = {
            'NEW_EXECUTABLES': {},
            'MODIFIED_EXECUTABLES': {},
            'FAILED': []
        }

        ref_funcs = self._get_all_functions(reference_oids)
        all_functions = self._get_all_functions(collection_oids)
        repeated_funcs = self._get_repeated_functions(all_functions)

        for oid in collection_oids:
            oid_result, ref_files = self._process_oid(oid, ref_funcs, repeated_funcs, reference_oids)
            if oid_result == "FAILED":
                results['FAILED'].append(oid)
            elif len(ref_files) == 1:
                results['MODIFIED_EXECUTABLES'][oid] = {
                    'REPORT': oid_result,
                    'REF_FILE_ID': next(iter(ref_files))
                }
            else:
                results['NEW_EXECUTABLES'][oid] = oid_result

        return results

    def _get_all_functions(self, oids):
        functions = []
        for oid in oids:
            funcs = api.get_tags(oid).get("FUNC_TLSH")
            if funcs:
                functions.extend(funcs)
        return functions

    def _process_oid(self, oid, ref_collection_funcs, repeated_funcs, reference_oids):
            oid_funcs = api.get_tags(oid).get("FUNC_TLSH")
            if not oid_funcs:
                return "FAILED"

            oid_result = {
                'func_matches': {},
                'modified_funcs': {},
                'new_funcs': {}
            }
            potential_ref_files = []
            potential_ref_files_match = []
            potential_ref_files_modified = []

            potential_ref_files_match = self._get_function_matches(oid_funcs, ref_collection_funcs, repeated_funcs, reference_oids, oid_result)

            if len(potential_ref_files_match) == 1:
                oid_result, potential_ref_files_modified = self._find_modified_functions(oid_funcs, repeated_funcs, potential_ref_files_match[0], oid_result, is_single_ref=True)
            else:
                oid_result, potential_ref_files_modified = self._find_modified_functions(oid_funcs, repeated_funcs, reference_oids, oid_result, is_single_ref=False)

            potential_ref_files = potential_ref_files_match + potential_ref_files_modified

            return oid_result, potential_ref_files

    def _get_function_matches(self, oid_funcs, ref_funcs, repeated_funcs, reference_oids, oid_result):
        potential_ref_files = []
        for func in oid_funcs:
            if func not in repeated_funcs and func in ref_funcs:
                for ref_oid in reference_oids:
                    ref_oid_funcs = api.get_tags(ref_oid).get("FUNC_TLSH", [])
                    if func in ref_oid_funcs:
                        oid_result['func_matches'][ref_oid] = oid_result['func_matches'].get(ref_oid, 0) + 1
                        if ref_oid not in potential_ref_files:
                            potential_ref_files.append(ref_oid)
        return potential_ref_files

    def _find_modified_functions(self, oid_funcs, repeated_funcs, ref_oids, oid_result, is_single_ref):
        for func in oid_funcs:
            if func in repeated_funcs:
                continue

            best_match = {
                'score': 390,
                'file': None,
                'func': None
            }

            ref_oids_to_check = [ref_oids] if is_single_ref else ref_oids
            for ref_oid in ref_oids_to_check:
                ref_oid_funcs = api.get_tags(ref_oid).get("FUNC_TLSH", [])
                for ref_func in ref_oid_funcs:
                    similarity_score = tlsh.diff(func, ref_func)
                    if similarity_score < best_match['score']:
                        best_match.update({'score': similarity_score, 'file': ref_oid, 'func': ref_func})

            if best_match['score'] < 50 or func == best_match['func']:
                oid_result['modified_funcs'][func] = best_match
            else:
                oid_result['new_funcs'][func] = best_match

    def generate_file_report(self):
        matched_execs, unique_col_execs, unique_ref_execs = self.get_file_matches(self.collection_exec, self.reference_exec)
        matched_non_execs, unique_col_non_execs, _ = self.get_file_matches(self.collection_non_exec, self.reference_non_exec)
        sorted_files = self.sort_files(unique_col_execs, unique_ref_execs)
        self.report = {
            'EXECUTABLE_MATCHES': matched_execs,
            'NON_EXECUTABLE_MATCHES': matched_non_execs,
            'MODIFIED_EXECUTABLES': sorted_files['MODIFIED_EXECUTABLES'],
            'NEW_EXECUTABLES': sorted_files['NEW_EXECUTABLES'],
            'NEW_NON_EXECUTABLES': unique_col_non_execs,
            'FAILED_EXECUTABLES': sorted_files['FAILED']
        }

    def calculate_statistics(self):
        return {
            'MATCHES: EXECUTABLES': self._calculate_percentage(self.report["EXECUTABLE_MATCHES"], self.collection_oids),
            'MATCHES: NON-EXECUTABLE': self._calculate_percentage(self.report['NON_EXECUTABLE_MATCHES'], self.collection_oids),
            'MODIFIED: EXECUTABLES': self._calculate_percentage(self.report['MODIFIED_EXECUTABLES'], self.collection_oids),
            'NEW: EXECUTABLES': self._calculate_percentage(self.report['NEW_EXECUTABLES'], self.collection_oids),
            'NEW: NON-EXECUTABLES': self._calculate_percentage(self.report['NEW_NON_EXECUTABLES'], self.collection_oids),
            'FAILED: EXECUTABLES': self._calculate_percentage(self.report['FAILED_EXECUTABLES'], self.collection_oids)
        }

    def print_statistics(self, stats):
        table = PrettyTable()
        table.title = "Collection Statistics"
        table.align = 'l'
        table.field_names = ["Category", "Number of Files", "Percentage of Collection"]
        for key, (total, percentage) in stats.items():
            table.add_row([key, total, percentage])
        print(table)

    def print_failed_executables(self):
        print("\n========================== FAILED EXECUTABLES ==========================")
        for file in self.report['FAILED_EXECUTABLES']:
            table = PrettyTable()
            table.title = f"Failed Executable - File ID: {file}"
            table.field_names = ["Potential File Names"]
            names = api.get_names_from_oid(file)
            for name in names:
                table.add_row([name])
            print(table)

    def print_modified_executables(self):
        print("\n================== MODIFIED EXECUTABLES ==================")
        self._print_category_with_reference(self.report['MODIFIED_EXECUTABLES'])

    def print_new_executables(self):
        print("\n================== NEW EXECUTABLES ==================")
        self._print_category(self.report['NEW_EXECUTABLES'])

    def print_new_non_executables(self):
        print("\n================== NEW NON-EXECUTABLES ==================")
        for file in self.report['NEW_NON_EXECUTABLES']:
            table = PrettyTable()
            table.title = f"NEW NON-EXECUTABLES - File ID: {file}"
            table.field_names = ["Potential File Names"]
            names = api.get_names_from_oid(file)
            for name in names:
                table.add_row([name])
            print(table)

    def _print_category(self, files_report):
        for file_id, report in files_report.items():
            self._print_file_table(file_id)

            if 'func_matches' in report and len(report['func_matches']) > 0:
                self._print_function_matches(report)

            if 'modified_funcs' in report and len(report['modified_funcs']) > 0:
                self._print_modified_functions(report)

            if 'new_funcs' in report and len(report['new_funcs']) > 0:
                self._print_new_functions(report)
            print("\n")

    def _print_category_with_reference(self, files_report):
        for file_id, data in files_report.items():
            ref_file_id = data['REF_FILE_ID']
            self._print_file_with_reference_table(file_id, ref_file_id)

            report = data['REPORT']
            if 'func_matches' in report and len(report['func_matches']) > 0:
                self._print_function_matches(report)

            if 'modified_funcs' in report and len(report['modified_funcs']) > 0:
                self._print_modified_functions(report)

            if 'new_funcs' in report and len(report['new_funcs']) > 0:
                self._print_new_functions(report)
            print("\n")

    def _print_modified_functions(self, report):
        table = prettytable()
        table.align = 'l'
        table.title = "MODIFIED FUNCTIONS"
        table.field_names = ["Function", "Reference File", "Reference Function", "Score"]
        for func, details in report['modified_funcs'].items():
            table.add_row([func, details['file'], details['func'], details['score']])
        print(table)

    def _print_function_matches(self, report):
        table = prettytable()
        table.align = 'l'
        table.title = "EXACT FUNCTION MATCHES"
        table.field_names = ["Reference File", "# of Exact Function Matches"]
        for func, matches in report['func_matches'].items():
            table.add_row([func, matches])
        print(table)

    def _print_new_functions(self, report):
        table = prettytable()
        table.align = 'l'
        table.title = "NEW FUNCTIONS"
        table.field_names = ["Function", "Closest Match File", "Closest Match Function", "Score"]
        for func, details in report['new_funcs'].items():
            table.add_row([func, details['file'], details['func'], details['score']])
        print(table)

    def _print_file_with_reference_table(self, file_id, ref_file_id):
        table = prettytable()
        table.align = 'l'
        table.title = f"File: {file_id} | Reference File: {ref_file_id}"
        table.field_names = ["Potential File Names", "Potential Reference File Names"]
        file_names = list(api.get_names_from_oid(file_id))
        ref_file_names = list(api.get_names_from_oid(ref_file_id))

        max_length = max(len(file_names), len(ref_file_names))
        file_names += [""] * (max_length - len(file_names))
        ref_file_names += [""] * (max_length - len(ref_file_names))

        for file_name, ref_file_name in zip(file_names, ref_file_names):
            table.add_row([file_name, ref_file_name])

        print(table)

    def _print_file_table(self, file_id):
        table = prettytable()
        table.align = 'l'
        table.title = f"File: {file_id}"
        table.field_names = ["Potential File Names"]
        file_names = list(api.get_names_from_oid(file_id))
        for name in file_names:
            table.add_row([name])
        print(table)



    def print_report(self, report):
        # Print func_matches table
        print("=== FUNC MATCHES ===")
        func_matches_table = [(func, matches) for func, matches in report['func_matches'].items()]
        print(tabulate(func_matches_table, headers=["Function ID", "Match Count"], tablefmt="grid"))
        
        # Print modified_funcs table
        print("\n=== MODIFIED FUNCTIONS ===")
        modified_funcs_table = [
            [func, details['file'], details['func'], details['score']]
            for func, details in report['modified_funcs'].items()
        ]
        print(tabulate(modified_funcs_table, headers=["Function", "File", "Mapped Func", "Score"], tablefmt="grid"))
        
        # Print new_funcs table
        print("\n=== NEW FUNCTIONS ===")
        new_funcs_table = [[func] for func in report['new_funcs']]
        print(tabulate(new_funcs_table, headers=["Function"], tablefmt="grid"))


def file_pre_analysis(args, opts):
    if args:
        collections, invalid = api.valid_oids(args)
        oids = api.expand_oids(collections)
    else:
        collections = api.collection_cids()

    force = opts.get('force', None)

    for collection in collections:
        print(f"COLLECTION: {api.get_colname_from_oid(collection)}")
        oids = api.expand_oids(collection)

        p = progress.Progress(len(oids))
        for oid in oids:
            analyzer = FileAnalyzer(oid, force)
            analyzer.get_or_default_tags()
            analyzer.tag_file_info()
            if analyzer.tags["CATEGORY"] == 'executable':
                analyzer.get_archs()
            api.apply_tags(oid, analyzer.tags)
            p.tick()

def collection_pre_analysis(args, opts) -> None:
    if args:
        valid, invalid = api.valid_oids(args)
        collections = [valid]
    else:
        collections = api.collection_cids()

    p = progress.Progress(len(collections))
    for collection in collections:
        collection_tags = {}
        oids = api.expand_oids(collection)

        # Initialize data structures for device attributes
        collection_src_types = {}
        collection_archs = set()
        device_core_strings = {}
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
            exts = tags.get("EXT")
            if exts:
                for ext in exts:
                    device_file_exts[ext] = device_file_exts.get(ext, 0) + 1

            # Handle File Category
            cat = tags.get("CATEGORY")
            device_file_category[cat] = device_file_category.get(cat, 0) + 1

            # Collect architectures
            archs = tags.get("ARCHS")
            if archs:
                for arch in archs:
                    collection_archs.add(arch)
        p.tick()

        # Aggregate device tags
        collection_tags = {
            "SRC_TYPE": collection_src_types,
            "EXT": device_file_exts,
            "CORE": device_core_strings,
            "ARCH": collection_archs,
            "CATEGORY": device_file_category
        }

        api.apply_tags(collection, collection_tags)

def file_analysis(args, opts) -> None:
    # Validate input arguments
    collections, invalid = api.valid_oids(args) if args else (api.collection_cids(), [])
    if invalid:
        logging.warning(f"Invalid OIDs detected: {invalid}")
    
    # Expand OIDs if args are provided
    oids = api.expand_oids(collections) if args else []

    # Determine force option
    force = opts.get('force')

    # Initialize thread pool executor
    with concurrent.futures.ThreadPoolExecutor(max_workers=1) as executor:
        for collection in collections:
            collection_tags = api.get_tags(collection)
            total_exe = collection_tags.get('CATEGORY', {}).get('executable', 0)
            oids = api.expand_oids(collection)

            exe_count = 1
            print(f"Processing COLLECTION: {api.get_colname_from_oid(collection)}")

            for oid in oids:
                analyzer = FileAnalyzer(oid, force)
                analyzer.get_or_default_tags()

                # Process only if CATEGORY is executable
                if analyzer.tags.get("CATEGORY") == 'executable':
                    print(f"Executable {exe_count} of {total_exe}")
                    analyzer.update_archs(collection_tags.get("ARCH"))
                    try:
                        # Submit task to executor
                        future = executor.submit(tag_disasm, oid, force, analyzer.tags)
                        analyzer.tags = future.result(timeout=TIMEOUT_LONG)
                    except concurrent.futures.TimeoutError:
                        print(f"Timeout while processing DISASM for {oid}")
                        _clean_up_disasm()
                        analyzer.tags["DISASM"] = {
                            "RESULT": "TIMEOUT",
                            "PASS": {},
                            "FAIL": {}
                        }
                        analyzer.tags["SELECTED_ARCH"] = None
                    # except Exception as e:
                    #     print(f"Error processing DISASM for {oid}: {e}")
                    finally:
                        future.cancel()

                    if analyzer.tags.get("DISASM", {}).get("RESULT") == "PASS":
                        analyzer.tag_function_tlsh()

                    exe_count += 1

                # Apply the tags to the OID
                api.apply_tags(oid, analyzer.tags)

def collection_analysis(args, opts):
    if args:
        collections, invalid = api.valid_oids(args)
        oids = api.expand_oids(collections)
    else:
        collections = api.collection_cids()

    force = opts.get('force', None)

    p = progress.Progress(collections)
    for collection in collections:
        collection_tags = api.get_tags(collection)
        oids = api.expand_oids(collection)
        collection_disasm = {}
        collection_func_hashes = []
        collection_selected_archs = {}
        for oid in oids:
            oid_tags = api.get_tags(oid)
            if oid_tags["DISASM"]["RESULT"] in collection_disasm:
                collection_disasm[oid_tags["DISASM"]["RESULT"]] += 1
            else:
                collection_disasm[oid_tags["DISASM"]["RESULT"]] = 1

            collection_func_hashes += oid_tags["FUNC_HASHES"]

            if oid_tags["SELECTED_ARCH"]["arch"] in collection_selected_archs:
                collection_selected_archs[oid_tags["SELECTED_ARCH"]["arch"]] += 1
            else:
                collection_selected_archs[oid_tags["SELECTED_ARCH"]["arch"]] = 1
        
        collection_tags["DISASM"] = collection_disasm
        collection_tags["FUNC_HASHES"] = collection_func_hashes
        collection_tags["SELECTED_ARCHS"] = collection_selected_archs

        api.apply_tags(collection, collection_tags)
        p.tick()

def framework_analysis(args, opts):
    if args:
        collections, invalid = api.valid_oids(args)
        oids = api.expand_oids(collections)
    else:
        collections = api.collection_cids()

    force = opts.get('force', None)
    p1 = progress.Progress(len(collections))
    for collection in collections:
        collection_tags = api.get_tags(collection)
        p2 = progress.Progress(len(collections))
        for ref_collection in collections:
            analyzer = FrameworkAnalyzer(collection, ref_collection)
            p2.tick()
        p1.tick()

def compare_collections(args, opts):
    collection = args[0]
    ref_collection = args[1]


def get_file_tags(args, opts):
    if args:
        collections, invalid = api.valid_oids(args)
        oids = api.expand_oids(collections)
    else:
        collections = api.collection_cids()

    for collection in collections:
        oids = api.expand_oids(collection)
        
        for oid in oids:
            tags = api.get_tags(oid)
            pprint(tags)

def get_collection_tags(args, opts):
    if args:
        collections, invalid = api.valid_oids(args)
        oids = api.expand_oids(collections)
    else:
        collections = api.collection_cids()

    for collection in collections:
        tags = api.get_tags(collection)
        pprint(tags)


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
        sample_name = f"{parent_directory_name}-{sample}"
        import_sample(sample_name, sample_path)


def tag_disasm(oid, force, tags):
    archs = tags["ARCHS"]
    results = api.get_field("ghidra_disasm_archs", oid, oid, {"archs": archs})
    if results:
        tags["DISASM"] = results["DISASM"]
        tags["SELECTED_ARCH"] = results["SELECTED_ARCH"]
    else:
        tags["DISASM"] = {
                    "RESULT": "FAIL",
                    "PASS": {},
                    "FAIL": {}
                }
        tags["SELECTED_ARCH"] = None
    return tags

def _clean_up_disasm():
    # List of file paths to be deleted
    scratch_dir = api.scratch_dir
    files_to_delete = [
        "ghidraBenchmarking_MainProcess.gpr",
        "ghidraBenchmarking_MainProcess.lock",
        "ghidraBenchmarking_MainProcess.lock~",
        "ghidraBenchmarking_MainProcess.rep"
    ]

    for file in files_to_delete:
        try:
            os.remove(scratch_dir+file)
            print(f"Deleted: {file}")
        except FileNotFoundError:
            print(f"File not found: {file}")
        except PermissionError:
            print(f"Permission denied: {file}")
        except Exception as e:
            print(f"Error deleting {file}: {e}")

exports = [file_pre_analysis, file_analysis, collection_pre_analysis, collection_analysis, get_file_tags, get_collection_tags, import_samples]