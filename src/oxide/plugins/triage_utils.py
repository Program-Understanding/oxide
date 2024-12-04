
from oxide.core.oxide import api
import pprint
import pandas as pd
import csv
import os 
import tlsh

from oxide.core import progress, api

print("Firmware Triage Pipeline Plugin")
info = """
        Plugin Commands
        • Importing Data
            • import_devices /path/to/firmware/samples -> Imports samples from a given directory as collections
        • Analyzing Data
            • tag_files &collection -> Analyzes and tags files of a collection
            • tag_collection &collection -> Analyzes and tags a collection
        • Viewing Results
            • get_file_tags &collection -> View the file tags of a collection
            • get_collection_tags &collection -> View the tags of a collection
        • Other
            • filter_tags &collection --category=value -> Filters files in a collection based of a specific flag value
        """
print(info)

pp = pprint.PrettyPrinter(depth=4)

def intersection_data(args, opts):
    file_intersections = {}
    total_function_intersections = {}
    unqiue_function_intersections = {}
    near_matches = {}

    cids = api.collection_cids()
    for c in cids:
        c_name = api.get_colname_from_oid(c)
        file_intersections[c_name] = {}
        total_function_intersections[c_name] = {}
        unqiue_function_intersections[c_name] = {}
        near_matches[c_name] = {}
        c_oids = set(api.expand_oids(c))
        p = progress.Progress(len(cids))
        for ref_c in cids:
            p.tick()
            ref_c_name = api.get_colname_from_oid(ref_c)
            ref_c_oids = set(api.expand_oids(ref_c))

            # File Matches
            file_intersections[c_name][ref_c_name] = len(c_oids.intersection(ref_c_oids))

            # All Function Matches
            c_ref_funcs_tlsh = api.get_tags(ref_c)["FUNC_TLSH"]
            c_funcs_tlsh = api.get_tags(c)["FUNC_TLSH"]
            total_function_intersections[c_name][ref_c_name] = len(set(c_funcs_tlsh) & set(c_ref_funcs_tlsh))

            # Function Matches From Unique Files
            if unqiue_function_intersections.get(ref_c_name) and unqiue_function_intersections[ref_c_name].get(c_name):
                unqiue_function_intersections[c_name][ref_c_name] = unqiue_function_intersections[ref_c_name][c_name]
            else:
                c_unique_files = c_oids.difference(ref_c_oids)
                ref_c_unique_files = ref_c_oids.difference(c_oids)
                matches = 0
                for c_oid in c_unique_files:
                    if api.get_tags(c_oid).get("FUNC_TLSH"):
                        c_oid_funcs_tlsh = api.get_tags(c_oid)["FUNC_TLSH"]
                        for ref_c_oid in ref_c_unique_files:
                            if api.get_tags(ref_c_oid).get("FUNC_TLSH"):
                                ref_c_oid_funcs_tlsh = api.get_tags(ref_c_oid)["FUNC_TLSH"]
                                matches += len(set(c_oid_funcs_tlsh) & set(ref_c_oid_funcs_tlsh))
                unqiue_function_intersections[c_name][ref_c_name] = matches

            # Near Matches From Unique Files
            # if near_matches.get(ref_c_name) and near_matches[ref_c_name].get(c_name):
            #     near_matches[c_name][ref_c_name] = near_matches[ref_c_name][c_name]
            # else:
            #     c_funcs_tlsh = api.get_tags(c).get("FUNC_TLSH")
            #     c_ref_funcs_tlsh = api.get_tags(ref_c).get("FUNC_TLSH")
            #     near_matches[c_name][ref_c_name] = 0
            #     for c_hash in c_funcs_tlsh:
            #         if c_hash not in total_function_intersections[c_name][ref_c_name]:
            #             for c_ref_hash in c_ref_funcs_tlsh:
            #                 if c_ref_hash not in total_function_intersections[c_name][ref_c_name]:
            #                     difference = tlsh.diff(c_hash, c_ref_hash)
            #                     if difference <= 50:
            #                         near_matches[c_name][ref_c_name] += 1

                    

    # Convert the dictionary into a pandas DataFrame
    df_files = pd.DataFrame(file_intersections).T  # Transpose to get sub-dicts as rows
    df_total_functions = pd.DataFrame(total_function_intersections).T  # Transpose to get sub-dicts as rows
    df_unique_functions = pd.DataFrame(unqiue_function_intersections).T  # Transpose to get sub-dicts as rows
    df_near_matches = pd.DataFrame(near_matches).T  # Transpose to get sub-dicts as rows

    df_files = df_files.sort_index(axis=0).sort_index(axis=1)
    df_total_functions = df_total_functions.sort_index(axis=0).sort_index(axis=1)
    df_unique_functions = df_unique_functions.sort_index(axis=0).sort_index(axis=1)
    df_near_matches = df_near_matches.sort_index(axis=0).sort_index(axis=1)

    print("---------------------FILE MATCHES---------------------")
    print(df_files)
    print("\n")
    print("---------------------TOTAL FUNCTION MATCHES---------------------")
    print(df_total_functions)
    print("---------------------FUNCTION MATCHES FROM UNIQUE FILES---------------------")
    print(df_unique_functions)
    print("---------------------NEAR FUNCTION MATCHES FROM---------------------")
    print(df_near_matches)

    df_files.to_csv("/home/nathan/Documents/file_matches.csv", index=True)
    df_total_functions.to_csv("/home/nathan/Documents/function_matches.csv", index=True)
    df_unique_functions.to_csv("/home/nathan/Documents/unique_matches.csv", index=True)
    df_near_matches.to_csv("/home/nathan/Documents/near_matches.csv", index=True)

def collection_disasm_stats(args, opts):
    if args:
        valid, invalid = api.valid_oids(args)
        devices = [valid]
    else:
        devices = api.collection_cids()

    for device in devices:
        device_tags = {}
        oids = api.expand_oids(device)

        device_disasm = {}
        device_disasm["PASS"] = 0
        device_disasm["FAIL"] = 0
        device_disasm["FOUND_ARCH_DISASM"] = 0

        
        for oid in oids:
            tags = api.get_tags(oid)

            if not tags:
                continue

            if "DISASM" in tags:
                disasm_result = tags["DISASM"]["RESULT"]
                
                if disasm_result == "PASS":
                    device_disasm["PASS"] += 1

                    if 'DEFAULT' not in tags["DISASM"]["PASS"]:
                        device_disasm["FOUND_ARCH_DISASM"] += 1
                else:
                    device_disasm["FAIL"] += 1

        device_tags["DISASM"] = device_disasm

        name = api.get_colname_from_oid(device)
        print("\n----------------------------------------------")
        print(f"cid - {device}\nFirmware - {name}\ndevice_disasm -")
        pp.pprint(device_disasm)
        print("----------------------------------------------")

def num_files_disasm(args, opts):
    if args:
        collections, invalid = api.valid_oids(args)
        oids = api.expand_oids(collections)
    else:
        collections = api.collection_cids()
    
    total_exes = 0
    total_disasm = 0

    for collection in collections:
        exe_count = 0
        disasm_count = 0
        pass_count = 0
        fail_count = 0
        timeout_count = 0
        oids = api.expand_oids(collection)
        for oid in oids:
            if api.get_tags(oid) is None:
                continue
            elif len(api.get_tags(oid)) > 1:
                tags = api.get_tags(oid)
                if tags.get("FILE_CATEGORY") == "executable":
                    exe_count += 1
                    if tags.get("DISASM"):
                        disasm_count += 1
                        if tags["DISASM"].get("RESULT") == "PASS":
                            pass_count += 1
                        elif tags["DISASM"].get("RESULT") == "FAIL":
                            fail_count += 1       
                        if tags["DISASM"].get("RESULT") == "TIMEOUT":
                            pass_count += 1
        print(f"{api.get_colname_from_oid(collection)}: {disasm_count} of {exe_count} ({(disasm_count/exe_count) * 100}%)")
        print(f"\tPASS: {pass_count}")
        print(f"\tFAIL: {fail_count}")
        print(f"\tTIMEOUT: {timeout_count}")
        total_exes += exe_count
        total_disasm += disasm_count
    print(f"TOTAL: {total_disasm} of {total_exes} ({(total_disasm/total_exes) * 100}%)")
exports = [collection_disasm_stats, num_files_disasm, intersection_data]

############################
### SUPPORTING FUNCTIONS ###
############################

def _print_csv(path, data):
    # Step 1: Collect all possible keys across all samples
    all_keys = set()
    for file_name, entry in data.items():
        flat_data = _flatten_dict(entry)
        all_keys.update(flat_data.keys())

    # Convert set to sorted list to ensure consistent order of columns
    all_keys = sorted(all_keys)

    # Step 2: Write to CSV
    with open(path, mode='w', newline='') as file:
        writer = csv.writer(file)
        
        # Write the header: include "file_name" column + all dynamic keys
        writer.writerow(['file_name'] + all_keys)

        # Write the data for each file
        for file_name, entry in data.items():
            flat_data = _flatten_dict(entry)
            # Ensure values are aligned with the keys
            row = [file_name] + [flat_data.get(key, None) for key in all_keys]
            writer.writerow(row)

# Recursive function to flatten nested dictionaries
def _flatten_dict(d, parent_key='', sep='_'):
    items = []
    for k, v in d.items():
        new_key = f"{parent_key}{sep}{k}" if parent_key else k
        if isinstance(v, dict):
            items.extend(_flatten_dict(v, new_key, sep=sep).items())
        else:
            items.append((new_key, v))
    return dict(items)
