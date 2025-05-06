""" Plugin: Utility functions for managing truth files.
"""
from oxide.core import api
from oxide.core.libraries.re_lib import instruction_to_string, get_slice
from oxide.core.oshell import OxideShell, ShellSyntaxError

import json
from pathlib import Path

NAME = "test_tagging"
DESC = "" 
USG = ""

context_size = [0, -1]

def tag_test(args, opts):
    results = {}

    path = Path(opts['entry_points'])
    with path.open(encoding="utf-8") as fp:
        entry_points = json.load(fp)


    valid, invalid = api.valid_oids(args)
    
    original_oids = valid[0]
    original_oids = get_all_file_names(original_oids)
    stripped_oids = valid[1]
    stripped_oids = get_all_file_names(stripped_oids)

    # Reverse list2 to map filename -> id
    filename_to_id_stripped = {filename: id for id, filename in stripped_oids.items()}

    # Pair the identifiers
    paired_oids = []
    for id1, filename in original_oids.items():
        id2 = filename_to_id_stripped.get(filename)
        if id2:
            paired_oids.append((id1, id2))

    for original, stripped in paired_oids:
        print(original)
        file_name = original_oids[original]
        results[file_name] = {}

        entry = entry_points[file_name]
        target_functions = {item['function_name']: item['description'] for item in entry}

        for original_function in target_functions:
            original_func_offset = get_func_offset(original, original_function)
            if original_func_offset:
                stripped_func_name = get_func_name(stripped, original_func_offset)
                try: 
                    results[file_name][original_function] = {'DESCRIPTION': target_functions[original_function]}
                    for i in context_size:
                        tag = api.retrieve("tag_function_context", stripped, {"func_name": stripped_func_name})
                        print(tag)
                        results[file_name][original_function][i] =  tag
                except:
                    pass
    return results

def test_file_tag(args, opts):
    results = {}

    valid, invalid = api.valid_oids(args)
    
    original_oids = valid[0]
    original_oids = get_all_file_names(original_oids)
    stripped_oids = valid[1]
    stripped_oids = get_all_file_names(stripped_oids)

    # Reverse list2 to map filename -> id
    filename_to_id_stripped = {filename: id for id, filename in stripped_oids.items()}

    # Pair the identifiers
    paired_oids = []
    for id1, filename in original_oids.items():
        id2 = filename_to_id_stripped.get(filename)
        if id2:
            paired_oids.append((id1, id2))

    functions = {}
    for original, stripped in paired_oids:
        functions = api.retrieve("tag_file", stripped)
        for fn in functions:
            functions[fn]['name'] = get_func_name(original, fn)
        results[original_oids[original]] = functions
    return results

def get_function_names(args, opts):
    file = opts['file']
    valid, invalid = api.valid_oids(args)
    
    original_oids = valid[0]
    original_oids = get_all_file_names(original_oids)

    for oid in original_oids:
        if original_oids[oid] == file:
            functions = api.get_field("ghidra_disasm", oid, "functions")
            names = {}
            for f in functions:
                names[f] = functions[f]['name']

    return names

def get_function_names(args, opts):
    file = opts['file']
    valid, invalid = api.valid_oids(args)
    
    original_oids = valid[0]
    original_oids = get_all_file_names(original_oids)

    for oid in original_oids:
        if original_oids[oid] == file:
            functions = api.get_field("ghidra_disasm", oid, "functions")
            names = {}
            for f in functions:
                names[f] = functions[f]['name']

    return names

def tag_firmware(args, opts):
    valid, invalid = api.valid_oids(args)
    oids = api.expand_oids(valid)

    exes, non_exes = separate_oids(oids)

    num_functions = {}

    for oid in exes:
        functions = api.get_field("ghidra_disasm", oid, "functions")
        num_functions[oid] = len(functions)

    sorted_items = sorted(num_functions.items(), key=lambda kv: kv[1])
    sorted_oids = [oid for oid, _ in sorted_items]

    result = {}

    total = len(sorted_oids)
    count = 1
    for oid in sorted_oids:
        print(f"{count} of {total}")
        result[oid] = api.retrieve("tag_file", oid)
        count += 1

def firmware_exes(args, opts):
    valid, invalid = api.valid_oids(args)
    oids = api.expand_oids(valid)

    exes, non_exes = separate_oids(oids)

    num_functions = {}
    result = {}

    for oid in exes:
        functions = api.get_field("ghidra_disasm", oid, "functions")
        num_functions[oid] = len(functions)

    sorted_items = sorted(num_functions.items(), key=lambda kv: kv[1])
    sorted_oids = [oid for oid, _ in sorted_items]

    for oid in sorted_oids:
        file_results = api.retrieve("tag_file", oid)
        if file_results['functions'] == 'FAILED':
            result[oid] = "FAILED"
        elif file_results['functions'] is None:
            result[oid] = None
        else:
            result[oid] = {}
            result[oid]['functions'] = len(file_results['functions'])
            result[oid]['influential functions'] = len(file_results['influential functions'])
    return result


exports = [tag_test, get_function_names, test_file_tag, tag_firmware, firmware_exes]

def separate_oids(oids):
    executables, non_executables = set(), set()
    for oid in oids:
        file_category = api.get_field("categorize", oid, oid)
        if file_category == "executable":
            executables.add(oid)
        else:
            non_executables.add(oid)
    return executables, non_executables

def get_all_file_names(collection):
    file_names = {}
    oids = api.expand_oids(collection)
    for oid in oids:
        file_names[oid] = list(api.get_names_from_oid(oid)).pop()
    return file_names

def get_paired_functions(paired_functions, target_functions):
    results = {}

    matched_functions = paired_functions['matched_funcs']
    lifted_matched_functions = paired_functions['lifted_matched_funcs']
    modified_functions = paired_functions['modified_funcs']

    results = extract_pairs(matched_functions, target_functions, results)
    results = extract_pairs(lifted_matched_functions, target_functions, results)
    results = extract_pairs(modified_functions, target_functions, results)
    return results


def extract_pairs(functions, target_functions, results):
    for match in functions:
        if functions[match]['func_name'] in target_functions:
            results[functions[match]['func_name']] = functions[match]['baseline_func_name']
            continue
    return results


def get_func_offset(oid, name):
    functions = api.get_field("ghidra_disasm", oid, "functions")
    if functions:
        for func in functions:
            if functions[func]['name'] == name:
                return func
    return None
        
def get_func_name(oid, offset):
    functions = api.get_field("ghidra_disasm", oid, "functions")
    if functions:
        for func in functions:
            if func == offset:
                return functions[func]['name']
    return None