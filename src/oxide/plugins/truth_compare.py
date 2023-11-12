import sys
import os
import json
import logging
import numpy as np

from typing import List, BinaryIO

from oxide.core import api

NAME = "truth_compare"
compare_logger = logging.getLogger(NAME)


def compare_min_truth(args, opts):
    """
        Compares where instructions in the min_truth are either missing or not the same.
        Returns ranges where the tool either agrees or disagrees with the min_truth
        Example of output:
            {
                "Bap": {
                "Correct" : [(0,100),(600,750)]
                "Incorrect" : [(200,600), (750,1000)]
                }
            }
        Syntax: compare_min_truth oid
        Options:
            file - specifies dumping to output file. Defaults to stdout.
            path - specifies where the json in min truth comparison is dumped. Default = "/localstore/(file_name)_min_truth_distances.json"
            graph - If graph is set, Uses matplotlib to plot out these distances. Outputs the fig output to localstore/graphs
            exclude - Exclude a particular disasm. Disasms included in this comparison:
                    ['objdump', 'ghidra_disasm', 'ida_disasm', 'fst_angr_disasm', 'emu_angr_disasm',
                    'radare_disasm', 'radare_linear', 'bap_disasm', 'pharos_disasm', 'binja_disasm',
                    'ddisasm_disasm', 'problstc_ref', 'problstc_disasm', 'min_truth', 'max_truth']
            only - Only compare with disassembler(s). Delimit with a comma ",".
            min_range - Set the X-axis to the range of min truth
    """
    function_mapping = {}
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")
    valid = api.expand_oids(valid)

    # Sets default output file for displaying output
    try:
        pipe = open(opts['file'], 'w')
    except KeyError:
        pipe = sys.stdout

    for oid in valid:
        fname = _name(oid)
        try:
            file_path = open[opts['path']]
        except KeyError:
            file_path = f"localstore/{fname}_min_truth_distances.json"
        tool_list = ['objdump', 'ghidra_disasm', 'ida_disasm']  # 'bap_bwoff'
        tool_list += ['fst_angr_disasm', 'emu_angr_disasm', 'radare_disasm', 'bap_disasm']
        tool_list += ['pharos_disasm', 'binja_disasm', 'ddisasm_disasm']
        tool_list += ['min_truth', 'max_truth']
        to_remove = []
        disasm_maps = {}
        function_mapping = {}
        if "exclude" in opts:
            try:
                tool_list.remove(opts['exclude'])
            except ValueError:
                print(f"{opts['exclude']} not found in tool_list")
        elif "only" in opts:
            if opts['only'] in tool_list:
                includes = opts['only'].split(",")
                tool_list =['min_truth', 'max_truth']
                for disasms in includes:
                    tool_list.append(disasms)
            else:
                raise ValueError(f"{opts['only']} not found in tool_list")
        # compare_logger.info
        compare_logger.debug("Comparing Inst within %s", oid)

        for tool in tool_list:
            # compare_logger.info
            compare_logger.info("\tOn tool %s", tool)

            module_name = tool
            if tool == "min_truth":
                module_name = 'truth_store'
                options = {'type': 'disasm_min'}
            elif tool == "max_truth":
                module_name = 'truth_store'
                options = {'type': 'disasm_max'}
            else:
                options = {'disassembler': module_name}

            if module_name == 'truth_store':
                disasm = {oid: api.retrieve(module_name, oid, options)}
            elif module_name == 'objdump':
                # Used for functions
                out_map = api.retrieve(module_name, oid, options)
                disasm = api.retrieve('disassembly', oid, options)

                if not out_map:
                    compare_logger.info('Objdump failed to return output')
                else:
                    if 'functions' in out_map:
                        function_mapping = out_map['functions']
                    else:
                        compare_logger.info('Objdump found no functions for %s', oid)
            else:
                disasm = api.retrieve('disassembly', oid, options)

            if disasm:
                # disasm returned as dictionary
                disasm = disasm.pop(list(disasm.keys())[0])
            else:
                to_remove.append(tool)
                continue

            if 'instructions' in disasm:
                inst_map = disasm['instructions']
            if inst_map:
                disasm_maps[tool] = inst_map

            else:
                # Add tool to list of tools to remove
                compare_logger.info("Removing (%s) in instruction comparison", module_name)
                to_remove.append(tool)

        for tool in to_remove:
            if tool in tool_list:
                tool_list.remove(tool)

        fname = _name(oid)
        print("Comparing {} ({}).\n".format(oid, fname), file=pipe)

        if 'min_truth' not in tool_list:
            raise ShellSyntaxError("Min truth not found for this oid")

        _min_truth_compare(fname, oid, disasm_maps, function_mapping, tool_list, opts, pipe, file_path)


exports = [compare_min_truth]


# ------------ Utilities -----------------

def _output_graph(name, opts, range_data):
    try:
        import matplotlib.pyplot as plt
        import matplotlib.patches as mpatches
    except ImportError as e:
        print(e)
        return

    if opts['graph'] == "" or len(opts['graph']) < 1:
        graph_output_directory = "localstore/graphs/"
    else:
        graph_output_directory = opts['graph']

    if not os.path.exists(graph_output_directory):
        os.makedirs(graph_output_directory)
        print("Directory", graph_output_directory, "created.")

    def calculate_missing_ranges(correct_ranges, incorrect_ranges):
        combined = correct_ranges + incorrect_ranges
        combined.sort(key=lambda x: x[0])

        missing = []

        for i in range(len(combined) - 1):
            if combined[i][1] < combined[i+1][0] - 1:
                missing.append((combined[i][1] + 1, combined[i+1][0] - 1))

        return missing
    def sort_tool_labels(tool):
        if tool == "min_truth":
            return -1
        elif tool == "max_truth":
            return 1
        else:
            return 0

    sorted_tool_labels = sorted(range_data.keys(), key=sort_tool_labels)

    fig, ax = plt.subplots()

    y_labels = []
    ## Finds range so that the min_truth is in the middle
    min_truth_data = range_data['min_truth']
    min_truth_correct_ranges = min_truth_data['Correct']
    min_truth_incorrect_ranges = min_truth_data['Incorrect']
    min_truth_min_offset = min(range[0] for range in min_truth_correct_ranges + min_truth_incorrect_ranges)
    min_truth_max_offset = max(range[1] for range in min_truth_correct_ranges + min_truth_incorrect_ranges)
    min_truth_range_length = min_truth_max_offset - min_truth_min_offset

    # Find the maximum range length for all the tools
    max_range_length = min_truth_range_length
    for tool, tool_data in range_data.items():
        if tool not in ['min_truth', 'max_truth']:
            correct_ranges = tool_data['Correct']
            if tool_data['Incorrect'] == [(0,0)]:
                incorrect_ranges = correct_ranges
            else:
                incorrect_ranges = tool_data['Incorrect']
            min_offset = min(range[0] for range in correct_ranges + incorrect_ranges)
            max_offset = max(range[1] for range in correct_ranges + incorrect_ranges)
            range_length = max_offset - min_offset
            max_range_length = max(max_range_length, range_length)

    # Calculate the x-axis limits based on the maximum range length
    xlim_left = min_truth_min_offset - (max_range_length - min_truth_range_length) // 2
    xlim_right = xlim_left + max_range_length
    for i, tool in enumerate(sorted_tool_labels):
        tool_data = range_data[tool]
        y_labels.append(tool)
        correct_ranges = tool_data['Correct']
        incorrect_ranges = tool_data['Incorrect']

        missing_ranges = calculate_missing_ranges(correct_ranges, incorrect_ranges)

        for ranges, color in zip([correct_ranges, incorrect_ranges, missing_ranges], ['green', 'red', 'blue']):
            if tool == "min_truth" or tool == 'max_truth':
                if color == 'red':
                    continue

            for start, end in ranges:
                if start == 1:
                    continue
                ax.barh(i, end - start, left=start, height=0.3, align='center', color=color, alpha=1)

    ax.set_yticks(range(len(y_labels)))
    ax.set_yticklabels(y_labels)
    ax.set_xlabel('Offset')
    ax.set_xlim(xlim_left, xlim_right)
    if 'min_range' in opts:
        ax.set_xlim(min(min_truth_data['Correct']))
    ax.set_ylabel("Tool")
    ax.set_title(f"Min / Max Disassembly Comparison for {name}")

    correct_patch = mpatches.Patch(color='green', label='Correct')
    incorrect_patch = mpatches.Patch(color='red', label='Incorrect')
    missing_patch = mpatches.Patch(color='blue', label='Missing')

    # Move the legend below the y-axis
    plt.legend(handles=[correct_patch, incorrect_patch, missing_patch], loc='best', bbox_to_anchor=(0.5, -0.25))

    # Adjust the figure's bottom margin
    plt.subplots_adjust(bottom=0.2)
    bbox = 'tight'
    output = graph_output_directory + f"{name}.eps"
    plt.savefig(output, format='eps', bbox_inches = bbox)


def _min_truth_compare(sample: str, oid: str, disasm_maps: dict, function_mapping: dict,
                     tool_list: List[str], opts: dict, pipe: BinaryIO, file_path) -> None:

    # blocks located in out_maps
    inst_maps = []
    offsets_lists = []

    # Extract instructio nstor for each tool, remaining and using option for min truth
    for tool in tool_list:
        if tool not in disasm_maps:
            continue
        inst_map = disasm_maps[tool]

        if 'meta' in inst_map:
            del inst_map['meta']

        # create list of items, and list of offsets with items for comparison
        offsets = [item for item in inst_map]

        # add to list of items for each tool
        inst_maps.append(inst_map)
        offsets_lists.append(offsets)

    header = api.get_field("object_header", oid, oid)
    # Compute sections for oid
    section_list = []
    for sec, sec_info in header.section_info.items():
        # start, end, name, flags
        section_list.append((sec_info['section_offset'],
                                sec_info['section_offset'] + sec_info['section_len'],
                                sec,
                                str(sec_info['flags'])))

    color = 'color' in opts
    union_offsets = set()
    for offset_list in offsets_lists:
        offset_set = set(offset_list)
        if 'meta' in offset_set:
            offset_set.remove('meta')
        # If instruction with None for address, remove
        offset_set.discard(None)
        union_offsets = union_offsets.union(offset_set)
    union_offsets = sorted(list(union_offsets))

    min_truth_distances = _compute_min_truth_distance(offsets_lists, tool_list)
    output = open(file_path, 'w')
    json.dump(min_truth_distances, output, indent=4)

    for x, y in min_truth_distances.items():
        print(x,y, "\n",file=pipe)

    if 'graph' in opts:
        _output_graph(_name(oid),opts, min_truth_distances)


def _compute_min_truth_distance(offsets_list, tool_list):
    """
        Compares all offsets from the given tool list to min_truth
        Input -
            offsets_list (list of lists of tuples) - A list of list of instruction tuples for each tool
                list of inst offsets from angr
                list of inst offsets from bap
            ... etc
            tool_list (list of tools used) - A list of tools
        Output -
            min_truth_distances (dict) - dict that stores where each tool disagrees with min_truth
    """

    min_truth_distances = {}
    if 'min_truth' not in tool_list:
        raise ShellSyntaxError("Min_truth not found in oid")
    else:
        min_truth_index = tool_list.index("min_truth")
        min_truth = offsets_list[min_truth_index]
        min_truth_range = (min(min_truth), max(min_truth))
        min_truth_set = set(offsets_list[min_truth_index])

    if 'max_truth' not in tool_list:
        raise ShellSyntaxError("max_truth not found in oid")
    else:
        max_truth_index = tool_list.index("max_truth")
        max_truth = offsets_list[max_truth_index]
        max_truth_range = (min(max_truth), max(max_truth))
        max_truth_set = set(offsets_list[max_truth_index])

    #Gets ranges for each tool intersection or difference
    #Max_distance = 8 for the reason that most x86 instructions are 1-6 bytes.
    def get_ranges(offsets, max_distance=8):
        if len(offsets) < 1:
           return[(0,0)]
        ranges = []
        start = offsets[0]
        end = offsets[0]

        for offset in offsets[1:]:
            if offset <= end + max_distance:
                end = offset
            else:
                ranges.append((start, end))
                start = offset
                end = offset

        ranges.append((start, end))
        return ranges

    #In the case where there are incorrects between correct ranges, splits correct range and vice versa
    def split_ranges_on_intersection(correct_ranges, incorrect_ranges):
        new_correct_ranges = []

        for correct_range in correct_ranges:
            temp_ranges = [(correct_range[0], correct_range[1])]

            for incorrect_range in incorrect_ranges:
                for temp_range in temp_ranges:
                    if incorrect_range[0] > temp_range[0] and incorrect_range[1] < temp_range[1]:
                        temp_ranges.remove(temp_range)
                        temp_ranges.append((temp_range[0], incorrect_range[0] - 1))
                        temp_ranges.append((incorrect_range[1] + 1, temp_range[1]))
                    elif incorrect_range[0] <= temp_range[0] and incorrect_range[1] >= temp_range[0] and incorrect_range[1] < temp_range[1]:
                        temp_ranges.remove(temp_range)
                        temp_ranges.append((incorrect_range[1] + 1, temp_range[1]))
                    elif incorrect_range[0] > temp_range[0] and incorrect_range[0] <= temp_range[1] and incorrect_range[1] >= temp_range[1]:
                        temp_ranges.remove(temp_range)
                        temp_ranges.append((temp_range[0], incorrect_range[0] - 1))

            new_correct_ranges.extend(temp_ranges)
        return new_correct_ranges
    for tool_index in range(len(tool_list)):
        tool_set = set(offsets_list[tool_index])
        tool_name = tool_list[tool_index]
        incorrect = sorted((tool_set - max_truth_set).union(max_truth_set - tool_set))
        correct = sorted(list(max_truth_set.intersection(tool_set)))
        # extra_incorrect = set(filter(lambda x: x < min_truth_min_range or x > min_truth_max_range, offsets_list[tool_index]))
        # # Combine the incorrect sets
        # incorrect = set(incorrect).union(extra_incorrect)
        # with open("test.txt", 'a') as f:
        #     f.write(f"{tool_name} : \n")
        #     f.write(f"correct = {correct}\n")
        #     f.write(f"incorrect = {incorrect}\n")
        #     f.write(f"min_truth = {list(min_truth_set)}\n")
        # if len(incorrect) < 1 or len(correct) < 1:
        #     if tool_name == "min_truth" or tool_name == "max_truth":
        #         pass
        #     else:
        #         print(f"Excluding {tool_name}: has incorrect length {len(incorrect)}, correct_length {len(correct)}")
        #         continue

        if tool_name == "min_truth":
            ##Puts one incorrect instruction in min truth to make graph work
            incorrect_ranges = [(min_truth_range[0] - 1, min_truth_range[0] - 1)]
            correct_ranges = get_ranges(sorted(list(min_truth)))
        elif tool_name == "max_truth":
            ##Puts one incorrect instruction in min truth to make graph work
            incorrect_ranges = [(max_truth_range[0] - 1, max_truth_range[0] - 1)]
            correct_ranges = get_ranges(sorted(list(max_truth)))
        else:
            correct_ranges = get_ranges(sorted(list(correct)))
            incorrect_ranges = get_ranges(sorted(list(incorrect)))
            correct_ranges = split_ranges_on_intersection(correct_ranges, incorrect_ranges)

        min_truth_distances[tool_name] = {
            "Correct": correct_ranges,
            "Incorrect": incorrect_ranges
        }

    return min_truth_distances

def _name(oid):
    if api.exists("file_meta", oid):
        return api.get_field("file_meta", oid, "names").pop()

    if api.exists("collections_meta", oid):
        return api.get_colname_from_oid(oid)
    return None