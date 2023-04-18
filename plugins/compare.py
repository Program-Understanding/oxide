"""
Copyright 2023 National Technology & Engineering Solutions
of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS,
the U.S. Government retains certain rights in this software.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
"""

""" Plugin: Scripts for comparing results of analysis tools.
"""
import sys
import os
import json
import logging
import numpy as np

from typing import List, BinaryIO

from core import api

# Spacing variable used for matrices, output
DEFAULT_SPACING = 15
spacing = DEFAULT_SPACING
spacing_str = "%%%ds" % spacing

NAME = "compare"
compare_logger = logging.getLogger(NAME)


def save_facts(args: List[str], opts: dict) -> None:
    """ Dumps output from extractor modules used in comparison in human readable format
            scratch/data/oid/tool.disasm
            scratch/data/oid/tool.blocks
            scratch/data/oid/tool.function
        Output format is JSON, with small preference tweaks for readability.
            one entry per line, but values are on single lines (reason for not using indent=4)
    """
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")
    valid = api.expand_oids(valid)

    # Set output directory
    out_dir = os.path.join(api.scratch_dir, "data")
    if "dir" in opts and os.path.exists(opts["dir"]):
        out_dir = opts["dir"]

    # For each tool that is available, fetch saved results
    disassemblers = api.get_available_modules("oid", "disassembler")

    for oid in valid:
        fname = _name(oid)

        os.makedirs(os.path.join(out_dir, fname), exist_ok=True)
        for tool in disassemblers:
            compare_logger.info(tool)
            out_map = api.retrieve(tool, oid)
            if out_map is not None:
                if 'instructions' in out_map:
                    out_list = []
                    # remove meta from dump
                    if "meta" in out_map['instructions']:
                        del out_map['instructions']['meta']
                    for key, meumonic in out_map['instructions'].items():
                        out_list.append([key, meumonic.replace('\t', '')])

                    # Disassembly, reformated (manually for custom appearance)
                    outlist_string = json.dumps(out_list)
                    format_outlist = outlist_string.replace('],', '],\n')
                    format_outlist = format_outlist.replace('},', '},\n')

                    disasm_file = os.path.join(out_dir, fname, "{}.disasm".format(tool))
                    with open(disasm_file, "w") as disasm_file:
                        print(format_outlist, file=disasm_file)

                if 'original_blocks' in out_map:
                    # Basic block output
                    block_file = os.path.join(out_dir, fname, "{}.blocks".format(tool))
                    with open(block_file, "w") as block_file:
                        print(json.dumps(out_map["original_blocks"], indent=4), file=block_file)

                if "functions" in out_map:
                    # Header, makes not machine readable without excluding first line
                    out_list = [{"oid": oid, "type": "functions"}]

                    # Remove meta from dump
                    if "meta" in out_map['functions']:
                        del out_map['functions']['meta']

                    # Remove any default addresses of -1
                    if -1 in out_map['functions']:
                        del out_map['functions'][-1]

                    for key, value in out_map['functions'].items():
                        if key is None:
                            compare_logger.debug("Function at null offset, get_offset failed %s %s", key, value["name"])
                            continue

                        if 'blocks' in value and value["blocks"] == [None]:
                            # FIXME:: Null blocks in some functions?
                            value["blocks"] = ["Unknown"]
                        out_list.append([int(key), value])
                    outlist_string = json.dumps(out_list)
                    format_outlist = outlist_string.replace('],', '],\n')
                    format_outlist = format_outlist.replace('},', '},\n')
                    function_file = os.path.join(out_dir, fname, "{}.functions".format(tool))
                    print(format_outlist, file=open(function_file, "w"))
            else:
                logging.info("Excluding %s", tool)


def compare_radare(args: List[str], opts: dict) -> None:
    """
        Runs a linear sweep vs informed recursive disassembly for comparison.
        Syntax: compare oid
    """
    global spacing
    global spacing_str
    spacing = DEFAULT_SPACING * 2
    # recompute spacing string
    spacing_str = "%%%ds" % spacing
    valid, invalid = api.valid_oids(args)
    if not valid:
        spacing = DEFAULT_SPACING
        spacing_str = "%%%ds" % spacing
        raise ShellSyntaxError("No valid oids found")
    valid = api.expand_oids(valid)

    # Set default output file for displaying output
    try:
        pipe = open(opts['file'], "w")
    except KeyError:
        pipe = sys.stdout

    for oid in valid:
        # Comparing all available tools
        to_remove = []
        tool_list = ['radare_disasm', 'radare_linear']
        out_maps = {}
        function_mapping = {}

        for tool in tool_list:
            out_map = api.retrieve(tool, oid)

            # From extracted map to instructions and basic blocks, check if runtime failure
            if out_map is not None:
                if tool == 'objdump' and 'functions' in out_map:
                    function_mapping = out_map['functions']

                if 'meta' in out_map:
                    del out_map['meta']

                out_maps[tool] = out_map['instructions']
            else:
                # Add tool to list of tools to remove
                to_remove.append(tool)

        for tool in to_remove:
            if tool in tool_list:
                tool_list.remove(tool)

        fname = _name(oid)

        header = api.get_field("object_header", oid, oid)
        if not header:
            spacing = DEFAULT_SPACING
            spacing_str = "%%%ds" % spacing
            return

        # find section containing entry point
        if 'radare_linear' in out_maps:
            first_offset = list(out_maps['radare_linear'].keys())[0]
            entry_section = header.find_section(header.get_rva(first_offset))
            if entry_section is not None:
                section_name = entry_section['name']
                section_offset = header.section_info[section_name]['section_offset']
                section_end = section_offset + header.section_info[section_name]['section_len']
                print("With section of interest starting at [{} - {}]".format(section_offset,
                                                                              section_end),
                      file=pipe)
                print("Comparing {}.\n".format(oid), file=pipe)
                _inst_comparison(fname, oid, out_maps, function_mapping, tool_list, opts, pipe)
    spacing = DEFAULT_SPACING
    spacing_str = "%%%ds" % spacing


def compare_insns(args, opts):
    """
        Runs a variety of analysis tools and compares instructions found.
        Syntax: compare_insns oid
        Options:
            file - specifies dumping to output file
            dir - specifies out directory to dump output
            verbose - Includes breakdown of instuctions per tool
            color - Adds coloring to output to make easier to view
    """
    function_mapping = {}
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")
    valid = api.expand_oids(valid)

    # Set default output file for displaying output
    try:
        pipe = open(opts['file'], "w")
    except KeyError:
        pipe = sys.stdout

    for oid in valid:
        fname = _name(oid)
        pipe = open("localstore/{}.insn_comparison.txt".format(fname), "w")

        # Comparing all available tools
        tool_list = ['objdump', 'ghidra_disasm', 'ida_disasm']  # 'bap_bwoff'
        tool_list += ['fst_angr_disasm', 'emu_angr_disasm', 'radare_disasm', 'radare_linear', 'bap_disasm']
        tool_list += ['pharos_disasm', 'binja_disasm', 'ddisasm_disasm', 'problstc_ref', 'problstc_disasm']
        tool_list += ['min_truth', 'max_truth']
        to_remove = []
        disasm_maps = {}
        function_mapping = {}

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
                disasm = api.retrieve(module_name, oid, options)
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
            try:
                inst_map = disasm['instructions']
            except:
                pass

            # From extracted map to instructions and basic blocks, check if runtime failure
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

        _inst_comparison(fname, oid, disasm_maps, function_mapping, tool_list, opts, pipe)


def compare_blocks(args, opts):
    """
        Runs a variety of analysis tools and compares contents of blocks found.
        Syntax: compare_insns oid
        Options:
            file - specifies dumping to output file
            dir - specifies out directory to dump output
            verbose - Includes breakdown of instuctions per tool
            color - Adds coloring to output to make easier to view
    """
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")
    valid = api.expand_oids(valid)

    out_dir = "data"
    if "dir" in opts:
        out_dir = opts["dir"]

    # Set default output file for displaying output, file sends all output to one file
    try:
        pipe = open(os.path.join(out_dir, opts['file']), "w")
    except KeyError:
        pipe = sys.stdout

    for oid in valid:
        # exclude at minimum objdump because no tool generated basic blocks
        to_remove = ['objdump']

        fname = _name(oid)
        print("Analyzing {}".format(fname))
        if "dir" in opts:
            # If out directory provided, open file in directory
            vlvl = ".verbose" if ('verbose' in opts and opts['verbose'] == 2) else ""
            pipe = open("{}{}.block_comparison.txt".format(fname, vlvl), "w")

        # Comparing all available tools, omitting Objdump as does not define blocks
        tool_list = ['objdump', 'ghidra_disasm', 'fst_angr_disasm', 'emu_angr_disasm']
        tool_list += ['ida_disasm', 'bap_disasm', '_disasm', 'ddisasm_disasm']  # 'bap_bwoff'
        tool_list += ['min_truth']
        out_maps = {}
        # function_mappping = {}

        for tool in tool_list:
            options = {}
            blocks = None
            module_name = tool
            if tool == "min_truth":
                module_name = 'truth_store'
                options = {'type': 'block_min'}
            elif tool == "max_truth":
                module_name = 'truth_store'
                options = {'type': 'block_max'}
            elif tool == "ghidra3":
                module_name = 'ghidra_disasm'
                options = {'disassembler': module_name, 'version': 3}
            else:
                options = {'disassembler': module_name}

            # from standardized name and settings, request blocks
            if module_name == 'truth_store':
                blocks = api.retrieve(module_name, oid, options)
            elif module_name == 'objdump':
                # Used for functions
                out_map = api.retrieve(module_name, oid, options)

                if not out_map:
                    compare_logger.info('Objdump failed to return output')
                else:
                    if 'functions' in out_map:
                        function_mapping = out_map['functions']
                    else:
                        compare_logger.info('Objdump found no functions for %s', oid)
            else:
                blocks = api.retrieve('basic_blocks', oid, options)

            if blocks:
                # disasm returned as dictionary
                blocks = blocks.pop(list(blocks.keys())[0])
            else:
                compare_logger.warning("\t\t removing %s due to empty output", tool)
                to_remove.append(tool)
                continue

            # From extracted map to instructions and basic blocks, check if runtime failure
            if blocks is not None or blocks == {}:
                out_maps[tool] = blocks
            else:
                # Add tool to list of tools to remove
                logging.warning("\t\t removing %s due to empty output", tool)
                to_remove.append(tool)

        for tool in to_remove:
            if tool in tool_list:
                tool_list.remove(tool)

        print("Comparing {} ({}).\n".format(oid, fname), file=pipe)

        _block_comparison(fname, out_maps, function_mapping, tool_list, opts, pipe)


def compare_funcs(args, opts):
    """
        Runs a variety of analysis tools and compares functions found.
        Syntax: compare_funcs oid
        Options:
            file - specifies dumping to output file
            dir - specifies out directory to dump output files
            verbose - Includes breakdown of instuctions per tool
            color - Adds coloring to output to make easier to view
    """
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")
    valid = api.expand_oids(valid)

    # Set default output file for displaying output, file sends all output to one file
    out_dir = "data"
    if "dir" in opts:
        out_dir = opts["dir"]
    else:
        pipe = sys.stdout

    try:
        pipe = open(os.path.join(out_dir, opts['file']), "w")
    except KeyError:
        pipe = sys.stdout

    for oid in valid:
        fname = _name(oid)

        if "dir" in opts:
            # If out directory provided, open file in directory
            vlvl = ".verbose" if ('verbose' in opts and opts['verbose'] == 2) else ""
            pipe = open("{}{}.block_comparison.txt".format(fname, vlvl), "w")

        # Comparing all available tools
        tool_list = ['objdump', 'ghidra_disasm', 'ida_disasm']  # 'bap_bwoff'
        tool_list += ['fst_angr_disasm', 'emu_angr_disasm', '_disasm', 'bap_disasm']
        tool_list += ['pharos_disasm', 'ddisasm_disasm']
        tool_list += ['dwarf_functions']
        tool_list += ['functions']
        to_remove = []
        out_maps = {}

        for tool in tool_list:
            module_name = tool
            if tool == "functions":
                module_name = 'truth_store'
                options = {'type': 'functions'}
            else:
                options = {}

            out_map = api.retrieve(module_name, oid, options)
            if out_map is not None and out_map != {}:
                out_maps[tool] = out_map
            else:
                to_remove.append(tool)

        for tool in to_remove:
            if tool in tool_list:
                tool_list.remove(tool)

        print("Comparing {} ({}).\n".format(oid, fname), file=pipe)
        _function_comparison(fname, out_maps, tool_list, opts, pipe)


exports = [compare_insns, compare_blocks, compare_funcs, compare_radare, save_facts]


# ------------ Utilities -----------------

def _name(oid):
    if api.exists("file_meta", oid):
        return api.get_field("file_meta", oid, "names").pop()

    if api.exists("collections_meta", oid):
        return api.get_colname_from_oid(oid)
    return None


def _display_dasm(union_offsets, section_list, inst_maps, function_mapping, tool_list,
                  color: bool, show_sections: bool, pipe):
    """ union_offsets
        section_list
        inst_maps
        function_mapping
        tool_list
        color
        show_sections
        pipe
    """
    # Display toolnames
    _print_labels(tool_list, pipe)

    # for every possible instructon, determine if other tools have as well
    for offset in union_offsets:
        if offset == "meta":
            continue

        if show_sections:
            # Not great for performance, scales with number of sections
            # FIXME:: this should use enumerate
            i = 0
            for start, end, sec_name, flags in section_list:
                if start <= offset < end:
                    print(sec_name, flags, file=pipe)
                    del section_list[i]
                i += 1

        if offset in function_mapping:
            print(function_mapping[offset]['name'], file=pipe)

        print(spacing_str % offset, file=pipe, end="|")
        for tool_index in range(len(tool_list)):
            # Display spacing width of each instruction or spacing width of spaces
            if offset in inst_maps[tool_index]:
                format_len = min(len(inst_maps[tool_index][offset]), spacing - 1)
            empty = " " * (spacing)
            if color: empty = "\u001b[41;1m{}\u001b[0m".format(empty)
            print(spacing_str % inst_maps[tool_index][offset]['str'][0: format_len] if offset in inst_maps[tool_index] else empty, file=pipe, end=" |")
        print(file=pipe)


def _display_blocks(union_offsets, block_maps, function_mapping, tool_list, color: bool, v: int, pipe):
    """ Provide verbose printing for basic blocks
    """
    # for every possible instruction, determine if other tools have as well
    deactivate = False
    for offset in union_offsets:
        if offset == "meta":
            continue

        # Print function name if we have it
        if offset in function_mapping:
            print("{}".format(function_mapping[offset]), file=pipe)
            # Omit linker code
            LINKER_CODE = ['<_init>:', '<.plt>:', '<deregister_tm_clones>:', '<register_tm_clones>:', '<__do_global_dtors_aux>:',
                           '<frame_dummy>:', '<__libc_csu_init>:', '<__libc_csu_fini>:', '<_start>:', '<_fini>:']
            LINKER_CODE += ['<_dl_relocate_static_pie>:']
            if function_mapping[offset] in LINKER_CODE or '@plt' in function_mapping[offset]:
                print("\t<omitting due to linker code>", file=pipe)
                deactivate = True
            else:
                deactivate = False

        # Skip linker code and plt entries
        if deactivate is True:
            continue

        # Print offset
        print("\t{}:".format(offset), file=pipe)

        for tool_index in range(len(tool_list)):
            if offset in block_maps[tool_index] and 'members' in block_maps[tool_index][offset]:
                # set verbose level printing
                if v <= 1:
                    members = [x[0] for x in block_maps[tool_index][offset]['members']]
                else:
                    members = block_maps[tool_index][offset]['members']
                print("\t\t{0}[{length:2n}]: {1} -> {2} ".format(spacing_str % tool_list[tool_index],
                                                                 members,
                                                                 block_maps[tool_index][offset]['dests'],
                                                                 length=len(block_maps[tool_index][offset]['members'])),
                      file=pipe)
        print(file=pipe)
        print(file=pipe)


def _display_funcs(union_offsets, func_maps, tool_list, color: bool, pipe):
    # Display toolnames
    _print_labels(tool_list, pipe)

    # Defining empty string in case of key not present
    empty = " " * (spacing)
    if color: empty = "\u001b[41;1m{}\u001b[0m".format(empty)

    # for every possible instruction, determine if other tools have as well
    for offset in union_offsets:
        if offset in union_offsets:
            print(spacing_str % offset, file=pipe, end="|")
            for tool_index in range(len(tool_list)):
                # Display spacing width of each instruction or spacing width of spaces
                if offset in func_maps[tool_index]:
                    if isinstance(func_maps[tool_index][offset], str):
                        print("FIXME:: %s is using str as value" % tool_list[tool_index])
                        fun_name = func_maps[tool_index][offset]
                    elif "name" in func_maps[tool_index][offset]:
                        fun_name = func_maps[tool_index][offset]["name"]
                    else:
                        fun_name = "not_found"
                    format_len = min(len(fun_name), spacing - 1)
                    print(spacing_str % fun_name[0: format_len], file=pipe, end=" |")
                else:
                    print(empty, file=pipe, end=" |")
            print(file=pipe)


def _inst_comparison(sample: str, oid: str, disasm_maps: dict, function_mapping: dict,
                     tool_list: List[str], opts: dict, pipe: BinaryIO) -> None:
    # blocks located in out_maps
    inst_maps = []
    offsets_lists = []

    # Extract instruction store for each tool, renaming and using option for min/max_truth
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

    unique_matrix = _compute_distance_in_tools(offsets_lists, tool_list)

    # Display Matrix
    np.set_printoptions(precision=0)  # set fixed width
    print("Matrix of instructions found in both tool x and tool y", file=pipe)
    print("\t Read as Above has N instructions not found in Left", file=pipe)
    _print_labels(tool_list, pipe)
    tool_index = 0
    if len(unique_matrix) > 1:
        for tool_index in range(len(unique_matrix) - 1):
            _print_numpy_row(unique_matrix, tool_index, tool_list[tool_index], pipe)
        _print_numpy_row(unique_matrix, tool_index + 1, "Total", pipe)
    print("----------------------------------------------------------", file=pipe)

    if 'verbose' in opts:
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
        _display_dasm(union_offsets, section_list, inst_maps, function_mapping, tool_list,
                      color, 'sections' in opts, pipe)


def _block_comparison(sample, out_maps, function_mapping, tool_list, opts, pipe):
    # Create list of basic blocks for each tool
    blocks_list = []

    # order basic blocks for tools
    for tool in tool_list:
        blocks_list.append(out_maps[tool])

    s = (len(tool_list) + 1, len(tool_list))
    block_entry_diff = np.zeros(s, dtype=int)
    block_member_diff = np.zeros(s, dtype=int)
    block_tarbb_diff = np.zeros(s, dtype=int)
    block_tarct_diff = np.zeros(s, dtype=int)

    # Calculate Same instructions from Blocks X and Blocks Y
    for x_idx in range(len(tool_list)):
        for y_idx in range(len(tool_list)):
            # accumulators of total for difference in offsets, and equivalent members
            diff_blocks = 0
            same_members = 0
            total_dests_in_x = 0
            excluded = 0
            excluded_count = 0
            same_dests_block = 0
            same_dests_count = 0

            # Calculate difference in basic block offsets
            for i in blocks_list[x_idx].keys():
                if i not in blocks_list[y_idx].keys():
                    diff_blocks += 1

            # Calculate difference in block members
            for i in blocks_list[x_idx].keys():
                if blocks_list[x_idx][i] == {}:
                    # Emuangr sometimes produces empty basic blocks
                    excluded += 1
                    continue
                x_members = set([k for k in blocks_list[x_idx][i]["members"]])
                x_dests = set([k for k in blocks_list[x_idx][i]["dests"]])

                # accumulate total number of destinations used in tool x, wrong from duplicate??
                total_dests_in_x += len(x_dests)

                if i in blocks_list[y_idx].keys():
                    y_members = set([k for k in blocks_list[y_idx][i]["members"]])
                    if x_members == y_members:
                        same_members += 1

                    y_dests = set([k for k in blocks_list[y_idx][i]["dests"]])
                    dests_diff = len(x_dests - y_dests)

                    if dests_diff == 0:
                        same_dests_block += 1
                        same_dests_count += len(x_dests)
                    else:
                        same_dests_count += dests_diff

                else:
                    # Only count block differences, not start of block differences
                    excluded += 1
                    excluded_count += len(x_dests)

            # Populate Matrix with difference in block offsets, and differences in members
            block_entry_diff[y_idx, x_idx] = diff_blocks

            excluded_or_common = excluded + same_members
            block_member_diff[y_idx, x_idx] = len(blocks_list[x_idx].keys()) - excluded_or_common
            block_tarbb_diff[y_idx, x_idx] = len(blocks_list[x_idx].keys()) - excluded - same_dests_block
            block_tarct_diff[y_idx, x_idx] = total_dests_in_x - excluded_count - same_dests_count

        # Total Column: List the total number of basic blocks
        block_entry_diff[y_idx + 1, x_idx] = len(blocks_list[x_idx].keys())
        block_member_diff[y_idx + 1, x_idx] = len(blocks_list[x_idx].keys()) - excluded
        block_tarbb_diff[y_idx + 1, x_idx] = len(blocks_list[x_idx].keys()) - excluded
        block_tarct_diff[y_idx + 1, x_idx] = total_dests_in_x

    # Display Block Comparison Matrix
    if len(block_entry_diff) > 1:
        print("\t***Entry Comparison Matrix ***", file=pipe)
        _print_labels(tool_list, pipe)
        for tool_index in range(len(block_entry_diff) - 1):
            _print_numpy_row(block_entry_diff, tool_index, tool_list[tool_index], pipe)
        _print_numpy_row(block_entry_diff, tool_index + 1, "Total", pipe)

    # Display Block Member Comparison Matrix
    if len(block_member_diff) > 1:
        print("\t\t*** Member Comparison Matrix ***", file=pipe)
        _print_labels(tool_list, pipe)
        for tool_index in range(len(block_member_diff) - 1):
            _print_numpy_row(block_member_diff, tool_index, tool_list[tool_index], pipe)
        _print_numpy_row(block_member_diff, tool_index + 1, "Total", pipe)

    # Display Block Destination Comparison Matrix
    if len(block_tarbb_diff) > 1:
        print("\t\t*** Destination Blocks Comparison Matrix ***", file=pipe)
        _print_labels(tool_list, pipe)
        for tool_index in range(len(block_tarbb_diff) - 1):
            _print_numpy_row(block_tarbb_diff, tool_index, tool_list[tool_index], pipe)
        _print_numpy_row(block_tarbb_diff, tool_index + 1, "Total", pipe)

    # Display Block Destination Comparison Matrix
    if len(block_tarct_diff) > 1:
        print("\t\t*** All Destinations Comparison Matrix ***", file=pipe)
        _print_labels(tool_list, pipe)
        for tool_index in range(len(block_tarct_diff) - 1):
            _print_numpy_row(block_tarct_diff, tool_index, tool_list[tool_index], pipe)
        _print_numpy_row(block_tarct_diff, tool_index + 1, "Total", pipe)
    print(file=pipe)
    print(file=pipe)

    if 'verbose' in opts:
        # set default verbosity
        if opts['verbose'] not in [1, 2]:
            opts['verbose'] = 0
        else:
            opts['verbose'] = int(opts['verbose'])

        color = 'color' in opts
        union_offsets = set()

        for block_map in blocks_list:
            offset_set = set(block_map.keys())
            if 'meta' in offset_set:
                offset_set.remove('meta')
            union_offsets = union_offsets.union(offset_set)

        union_offsets = sorted(list(union_offsets))
        _display_blocks(union_offsets, blocks_list, function_mapping, tool_list, color, opts['verbose'], pipe)


def _function_comparison(sample, out_maps, tool_list, opts, pipe):
    func_maps = []
    offsets_lists = []
    to_remove = []
    for tool in tool_list:
        # Extract functions from output of each tool
        if 'functions' in out_maps[tool]:
            fun_map = out_maps[tool]['functions']
        else:
            to_remove.append(tool)
            continue

        # Remove meta key if present
        try:
            del fun_map['meta']
        except KeyError:
            pass

        # create list of items, and list of offsets with items for comparison
        offsets = [offset for offset in fun_map]

        func_maps.append(fun_map)
        offsets_lists.append(offsets)

    # Remove any tools that did not contain functions
    for tool in to_remove:
        if tool in tool_list:
            tool_list.remove(tool)

    union_offsets = set()
    for offset_list in offsets_lists:
        offset_set = set(offset_list)
        offset_set.discard(None)
        union_offsets = union_offsets.union(set(offset_set))
    union_offsets = sorted(list(union_offsets))

    # compute matrix
    s = (len(tool_list) + 1, len(tool_list))
    function_offset_diff = np.zeros(s, dtype=int)
    for offset in union_offsets:
        for x_idx in range(len(tool_list)):
            for y_idx in range(len(tool_list)):
                if offset in func_maps[x_idx] and offset not in func_maps[y_idx]:
                    function_offset_diff[y_idx][x_idx] += 1

            # Set total number of function row
            if offset in func_maps[x_idx]:
                function_offset_diff[y_idx + 1][x_idx] += 1

    # Display function Comparison Matrix
    if len(function_offset_diff) > 1:
        print("*** Function Offset Matrix ***", file=pipe)
        _print_labels(tool_list, pipe)
        for tool_index in range(len(function_offset_diff) - 1):
            _print_numpy_row(function_offset_diff, tool_index, tool_list[tool_index], pipe)
        _print_numpy_row(function_offset_diff, tool_index + 1, "Total", pipe)

    print(file=pipe)

    # Display verbose function differences
    if 'verbose' in opts:
        color = 'color' in opts
        _display_funcs(union_offsets, func_maps, tool_list, color, pipe)


def _compute_distance_in_tools(cfgs, tool_list):
    """ Get a set of lists of instruction tuples, compute difference in offsets
        Input -
            cfgs (list of lists of tuples) - A list of list of instruction tuples for each tool
                list of inst offsets from angr
                list of inst offsets from bap
            ... etc
        Output -
            unique_matrix (numpy matrix nxn) - matrix that stores difference in offset from n tool
    """
    # Create empty matrix of len n by n, where n is number of graphs
    s = (len(cfgs) + 1, len(cfgs))
    unique_matrix = np.zeros(s, dtype=int)

    # Calculate Same instructions from CFG_x and CFG_y
    for cfg_index1 in range(len(cfgs)):
        for cfg_index2 in range(len(cfgs)):
            # Computer Difference in sets of offsets
            unique_cfg1 = set(cfgs[cfg_index1]) - set(cfgs[cfg_index2])

            # Define x, y for matrix to show number of instructions that differ for tool_x and tool_y
            unique_matrix[cfg_index2, cfg_index1] = len(unique_cfg1)

    for cfg_index in range(len(cfgs)):
        unique_matrix[len(cfgs), cfg_index] = len(cfgs[cfg_index])

    return unique_matrix


def _print_labels(tools_list, pipe) -> None:
    """ Print labels for x axis of comparison matrix
        Input -
            tools_list (list of string) - list of tool names from inst_list files name
    """
    print(spacing_str % (" "), end="", file=pipe)
    for index in tools_list:
        print("| " + spacing_str % index, end="", file=pipe)
    print(file=pipe)


def _print_numpy_row(matrix, row_num: int, column_label: str, pipe) -> None:
    """ Numpy row, N by N where row_num is less than N
    """
    print(spacing_str % column_label, end="", file=pipe)
    for ele in matrix[row_num]:
        print("| " + spacing_str % (str(ele)), end='', file=pipe)
    print(file=pipe)
