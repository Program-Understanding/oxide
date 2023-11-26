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

""" IDAPro processing script for basic blocks, and instructions using script:ida_info_out.py
        Two versions of this script exist, with the update focused on 7.1+ with new api
        new api changes how to access addresses and instructions etc, WIP
        # TODO:: overlap both into one polished python script for IDA
"""

import subprocess
import os
import json
import time
import logging

canonical_mapping = {}

# ------------------------------- Tool: IDA -------------------------------------


def _ida_run_script(file_test: str) -> None:
    """ Execute tool to produce intermediate file for parsing (unknown how to parse stdout)
    """
    cmd = '%s -B -S"%s %s" %s' % (IDA_PATH, IDA_SCRIPT_PATH, IDA_TMP_FILE, file_test)
    # print("DEBUG", cmd)
    return subprocess.run(cmd, shell=True)


def _merge_members(members: list, members_to_add: list) -> list:
    final_list = members
    members_offsets = [i[0] for i in members]
    for x, _ in members_to_add:
        if x in members_offsets:
            continue
        else:
            final_list.append([x, "null"])
    return sorted(final_list)


def _add_block_to_save(line: str, header_interface, output_map: dict) -> None:
    """ Extract information from json format about basic block
    """
    array_index = line.index("[")
    bb_list = json.loads(line[array_index:])
    bb_offset = header_interface.get_offset(int(bb_list[0], 16))

    # IDAPro finds large address not mapped correctly by get_offset
    if bb_offset is None:
        return

    # Populate output map of offset with enteries from json output
    blocks = output_map["original_blocks"]

    # Handle case where duplicate block is found, similar to defaultdict usage
    new_block = False
    if bb_offset not in blocks:
        blocks[bb_offset] = {}
        new_block = True

    dests = []
    # using ida_info_out.py script, parse individual control flow for each instruction
    # Ida does not split on calls, but does record individual instruction destinations
    # These are recorded in ida_info_out.py and parsed here
    for x in bb_list[1]:
        offset_x = header_interface.get_offset(int(x, 16))
        canonical_mapping[offset_x] = []
        for y in bb_list[1][x]:
            if header_interface.get_offset(int(y, 16)) is not None:
                canonical_mapping[offset_x].append(header_interface.get_offset(int(y, 16)))
                dests.append(header_interface.get_offset(int(y, 16)))
            else:
                canonical_mapping[offset_x].append("EXTERNAL:%s" % y)
                dests.append("EXTERNAL:%s" % y)

    members = [[header_interface.get_offset(int(x, 16)), "null"] for x in bb_list[2]]

    # if second copy of block, merge instructions found within
    if new_block:
        blocks[bb_offset]["dests"] = dests
        blocks[bb_offset]["members"] = members
    else:
        blocks[bb_offset]["dests"] = sorted(set(blocks[bb_offset]["dests"] + dests), key=str)
        blocks[bb_offset]["members"] = _merge_members(blocks[bb_offset]["members"], members)

    blocks[bb_offset]["hex"] = hex(bb_offset)
    blocks[bb_offset]["rva"] = int(bb_list[0], 16)


def _add_function_to_save(line: str, header_interface, output_map: dict) -> None:
    """ Extract information from json format about function
    """
    # For each line of function found in ida_info_out.py, populate stored information
    json_index = line.index("[")
    fun_list = json.loads(line[json_index:])
    fun_offset = header_interface.get_offset(int(fun_list[0], 16))
    output_map["functions"][fun_offset] = {'name': fun_list[1], 'vaddr': int(fun_list[0], 16)}


def _populate_output_map(header_interface, output_map):
    try:
        ida_tmp_file = open(IDA_TMP_FILE, "r")
    except OSError:
        logging.error("Ida script output file not found, returning...")
        return

    out_lines = (ida_tmp_file.read()).split("\n")

    if len(out_lines) == 0:
        return

    for line in out_lines[1:]:
        # Parse file that is output from ida_info_out.py
        #   I - Instruction, B - Block, F - Function, INFO - debugging
        if len(line) < 1:
            continue
        if "RESULT_I" in line:
            array_index = line.index("[")
            inst_list = json.loads(line[array_index:])
            inst_addr = int(inst_list[0], 16)

            # get Offset through loaded address in IDAPro
            file_offset = header_interface.get_offset(inst_addr)

            if file_offset is not None:
                output_map["instructions"][file_offset] = inst_list[1]
            else:
                # offset not found in binary
                continue

        elif "RESULT_B" in line:
            _add_block_to_save(line, header_interface, output_map)
        elif "RESULT_F" in line:
            _add_function_to_save(line, header_interface, output_map)
        elif "INFO" in line:
            # Debug information
            logging.info(line)


def _clean_temporary_file():
    """ Remove intermediate file used to parse tool output
    """
    try:
        os.remove(IDA_TMP_FILE)
    except OSError:
        pass


def _update_blocks_with_insns(output_map):
    """ For each stubbed out basic block (addr, 'null'), populate with mnemonics
    """
    block_map = output_map["original_blocks"]
    # visit all basic blocks
    for bb in block_map:
        if bb == "meta":
            continue

        # traverse blocks members
        mems = output_map["original_blocks"][bb]["members"]
        for i in range(len(mems)):
            # update text of instruction in original blocks from instructions dictionary
            # don't assume block index exists in instructions
            if mems[i][0] in output_map["instructions"]:
                mems[i] = (mems[i][0], output_map["instructions"][mems[i][0]])

def extract(file_test, header_interface):
    """ Runs instruction extraction from idapro terminal interface using python language script
        Input -
            file_test (string) - Sample using bap.run() which runs analyses
            header_interface (header) - header object using header utiility lib
    """
    # Define Header interface
    output_map = {}
    output_map["meta"] = {}
    output_map["instructions"] = {}
    output_map["original_blocks"] = {}
    output_map["canon_blocks"] = {}
    output_map["functions"] = {}

    if not header_interface.known_format:
        logging.info("File Sample is of unknown format, IDA returning empty output.")
        return None

    start = time.time()
    _ida_run_script(file_test)
    end = time.time()

    _populate_output_map(header_interface, output_map)
    _clean_temporary_file()

    # Populate instruction
    _update_blocks_with_insns(output_map)

    output_map["meta"] = end - start

    if not output_map["instructions"]:
        return None
    return output_map
