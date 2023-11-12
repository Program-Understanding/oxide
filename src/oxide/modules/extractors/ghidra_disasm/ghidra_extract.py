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

""" Wrapper for scripts for Ghidra to extract basic block and
    instructions
"""

import os
import subprocess
import json
import logging
import time

from typing import Optional, Tuple

from oxide.core.libraries.ghidra_utils import get_file_offset

NAME = "ghidra_disasm"
logger = logging.getLogger(NAME)

LOAD_ADDR = 0

# --------------------------- Tool 5: Ghidra -----------------------------------------


"""
    Persistent bugs:
        Ghidra 9.2.2 produces address "1000:0000" while 9.0.2 "004000000"
"""


def extract_ghidra_disasm(file_test: str) -> Optional[str]:
    cmd = "{} {} {} ".format(GHIDRA_PATH, GHIDRA_Project_PATH, GHIDRA_Project_NAME) + \
          "-import {} -overwrite -scriptPath {} ".format(file_test, SCRIPTS_PATH)   + \
          "-postScript {} | grep RESULT".format(EXTRACT_SCRIPT)
    logger.info("cmd: %s", cmd)
    output = None
    with open(os.devnull, "w") as null:
        try:
            output = subprocess.check_output(cmd, universal_newlines=True, shell=True, stderr=null)
        except subprocess.CalledProcessError as e:
            logger.warning(e.output)
    return output


def _populate_insns_map(ghidra_inst_ref: list, header_interface, output_map: dict) -> None:
    if len(ghidra_inst_ref) == 0:
        logger.info("No instructions found in Ghidra.")
        return

    for line in ghidra_inst_ref:
        if len(line) < 1:
            continue

        try:
            inst_list = json.loads(line)
            # TODO:: check instruction format len of json
            inst_offset = get_file_offset(int(inst_list[0], 16), header_interface, LOAD_ADDR, OFFSETS_OFF)
        except ValueError:
            logger.warning("Instruction address is not valid %s", inst_list[0])
            output_map["instructions"] = {}  # reset dictionary
            return
        output_map["instructions"][inst_offset] = inst_list[1]


def _populate_block_map(ghidra_block_ref: list, header_interface, output_map: dict) -> None:
    if len(ghidra_block_ref) == 0:
        logger.info("No basic blocks found in Ghidra extracted information.")
        return

    for line in ghidra_block_ref:
        if len(line) < 1:
            continue

        bb_list = json.loads(line)
        bb_offset = get_file_offset(int(bb_list[0], 16), header_interface, LOAD_ADDR, OFFSETS_OFF)
        output_map["original_blocks"][bb_offset] = {}

        dests = []
        for x in bb_list[1]:
            try:
                dest_offset = get_file_offset(int(x, 16), header_interface, LOAD_ADDR, OFFSETS_OFF)
                if dest_offset:
                    dests.append(dest_offset)
                else:
                    dests.append('EXTERNAL:%s' % int(x, 16))
            except ValueError:
                dests.append(x)

        output_map["original_blocks"][bb_offset]["dests"] = sorted(dests, key=str)

        members = [(get_file_offset(int(x, 16), header_interface, LOAD_ADDR, OFFSETS_OFF), "null") for x in bb_list[2]]
        output_map["original_blocks"][bb_offset]["members"] = members


def _populate_function_map(ghidra_function_ref: list, header_interface, output_map: dict) -> None:
    if len(ghidra_function_ref) == 0:
        logger.info("No functions found in Ghidra extracted information.")
        return

    for line in ghidra_function_ref:
        # Omit null line
        if len(line) < 1:
            continue

        try:
            bb_list = json.loads(line)
            fun_offset = -1
            fun_offset = get_file_offset(int(bb_list['vaddr'], 16), header_interface, LOAD_ADDR, OFFSETS_OFF)
            output_map["functions"][fun_offset] = bb_list
            output_map["functions"][fun_offset]["blocks"] = [get_file_offset(x, header_interface, LOAD_ADDR, OFFSETS_OFF) for x in bb_list["blocks"]]
        except json.decoder.JSONDecodeError:
            # skip boiler plate messages
            continue


def _update_blocks_with_insns(output_map: dict) -> None:
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
                # for canonical representation must lower case instructions
                # Replace tuple value with updated second key
                mems[i] = (mems[i][0], output_map["instructions"][mems[i][0]].lower())


def _sort_lines(extract_lines: str) -> Tuple[list, list, list]:
    global LOAD_ADDR
    ghidra_inst_ref = []
    ghidra_block_ref = []
    ghidra_function_ref = []

    for line in extract_lines.split('\n'):
        try:
            space_index = line.index(' ')
            json.loads(line[space_index + 1:])
        except ValueError:
            continue
        except json.decoder.JSONDecodeError:
            logger.error("json decoding error %s", line[space_index + 1:])
            # ensure line can be decoded
            continue

        if len(line) > 6 and line[0:7] == "RESULTM":
            # meta information such as load address
            try:
                LOAD_ADDR = int(json.loads(line[space_index + 1:])[0], 16)  # load address in singleton list
            except ValueError:
                logger.info("invalid casting of address to int, possible Ghidra version issue")
                # Exception handling related to Ghidra 9.2.1+ (addr 1000:0000)
                break
        if len(line) > 6 and line[0:7] == "RESULTI":
            ghidra_inst_ref.append(line[space_index + 1:])
        elif len(line) > 6 and line[0:7] == "RESULTB":
            ghidra_block_ref.append(line[space_index + 1:])
        elif len(line) > 6 and line[0:7] == "RESULTF":
            ghidra_function_ref.append(line[space_index + 1:])
        else:
            logger.debug("Line is not instruction, block, or function - %s", line)

    return LOAD_ADDR, ghidra_inst_ref, ghidra_block_ref, ghidra_function_ref


def extract(file_test: str, header) -> dict:
    """ Runs instruction extraction from ghidraHEADLESS using a java language
        script.

        Input -
            file_test (file) - Sample using bap.run() which runs analyses
            header_interface (header) - header object using header utiility lib

        Returns -
            output_map (dict) - dictionary containing facts extracted from tool
    """
    output_map = {}
    output_map["meta"] = {}
    output_map["instructions"] = {}
    output_map["original_blocks"] = {}
    output_map["canon_blocks"] = {}
    output_map["functions"] = {}

    if not header.known_format:
        logger.warning("File Sample unknown format, Ghidra returning empty. (%s)", file_test)
        return None

    start = time.time()
    extract_script_dump = extract_ghidra_disasm(file_test)
    end = time.time()

    if not extract_script_dump:
        logger.warning("Ghidra extract script returned an error")
        return None

    load_addr, ghidra_inst_ref, ghidra_block_ref, ghidra_function_ref = _sort_lines(extract_script_dump)

    output_map["meta"]["time"] = end - start
    output_map["meta"]["load_addr"] = load_addr

    if len(ghidra_inst_ref) > 0:
        _populate_insns_map(ghidra_inst_ref, header, output_map)
    if len(ghidra_block_ref) > 0 and output_map["instructions"] != {}:
        _populate_block_map(ghidra_block_ref, header, output_map)
    if len(ghidra_function_ref) > 0 and output_map["instructions"] != {}:
        _populate_function_map(ghidra_function_ref, header, output_map)

    if (0 == len(ghidra_inst_ref)) and (0 == len(ghidra_block_ref)) and (0 == len(ghidra_function_ref)):
        logger.warning("Ghidra found no instructions, basic blocks, and functions")
        return None

    # Populate Instruction
    _update_blocks_with_insns(output_map)

    return output_map
