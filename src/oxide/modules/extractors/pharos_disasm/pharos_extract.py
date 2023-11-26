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

""" Pharos processing script for basic blocks, and instructions
"""

import subprocess
import os
from typing import Optional
import time
import logging

name = "pharos_extract"
logger = logging.getLogger(name)

# ------------------------------- Tool: Pharos/Rose -------------------------------------


def test_docker():
    # Test if pharos is configured and installed
    cmd = "docker"
    with open(os.devnull, "w") as null:
        subprocess.check_output(cmd, universal_newlines=True, shell=True, stderr=null)


def test_module(scratch_dir, pharos_image):
    # Test if pharos is configured and installed
    cmd = "docker run -v {}:/dir --rm {} dumpmasm".format(scratch_dir, pharos_image)
    with open(os.devnull, "w") as null:
        subprocess.check_output(cmd, universal_newlines=True, shell=True, stderr=null)


def extract_pharos_disasm(file_name: str, header_interface, scratch_dir: str) -> str:
    """ Executes docker image for pharos to dump output
        Parameters -
            file_name (str): program under test
            header_interface (header): header providing access to whether 64 bit
    """
    file_base_name = os.path.basename(file_name)

    flags = ""
    if header_interface.is_64bit():
        # if input is 64 bit, must toggle optional mode
        flags += "--allow-64bit"

    # FIXME:: replace api call with passed in from module_interface
    cmd = "docker run -v {}:/dir --rm {} dumpmasm dir/{} {}".format(scratch_dir,
                                                                    PHAROS_IMAGE,
                                                                    file_base_name,
                                                                    flags)

    logger.debug(cmd)
    with open(os.devnull, "w") as null:
        return subprocess.check_output(cmd, universal_newlines=True, shell=True, stderr=null)


def _process_pharos_results(pharos_results: str, header_interface) -> (list, list, list):
    """ From serial output from pharos docker image, parse into instructions and flows
        update instructions output. Cannot use Json as hex digits.

        Expected Format -
            "PART",0x000002B4,"DATA",0x00000000,"00000000","db","???"
            "PART",0x0000063B,"INSN",0x00000630,"4885C0","test","rax, rax"
            "FLOW",0x00000630,0x00000634,"FALLTHRU"
            OPTI[INFO ]: Dumpmasm completed successfully.

        Parameters -
            pharos_result (str): raw output from tool
            header_interface (header): binary header giving access to 64 bit and object format
            output_map (dict): dictionary to store instructions and basic blocks
    """
    # TODO:: canonicalize blocks, as tool intentionally does not do this
    # Pharos keeps instruction level graph, we can simplify this to blocks
    # print(pharos_results)
    data = []
    instr = []
    edges = []

    for line in pharos_results.split("\n"):
        # If logging message, omit and pass logging messages through
        if len(line) > 4 and line[0:4] == "OPTI":
            logger.debug(line)
            continue

        elements = line.split(",")
        if len(elements) > 2 and elements[2] == '"DATA"':
            # Skipping data for now
            data.append(elements)
        elif len(elements) > 2 and elements[2] == '"INSN"':
            # PART
            offset = header_interface.get_offset(int(elements[1], 16))
            function = header_interface.get_offset(int(elements[3], 16))
            # TODO:: how is prefixes handled, 5 is mnemonic, 6 is args
            # Omit " from output
            body = "{}".format(' '.join(elements[5:])).replace('"', '')
            instr.append((offset, function, body))
            logger.debug("%s %s %s", function, offset, body)
        elif len(elements) > 1 and elements[0] == '"FLOW"':
            src = header_interface.get_offset(int(elements[1], 16))
            try:
                dst = header_interface.get_offset(int(elements[2], 16))
            except ValueError:
                # Unresolved indirect jump, possibly external calls as well
                dst = "{}".format(elements[2])
            edge_type = elements[3]
            logger.debug("%s %s %s", src, dst, edge_type)
            edges.append((src, dst, edge_type))
        else:
            logger.debug("Unhandled type, {}".format(line))

    return instr, edges, data


def _record_instr(output_map: dict, instr: list) -> None:
    for offset, function, body in instr:
        output_map["instructions"][offset] = body


def _record_blocks(output_map: dict, instr_records: list, edges: list) -> None:
    instr_offsets = [insn[0] for insn in instr_records]
    begins = set()
    ends = set()
    edge_map = {}

    # Annotate instructions that start and end basic blocks
    for src, dst, edge_type in edges:
        # instruction in src ends a basic block
        # instruction targetted by dst begins a basic block
        ends.add(src)
        begins.add(dst)

        # expect source to be non-unique 1:N
        if src not in edge_map:
            edge_map[src] = [dst]
        else:
            edge_map[src].append(dst)

        # add beginning following a branch
        try:
            insn_index = instr_offsets.index(dst)
        except ValueError:
            continue
        begins.add(instr_offsets[insn_index])

        # Do not need to find implicit control flow, as explicit in structure of fallthrough

    # add offset of first instruction into begin set
    begins.add(instr_records[0][0])

    blocks = {}
    members = []
    for offset, _, _ in instr_records:
        # ASSUMPTION: insn are in sequential order, can sort if needed
        if offset in begins:
            blocks[offset] = {}
            current_block = offset

        members.append((offset, "null"))

        if offset in ends:
            blocks[current_block]["dests"] = edge_map[offset]
            blocks[current_block]["members"] = members
            members = []

    output_map["original_blocks"] = blocks


def _record_data(output_map: dict, data: list) -> None:
    pass


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
                mems[i] = (mems[i][0], output_map["instructions"][mems[i][0]].lower())


def extract(file_test: str, header_interface, scratch_dir: str) -> Optional[dict]:
    """ Runs instruction extraction from pharos docker image using python language script
        Input -
            file_test (string) - Sample using bap.run() which runs analyses
            header_interface (header) - header object using header utiility lib
    """
    # Define Header interface
    output_map = {}
    # timing, oxide version, and tool version
    output_map["meta"] = {}
    output_map["instructions"] = {}
    output_map["original_blocks"] = {}
    output_map["canon_blocks"] = {}

    if not header_interface.known_format:
        logging.info("File Sample is of unknown format, Pharos returning empty output.")
        return None

    if header_interface.type == "MACHO":
        # Mach-O not supported as of 4-6-21
        logging.info("File Sample is of Mach-O format, Pharos returning empty output.")
        return None

    start = time.time()

    try:
        pharos_results = extract_pharos_disasm(file_test, header_interface, scratch_dir)
    except subprocess.CalledProcessError:
        logging.error("Pharos encountered error on binary, likely disassmbler for arch")
        return None
    end = time.time()

    output_map["meta"]["time"] = end - start

    instr, edges, data = _process_pharos_results(pharos_results, header_interface)

    _record_instr(output_map, instr)
    # Instruction level CFG
    _record_blocks(output_map, instr, edges)
    _record_data(output_map, data)

    _update_blocks_with_insns(output_map)

    return output_map
