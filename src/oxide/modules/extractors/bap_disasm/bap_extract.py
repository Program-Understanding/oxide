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

""" BAP processing script for basic blocks, and instructions

"""

import logging
import time

logger = logging.getLogger('bap-extract')

# Python bindings may not be installed
import bap
try:
    bap.run('test-install')
except FileNotFoundError:
    logger.debug('bap not found in environment. Please install bap')
    raise ImportError
except bap.bap.Failed:
    # This file doesn't need to exist, only checking if bap could run
    pass


# ------------------------------- Tool 4: BAP -------------------------------------


def _add_block_to_save(bb, header_interface, block_map):
    """ populate basic block map, with members, and destinations (as Tid for now)

    Args:
        header_interface
        block_map (dict): Original basic blocks in output_map
    """
    # store offset of basic block in first field
    bb_addr = header_interface.get_offset(int(bb.attrs.elements["address"], 16))

    # Support duplicate basic blocks
    if bb_addr not in block_map:
        block_map[bb_addr] = {}

    # Instruction sucessors, intrerpret jumps field of basic block
    # Find instructions with control flow from jumps table
    destination_block_ids = []
    for goto_stmts in bb.jmps.elements:
        dests = goto_stmts.target
        if not isinstance(dests, tuple):
            dest = dests.arg
            if isinstance(dest, bap.bir.Tid):
                destination_block_ids.append(dest.number)
        else:
            for elem in dests:
                dest = elem.arg
                if isinstance(dest, bap.bir.Tid):
                    destination_block_ids.append(dest.number)

    if "dests" not in block_map[bb_addr]:
        # First time seeing basic block
        block_map[bb_addr]["dests"] = destination_block_ids
    else:
        # Duplicate basic block, unioning destinations
        block_map[bb_addr]["dests"] = list(set(block_map[bb_addr]["dests"] + destination_block_ids))

    if "members" not in block_map[bb_addr]:
        members = []
    else:
        members = block_map[bb_addr]["members"]

    # Get instruction Definitions, only add instruction offset+opcode if not in list
    for inst_def in bb.defs.elements:
        insn_offset = header_interface.get_offset(int(inst_def.attrs.elements["address"], 16))
        insn_body = inst_def.attrs.elements["insn"]

        insn_in_members = [item for item in members if item[0] == insn_offset]

        # existing members did not have current instruction
        if not insn_in_members:
            members.append((insn_offset, insn_body))

    # FIXME: Check if destination are different, not just offset, Get branch Defition,
    # only add if not in current member list
    for inst_goto in bb.jmps.elements:
        if "address" in inst_goto.attrs.elements:
            jump_offset = header_interface.get_offset(int(inst_goto.attrs.elements["address"], 16))
            jump_body = inst_goto.attrs.elements["insn"]

            jmp_insn_in_members = [item for item in members if item[0] == jump_offset]

            if not jmp_insn_in_members:
                members.append((jump_offset, jump_body))

    if len(members) == 0:
        pass
        # FIXME: Debug these goto only blocks, maybe NOPs
        # print(bb)

    block_map[bb_addr]["members"] = sorted(members)


def _process_subroutines(proj, header_interface, output_map):
    """
    Args:
        proj (bap.project): project with basic blocks and instructions
        header_interface (header): interface to oxide header processing
        output_map (dictionary): Output reference
    """
    # Structure to resolve tid to offset, used in preceeding blocks and destinations
    block_tid_map = {}

    # scan all found subroutines
    for routine in proj.program.subs.elements:
        # fetch each basic block from these
        for bb in routine.blks:
            # For non-NULL basic blocks,
            # FIXME::update logic for more robust, our jump table may need plugin
            if "address" not in bb.attrs.elements:
                continue

            bb_addr = bb.attrs.elements["address"]

            n_members = len(bb.defs.elements) + len(bb.jmps.elements)
            if n_members == 0:
                continue

            _add_block_to_save(bb, header_interface, output_map["original_blocks"])

            # Map tid number to a vaddr, block id is stored as number field
            # in first element in tuple.
            block_tid_map[bb.arg[0].number] = bb_addr

            # Get instruction Definitions
            for inst_def in bb.defs.elements:
                inst_addr = int(inst_def.attrs.elements["address"], 16)
                inst_offset = header_interface.get_offset(inst_addr)
                output_map["instructions"][inst_offset] = inst_def.attrs.elements["insn"]

            # Get branch Defition
            for inst_goto in bb.jmps.elements:
                if "address" in inst_goto.attrs.elements:
                    jump_addr = int(inst_goto.attrs.elements["address"], 16)
                    jump_offset = header_interface.get_offset(jump_addr)
                    output_map["instructions"][jump_offset] = inst_goto.attrs.elements["insn"]

    # Update basic blocks from tid to offset
    for blk_key in output_map["original_blocks"]:
        if blk_key == "meta":
            continue

        # iterate over destinations and update Tid to actual address
        blk = output_map["original_blocks"][blk_key]
        for tgt_idx in range(len(blk["dests"])):
            # Potential for BAP to just not find basic block instead of external?
            if blk["dests"][tgt_idx] in block_tid_map:
                blk["dests"][tgt_idx] = header_interface.get_offset(int(block_tid_map[blk["dests"][tgt_idx]], 16))
            else:
                blk["dests"][tgt_idx] = "External:%d" % blk["dests"][tgt_idx]


def extract(file_test, header, bw_off=None):
    """ Computes BAP disassembly of a sample file
        Input -
            file_test (string) - Sample name to be plugged in using bap.run() for analysis
            header_interface (header) - header object using header utiility lib
    """
    output_map = {}
    output_map["meta"] = {}
    output_map["instructions"] = {}
    output_map["original_blocks"] = {}
    output_map["canon_blocks"] = {}

    if not header.known_format:
        logging.info("File Sample is of unknown format, BAP returning empty output.")
        return None

    start = time.time()

    # Initialize BAP Project, check if byteweight off is defined in kwargs
    # FIXME:: Bap if not installed will cause bap-server to hang, may need to specify timeout
    if "bw_off" in vars() and bw_off is True:
        proj = bap.run(file_test, ["--rooter=internal"])
        logging.debug("Byteweight off, debugging odd basic blocks with no destination")
    else:
        proj = bap.run(file_test)
        logging.debug("Byteweight on, standard behavior")

    end = time.time()

    _process_subroutines(proj, header, output_map)

    output_map["meta"]["time"] = end - start

    return output_map
