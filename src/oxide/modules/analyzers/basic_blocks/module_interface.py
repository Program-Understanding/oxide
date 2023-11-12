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

DESC = " Wrapper to access basic block analysis from extractors (ghidra, ida, angr)"
NAME = "basic_blocks"
USG = "This module returns a dictionary with the \
basic block analysis results for each binary file including the address of the first and last instruction as \
first_insn and last_insn, the total number of instructions as num_insns, a list of instruction mnemonics \
as members, potential destinations as dests and an optional hash value"

import hashlib
import logging

from oxide.core import api

from typing import List, Any, Dict


logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"disassembler": {"type": str, "mangle": False, "default": "ghidra_disasm"}}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "Usage": USG}


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    logger.debug("results()")

    disassembler = opts["disassembler"]
    disassemblers = api.get_available_modules("disassembler")
    if disassembler not in disassemblers:
        logger.info("Invalid option `%s` for disassembler, options are %s", disassembler,
                                                                            disassemblers)

    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        blocks = None
        if not disassembler or disassembler == "ghidra_disasm":
           blocks = api.get_field("ghidra_disasm", oid, "original_blocks", opts)
        elif disassembler == "probablistic_disasm":
            # TODO: switch this to default disassembler
            blocks = api.get_field("probablistic_disasm", oid, "original_blocks", opts)
        elif disassembler in disassemblers:
            blocks = api.get_field(disassembler, oid, "original_blocks", opts)
        else:
            # invalid disassembler option
            blocks = None

        if not blocks:
            continue

        results[oid] = build_basic_blocks(blocks)

    return results


def build_basic_blocks(blocks: dict) -> dict:
    bbs = {}
    for i in blocks:
        if i == "meta": continue
        if blocks[i]['members'] == []:
            logger.debug('Dropping block %s because no memebers %s', i, blocks[i])
            continue
        bb_info = {}
        bb_info["first_insn"] = i
        bb_info["last_insn"] = blocks[i]['members'][-1]
        bb_info["num_insns"] = len(blocks[i]['members'])
        bb_info["members"] = [j for j in blocks[i]['members']]
        bb_info["dests"] = blocks[i]['dests']
        # h = hashlib.new("sha1")
        # long_str = "".join([j[1] for j in blocks[i]['members']])
        # h.update(long_str.encode())
        # bb_info["hash"] = h.digest()
        bbs[i] = bb_info
    return bbs
