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

DESC = "Return general file stats."
NAME = "file_stats"
USG = "This module returns a dictionary containing the statistics for each binary file in the collection by their individual oid. \
    The dictionary includes the number of basic blocks, the number of functions, the number of sections, whether or not the RTTI is present and if present, the \
    section names."

import hashlib
import operator
import logging

from typing import Dict, Any, List

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"disassembler": {"type": str, "mangle": False, "default": "ghidra_disasm"}}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "Usage": USG}


def results(oid_list: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    logger.debug("results()")

    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        res = {}
        names = api.get_field("file_meta", oid, "names")
        res["Names"] = ",".join(names)
        header = api.get_field("object_header", oid, oid)
        if header:
            res["Number of sections"] = len(header.section_info)
            section_names = [str(sec_name) for sec_name in header.section_info.keys()]
            res["Section names"] = ",".join(section_names)

        bbs = api.retrieve("basic_blocks", oid)
        if bbs:
            res["Number of basic blocks"] = len(bbs)

        insns = api.get_field("disassembly", oid, "instructions")
        if insns:
            res["Number of instructions"] = len(insns)

        funs = api.get_field("function_summary", oid, res["Names"])
        if funs:
            res["Number of functions"] = len(funs)
            res["Function names"] = ",".join(funs.keys())

        opcode_hist = api.retrieve("opcode_histogram", oid)
        if opcode_hist:
            opcodes_ordered = sorted(opcode_hist.items(), key=lambda kv: kv[1], reverse=True)
            # grab up to 10 opcodes
            opcodes_ordered = opcodes_ordered[: min(10, len(opcodes_ordered))]
            res["Top 10 opcodes"] = ",".join([opcode for opcode, frequency in opcodes_ordered])

        rtti = api.get_field("detect_rtti", oid, oid)
        res["RTTI Present"] = rtti
        results[oid] = res

    return results
