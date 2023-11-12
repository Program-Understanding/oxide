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

DESC = " Extract fuzzy hashes of each function from a disassembly"
NAME = "function_hashes"
USG = "This module takes a collection of binary files and analyzes them. It processes each binary and extracts fuzzy hashes and lengths of \
the individual functions found in the binaries. The module then returns a dictionary containing the function names as keys and their \
corresponding fuzzy hashes and lengths as values."

import logging
import hashlib
from oxide.core import api
logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

def documentation():
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage": USG}

def process(oid, opts):
    f_dict = {}
    names = api.get_field("file_meta", oid, "names")
    logger.debug("process(%s)", names)

    # Get functions, basic blocks, and disassembly
    funs = api.get_field("ghidra_disasm", oid, "functions")
    if not funs: return False
    bbs = api.get_field("ghidra_disasm", oid, "original_blocks")
    insns = api.get_field("disassembly", oid, oid)
    if insns and "instructions" in insns:
        insns = insns["instructions"]
    else:
        return False

    range = sorted(insns.keys())
    logger.info("Instruction range: %d - %d", range[0], range[-1])

    for f in funs:
        if f == 'meta': continue
        blocks = funs[f]['blocks']
        f_string = ""
        f_info = {}
        f_len = 0
        f_icount = 0
        for b in blocks:
            if b not in bbs: continue
            f_icount += len(bbs[b]['members'])
            for insn_offset, insn_text in bbs[b]['members']:
                if insn_offset not in insns.keys():
                    logger.error("Basic Block member not found: %s", insn_offset)
                    continue
                f_len += insns[insn_offset]['size']
                opcode = insn_text.split(' ')
                if opcode:
                    opcode = opcode[0]
                    f_string += opcode

        if f_icount > 5:  # Eliminate functions that are just jumping to external
            f_info["hash"] = hashlib.sha1(f_string.encode()).hexdigest()
        else:
            f_info["hash"] = None

        f_info["len"] = f_len
        f_dict[funs[f]['name']] = f_info
    logger.debug("Storing")
    api.store(NAME, oid, f_dict, opts)
    return True
