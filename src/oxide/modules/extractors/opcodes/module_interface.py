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

DESC = " Extract opcodes from a disassembly"
NAME = "opcodes"
USG = "This module extracts and returns the operation codes(opcodes) from a binary file if any otherwise returns the associated oid for the binary and \
a string that says none "

import logging
import api
logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"by_func": {"type":bool, "mangle":True,"default":False,"description":"Organize output by function"}}


def documentation():
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage": USG}


def process(oid, opts):
    logger.debug("process()")
    disasm = api.get_field("disassembly", [oid], oid)
    if disasm is None:
        return False

    if opts["by_func"]:
        f_dict = {}
        g_dis = api.retrieve("ghidra_disasm",oid)
        funcs = g_dis["functions"]
        dis = api.get_field("disassembly", oid,oid)['instructions']
        for f in funcs:
            if f == "meta": continue
            name = funcs[f]["name"]
            f_dict[name] = {}
            for b in funcs[f]["blocks"]:
                for i in g_dis["original_blocks"][b]["members"]:
                    addr = i[0]
                    if addr not in dis: continue
                    f_dict[name][addr] = dis[addr]["mnemonic"]
        api.store(NAME,oid,f_dict,opts)
        return True
    opcodes = get_opcodes(disasm["instructions"])
    api.store(NAME, oid, {"opcodes": opcodes}, opts)
    return True


def get_opcodes(insns):
    sequence = []
    offsets = list(insns.keys())
    offsets.sort()
    for offset in offsets:
        sequence.append(insns[offset]["mnemonic"])
    return sequence
