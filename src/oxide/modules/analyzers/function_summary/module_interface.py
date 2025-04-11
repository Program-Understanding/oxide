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

DESC = " Extract basic function info."
NAME = "function_summary"
USG = "This module returns a dictionary containing the function summary for each file which includes the name of the function, \
    the offset of the function within the file and the function signature which provides details about the function's return type, \
    calling convention and parameters."

import logging

from typing import Dict, Any, List

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": {}, "set": True,
            "atomic": True, "Usage": USG}


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    logger.debug("results()")

    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        names = api.get_field("file_meta", oid, "names")
        names = ",".join(names)
        f_dict = {}
        ghidra_dis = api.retrieve("ghidra_disasm", oid)
        complexity = api.retrieve("cyclo_complexity", oid)
        disassembly = api.get_field("disassembly", oid, oid)['instructions']
        if "functions" in ghidra_dis:
            funs = ghidra_dis["functions"]
        else: funs = None
        if not funs: continue
        for f in funs:
            if f == 'meta': continue
            num_insns = 0
            operands = {"imm":0, "reg":0, "mem":0}
            for b in funs[f]['blocks']:
                num_insns += len(ghidra_dis["original_blocks"][b]['members'])
                for i in ghidra_dis["original_blocks"][b]['members']:
                    addr = i[0]
                    if not addr in disassembly:
                        continue
                    for op in disassembly[addr]["operands"]:
                        op_info = disassembly[addr]["operands"][op]
                        if "type.imm" in op_info:
                            operands["imm"] += 1
                        if "type.reg" in op_info:
                            operands["reg"] += 1
                        if "type.mem" in op_info:
                            operands["mem"] += 1
            if num_insns == 0:
                continue
            f_dict[funs[f]['name']] = {'offset':f,
                'signature':funs[f]['signature']}
            f_dict[funs[f]['name']]["num_insns"] = num_insns
            if f in complexity:
                f_dict[funs[f]['name']]["complexity"] = complexity[f]["complexity"]
                f_dict[funs[f]['name']]["complexity_desc"] = complexity[f]["desc"]
            else:
                f_dict[funs[f]['name']]["complexity"] = None
                f_dict[funs[f]['name']]["complexity_desc"] = None
            # f_dict[funs[f]['name']]["operands"] = operands
            # f_dict[funs[f]['name']]["params"] = funs[f]["params"]
        results[oid] = f_dict

    return results
