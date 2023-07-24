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
USG = "This module takes a list of collection with list of OID's for each binary file or a single OID pertaining to a binary file and performs \
analysis on them which returns a dictionary containing the function summary for each binary file which includes the name of the function, \
The offset of the function within the binary file and the function signature which provides details about the functions return type, \
calling convention and parameters. The dictionary keys are the names of binary files"

import logging

from typing import Dict, Any, List

from core import api

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
        funs = api.get_field("ghidra_disasm", oid, "functions")
        if not funs: continue
        for f in funs:
            if f == 'meta': continue
            f_dict[funs[f]['name']] = {'offset':f,
                'signature':funs[f]['signature']}
        results[names] = f_dict
    return results
