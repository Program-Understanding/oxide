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

DESC = " This module is a template for analyzer, new analyzers can copy this format"
NAME = "function_unified_diff"

# imports
import logging
from difflib import SequenceMatcher, unified_diff
from typing import Dict, Any, List

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"function": {"type": str, "mangle": True, "default": "None"},
            "baseline_function": {"type": str, "mangle": True, "default": "None"}
}


def documentation() -> Dict[str, Any]:
    """ Documentation for this module
        private - Whether module shows up in help
        set - Whether this module accepts collections
        atomic - TBD
    """
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True}


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    """ Entry point for analyzers, these do not store in database
        these are meant to be very quickly computed things passed along
        into other modules
    """
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    results = {}
    oid = oid_list[0]
    func = opts['function']
    func_insts = retrieve_function_instructions(oid, func)

    baseline_oid = oid_list[1]
    baseline_func = opts['baseline_function']
    baseline_func_insts = retrieve_function_instructions(baseline_oid, baseline_func)
    
    if func_insts and baseline_func_insts:
        max_context = max(len(baseline_func_insts), len(func_insts))
        u_diff = unified_diff(baseline_func_insts, func_insts, n=max_context)
    else:
        u_diff = None
    
    unified_diff_result = []
    if u_diff:
        for line in u_diff:
            unified_diff_result.append(line)

    results = {
        'unified_diff': unified_diff_result
    }
    return results

def retrieve_function_instructions(file, func):
    """
    Retrieve function instructions for a specific function by its name.
    """
    function_data = api.retrieve('function_representations', file, {'lift_addrs': True})
    for func_id, details in function_data.items():
        if details.get('name') == func:
            return details.get('modified_fun_instructions', None)
    return None
