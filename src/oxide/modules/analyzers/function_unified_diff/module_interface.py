DESC = " This module is a template for analyzer, new analyzers can copy this format"
NAME = "function_unified_diff"

# imports
import logging
from difflib import SequenceMatcher, unified_diff
from typing import Dict, Any, List

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"target": {"type": int, "mangle": True, "default": "None"},
            "baseline": {"type": int, "mangle": True, "default": "None"}
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
    target_oid = oid_list[0]
    target_func = opts['target']
    target_func_insts = retrieve_function_instructions(target_oid, target_func)

    baseline_oid = oid_list[1]
    baseline_func = opts['baseline']
    baseline_func_insts = retrieve_function_instructions(baseline_oid, baseline_func)
    
    if target_func_insts and baseline_func_insts:
        max_context = max(len(baseline_func_insts), len(target_func_insts))
        u_diff = unified_diff(baseline_func_insts, target_func_insts, n=max_context)
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
    if func in function_data:
        return function_data[int(func)].get('modified_fun_instructions', None)
    return None
