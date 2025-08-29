
DESC = ""
NAME = "function_diff_features"

# imports
import logging
from typing import Dict, Any, List

from oxide.core import api
from utils import retrieve_function_instructions, diff_features

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"target": {"type": str, "mangle": True, "default": "None"},
            "baseline": {"type": str, "mangle": True, "default": "None"}
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
    target_file = oid_list[0]
    target_func = opts['target']
    target_func_insts = retrieve_function_instructions(target_file, target_func)

    baseline_file = oid_list[1]
    baseline_func = opts['baseline']
    baseline_func_insts = retrieve_function_instructions(baseline_file, baseline_func)

    diff = api.retrieve("bindiff", [target_file, baseline_file]) or {}

    if target_func_insts and baseline_func_insts:
        return diff_features(diff, target_file, target_func, target_func_insts, baseline_file, baseline_func, baseline_func_insts)
    else:
        return None