
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
    results = {}
    target_file = oid_list[0]
    target_func_insts = opts['target']
    target_func_insts = retrieve_function_instructions(target_file, target_func_insts)

    baseline_file = oid_list[1]
    baseline_func = opts['baseline']
    baseline_func_insts = retrieve_function_instructions(baseline_file, baseline_func)

    if target_func_insts and baseline_func_insts:
        added_instr, removed_instr, opcode_modifications, operand_modifications, basic_blocks, func_calls = diff_features(target_file, target_func_insts, target_func_insts, baseline_file, baseline_func, baseline_func_insts)
    else:
        added_instr = 0
        removed_instr = 0
        opcode_modifications = 0
        operand_modifications = 0
        basic_blocks = 0
        func_calls = 0

    results = {
        'added_instr': added_instr,
        'removed_instr': removed_instr,
        'modified_opcode_instr': opcode_modifications,
        'modified_operand_instr': operand_modifications,
        'basic_blocks': basic_blocks,
        'func_calls': func_calls
    }

    return results