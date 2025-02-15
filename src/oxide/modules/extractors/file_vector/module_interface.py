DESC = ""
NAME = "file_vector"
CATEGORY = ""

import logging

from typing import Dict, Any

from oxide.core import api

import networkx as nx
import numpy as np

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True, "category": CATEGORY}

def process(oid: str, opts: dict) -> bool:
    """
    Process the given object identifier (oid) to generate a feature vector for each function.
    
    The final feature vector for each function is the concatenation of:
      - The averaged basic block (node) features.
      - The graph-level features computed from the control flow graph (CFG).
    """
    logger.debug("process()")
    
    file_vector = generate_file_vector(oid)
    if not file_vector:
        return {}

    # Convert the dictionary values to a 1D NumPy array.
    result = np.array(list(file_vector.values())).flatten()

    api.store(NAME, oid, result, opts)
    return True


def generate_file_vector(oid):
    """ Extracts features for file-level and function-level matching. """
    results = {}

    funs = api.get_field("ghidra_disasm", oid, "functions")
    if funs:
        num_functions = len(funs)
        results["Num_Functions"] = num_functions

    bbs = api.retrieve("basic_blocks", oid)
    if bbs:
        results["Avg_bb"] = len(bbs)

    insns = api.get_field("ghidra_disasm", oid, "instructions")
    if insns:
        results["Num_instr"] = len(insns)

    fun_calls = api.retrieve("function_calls", oid)
    if fun_calls:
        results["Num_FC"] = len(fun_calls)

    return results