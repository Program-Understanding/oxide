DESC = "This module builds a map of each function's outgoing call targets"
NAME = "function_call_targets"
CATEGORY = ""  # used for filtering of modules e.g. disassemblers like ida

import logging

from typing import Dict, Any

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"version": {"type": int, "mangle": True, "default": -1}}

def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True, "category": CATEGORY}

def process(oid: str, opts: dict) -> bool:
    logger.debug("process()")

    functions = api.get_field("ghidra_disasm", oid, "functions")
    basic_blocks = api.get_field("ghidra_disasm", oid, "original_blocks")

    if functions is None or basic_blocks is None:
        return None
    else:
        result = calls_to(functions, basic_blocks)

    api.store(NAME, oid, result, opts)
    return result


def calls_to(functions, basic_blocks):
    # Build a map from each basic‐block address to its parent function
    block2func = {}
    for func_addr, fdata in functions.items():
        # get the list of blocks for this function (empty list if missing)
        blocks = fdata.get("blocks", [])
        for bb in blocks:
            block2func[bb] = func_addr


    result = {}
    for func_addr, fdata in functions.items():
        targets = set()
        for bb in fdata.get("blocks", []):
            bbinfo = basic_blocks.get(bb, {})
            for dest in bbinfo.get("dests", []):
                callee_func = block2func.get(dest)
                # if it lands in a *different* function, record it
                if callee_func and callee_func != func_addr:
                    targets.add(callee_func)

        # sort or listify as you prefer
        result[func_addr] = sorted(targets)
    return result

