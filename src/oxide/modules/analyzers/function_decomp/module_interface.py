DESC = ""
NAME = "function_decomp"

import logging
import re
from difflib import SequenceMatcher
from typing import Any, Dict, List, Optional, Tuple

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")
# ---------------------------
# Options
# ---------------------------

opts_doc = {
    "function_name": {"type": str, "mangle": True, "default": "None"},
    "function_addr": {"type": str, "mangle": True, "default": "None"},
}


def documentation() -> Dict[str, Any]:
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }

# ---------------------------
# Public entry
# ---------------------------


def results(oid_list: List[str], opts: dict) -> Dict[str, Any]:
    oid_list = api.expand_oids(oid_list)

    oid = oid_list[0]

    if opts["function_name"] != "None":
        func_name = opts["function_name"]
    elif opts["function_addr"] != "None":
        func_addr = opts["function_addr"]
        func_name = _get_function_name(oid, func_addr)
    else:
        return {"ERROR": "Please pass in either function_name or function_addr"}
        
    return retrieve_function_decomp_lines(oid, func_name)
# ---------------------------
# Ghidra helpers
# ---------------------------


def _resolve_func_key(decompile: Dict[str, Any], want: str) -> Optional[str]:
    if want in decompile:
        return want

    want_short = want.split("::")[-1]
    cands = [
        k
        for k in decompile.keys()
        if isinstance(k, str) and k.split("::")[-1] == want_short
    ]
    if len(cands) == 1:
        return cands[0]
    return None


def retrieve_function_decomp_lines(oid: str, func_name: Any) -> Optional[List[str]]:
    """
    Return:
      - None  => hard failure (can't resolve function or decmap)
      - []    => function resolved but no decompiler output (benign/empty)
      - [...] => decompiler lines
    """
    if not func_name:
        # Can't even identify the function => hard failure
        return None

    decmap = api.retrieve("ghidra_decmap", [oid], {"org_by_func": True})
    if not isinstance(decmap, dict) or not decmap:
        # Missing/invalid decmap => hard failure
        return None

    dm = decmap.get(oid, decmap) if isinstance(decmap.get(oid), dict) else decmap
    decompile = dm.get("decompile") if isinstance(dm, dict) else None
    if not isinstance(decompile, dict):
        # Missing/invalid decompile section => hard failure
        return None

    func_key = func_name if func_name in decompile else _resolve_func_key(decompile, func_name)
    if not func_key:
        # Function exists (ghidra_disasm) but no decompile entry => empty decomp, NOT failure
        return []

    func_blocks = decompile.get(func_key)
    if not isinstance(func_blocks, dict):
        # Function exists but no blocks => empty decomp, NOT failure
        return []

    decomp_map: Dict[int, str] = {}
    saw_any_tagged = False
    untagged_fallback: List[str] = []

    for _block_id, block in func_blocks.items():
        if not isinstance(block, dict):
            continue
        lines = block.get("line") or []
        if not isinstance(lines, list):
            continue

        for raw in lines:
            if not isinstance(raw, str):
                continue

            # Prefer split parsing to preserve indentation after the colon.
            try:
                left, right = raw.split(":", 1)
                ln = int(left.strip())
                code = right.rstrip("\r\n")
                saw_any_tagged = True
                decomp_map.setdefault(ln, code)
                continue
            except Exception:
                pass

            untagged_fallback.append(raw.rstrip("\r\n"))

    if saw_any_tagged and decomp_map:
        return [decomp_map[ln] for ln in sorted(decomp_map)]

    if untagged_fallback:
        return untagged_fallback

    # Function existed, but no usable lines => empty decomp
    return []

def _get_function_name(oid: str, addr: Any) -> Optional[str]:
    if addr is None:
        return None
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    return funcs.get(addr, {}).get("name")