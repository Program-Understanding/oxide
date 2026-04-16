DESC = "Persisted target→baseline function pairing map for a file pair (matched functions only, via BinDiff)."
NAME = "function_mapping"

import logging
import re
from typing import Any, Dict, List, Optional, Tuple

from oxide.core import api

logger = logging.getLogger(NAME)

opts_doc: Dict[str, Any] = {}

def documentation() -> Dict[str, Any]:
    """
    Returns module documentation.
    """
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }

def documentation() -> Dict[str, Any]:
    """
    Persistent analyzer:
      atomic=False => results are stored and can be retrieved later.
    """
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": False,  # persist results
    }

def results(oid_list: List[str], opts: dict) -> Optional[Dict[str, str]]:
    """
    Usage:
      api.retrieve("function_pairing", [target_file_oid, baseline_file_oid], {})

    Returns:
      { "<target_addr_dec>": "<baseline_addr_dec>" | "" }
    Only includes matched target functions from BinDiff.
    """
    oid_list = api.expand_oids(oid_list)
    if len(oid_list) < 2:
        logger.error("function_pairing requires two OIDs: [target_file, baseline_file]")
        return None

    target_oid = oid_list[0]
    baseline_oid = oid_list[1]

    # Read-through cache stored under target_oid, keyed by baseline_oid
    if api.exists(NAME, target_oid):
        data = api.retrieve(NAME, target_oid) or {}
        if isinstance(data, dict) and baseline_oid in data:
            return data[baseline_oid]
        
    diff = api.retrieve("bindiff", [target_oid, baseline_oid]) or {}

    out: Dict[str, str] = {}
    for t_addr, b_addr in _iter_match_pairs(diff):
        result = {
            "b_addr": b_addr,
            "b_name": _get_function_name(baseline_oid, b_addr),
            "t_addr": t_addr,
            "t_name": _get_function_name(target_oid, t_addr)
        }
        out[t_addr] = result

    # Store/update cache
    if api.exists(NAME, target_oid):
        data = api.retrieve(NAME, target_oid) or {}
        if not isinstance(data, dict):
            data = {}
        data[baseline_oid] = out
        api.store(NAME, target_oid, data)
    else:
        api.store(NAME, target_oid, {baseline_oid: out})

    return out

def _iter_match_pairs(diff: Dict[str, Any]) -> List[Tuple[Any, Any]]:
    """
    Normalize diff['function_matches'] into a list of (t_addr, b_addr) pairs.
    Accepts either:
      - dict keyed by (t_addr, b_addr) with metadata values
      - list of (t_addr, b_addr) pairs
    """
    fm = (diff or {}).get("function_matches", {})
    if isinstance(fm, dict):
        return list(fm.keys())
    if isinstance(fm, list):
        return list(fm)
    return []

def _get_function_name(oid: str, addr: Any) -> Optional[str]:
    if addr is None:
        return None
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    return funcs.get(addr, {}).get("name")