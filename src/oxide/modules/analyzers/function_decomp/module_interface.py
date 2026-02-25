DESC = ""
NAME = "function_decomp"

import logging
import re
from difflib import SequenceMatcher
from typing import Any, Dict, List, Optional, Tuple

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")
_FUN_TOKEN_RE = re.compile(r"\bFUN_([0-9a-fA-F]+)\b")
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

    # Read-through cache stored under target_oid
    if api.exists(NAME, oid, opts):
        return api.retrieve(NAME, oid, opts)

    if opts["function_name"] != "None":
        func_name = opts["function_name"]
    elif opts["function_addr"] != "None":
        func_addr = opts["function_addr"]
        func_name = _get_function_name(oid, func_addr)
    else:
        return {"ERROR": "Please pass in either function_name or function_addr"}
    
    results = {'decomp': retrieve_function_decomp_text(oid, func_name)}

    # Store/update cache
    api.store(NAME, oid, results, opts)
        
    return results
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


def retrieve_function_decomp_text(oid: str, func_name: Any) -> Optional[str]:
    """
    Return:
      - None   => hard failure (can't resolve function or decmap)
      - ""     => function resolved but no decompiler output (benign/empty)
      - "..."  => decompiler text
    """
    if not func_name:
        return None

    decmap = api.retrieve("ghidra_decmap", [oid], {"org_by_func": True})
    if not isinstance(decmap, dict) or not decmap:
        return None

    dm = decmap.get(oid, decmap) if isinstance(decmap.get(oid), dict) else decmap
    decompile = dm.get("decompile") if isinstance(dm, dict) else None
    if not isinstance(decompile, dict):
        return None

    func_key = func_name if func_name in decompile else _resolve_func_key(decompile, str(func_name))
    if not func_key:
        # function resolved in disasm but no decompile entry
        return ""

    func_blocks = decompile.get(func_key)
    if not isinstance(func_blocks, dict):
        return ""

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
        ordered = [decomp_map[ln] for ln in sorted(decomp_map)]
        return "\n".join(ordered)

    if untagged_fallback:
        return "\n".join(untagged_fallback)

    return ""

def _get_function_name(oid: str, addr: Any) -> Optional[str]:
    if addr is None:
        return None
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    if not isinstance(funcs, dict):
        return None

    def _name_from_meta(meta: Any) -> Optional[str]:
        if isinstance(meta, dict):
            n = meta.get("name")
            if isinstance(n, str) and n:
                return n
            return None
        if isinstance(meta, str) and meta:
            return meta
        return None

    for key in _candidate_func_keys(addr):
        if key in funcs:
            name = _name_from_meta(funcs.get(key))
            if name:
                return name

    addr_int = _parse_addr_any(addr)
    if addr_int is not None:
        for k, meta in funcs.items():
            if _parse_addr_any(k) == addr_int:
                name = _name_from_meta(meta)
                if name:
                    return name
    return None


def _candidate_func_keys(addr: Any) -> List[Any]:
    keys: List[Any] = []
    seen: set = set()

    def _add(v: Any) -> None:
        marker = repr(v)
        if marker in seen:
            return
        seen.add(marker)
        keys.append(v)

    _add(addr)
    _add(str(addr))

    parsed = _parse_addr_any(addr)
    if parsed is not None:
        _add(parsed)
        _add(str(parsed))
        _add(hex(parsed))
        _add(hex(parsed).upper())
        _add(f"FUN_{parsed:x}")
        _add(f"FUN_{parsed:X}")

    return keys


def _parse_addr_any(v: Any) -> Optional[int]:
    try:
        if isinstance(v, int):
            return v
        if isinstance(v, str):
            s = v.strip()
            if not s:
                return None
            m = _FUN_TOKEN_RE.fullmatch(s) or _FUN_TOKEN_RE.search(s)
            if m:
                return int(m.group(1), 16)
            if s.lower().startswith("0x"):
                return int(s, 16)
            if s.isdigit():
                return int(s, 10)
    except Exception:
        return None
    return None
