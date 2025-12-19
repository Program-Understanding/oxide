from __future__ import annotations
from typing import Any, Dict, List, Optional
from oxide.core import api
from text_tools import RE_DECMAP_PREFIX, parse_addr_any


def resolve_func_key(decompile: Dict[str, Any], want: str) -> Optional[str]:
    if want in decompile:
        return want

    want_short = want.split("::")[-1]
    cands = [
        k for k in decompile.keys()
        if isinstance(k, str) and k.split("::")[-1] == want_short
    ]
    if len(cands) == 1:
        return cands[0]
    return None


def strip_decmap_prefix_if_present(lines: List[str]) -> List[str]:
    if not lines:
        return lines

    if not any(isinstance(s, str) and RE_DECMAP_PREFIX.match(s) for s in lines[:25]):
        return lines

    out: List[str] = []
    for s in lines:
        if not isinstance(s, str):
            out.append(s)
            continue
        m = RE_DECMAP_PREFIX.match(s)
        out.append((m.group(1) if m else s).rstrip("\r\n"))
    return out


def get_function_name(oid: str, offset: Any) -> Optional[str]:
    addr = parse_addr_any(offset)
    if addr is None:
        return None
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    return funcs.get(addr, {}).get("name")


def retrieve_function_decomp_lines(oid: str, func_addr: Any) -> Optional[List[str]]:
    func_name = get_function_name(oid, func_addr)
    if not func_name:
        return None

    decmap = api.retrieve("ghidra_decmap", [oid], {"org_by_func": True})
    if not isinstance(decmap, dict) or not decmap:
        return None

    dm = decmap.get(oid, decmap) if isinstance(decmap.get(oid), dict) else decmap
    decompile = dm.get("decompile") if isinstance(dm, dict) else None
    if not isinstance(decompile, dict):
        return None

    func_key = func_name if func_name in decompile else resolve_func_key(decompile, func_name)
    func_blocks = decompile.get(func_key) if func_key else None
    if not isinstance(func_blocks, dict):
        return None

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
        return [decomp_map[ln] for ln in sorted(decomp_map)]

    if untagged_fallback:
        return untagged_fallback

    return None
