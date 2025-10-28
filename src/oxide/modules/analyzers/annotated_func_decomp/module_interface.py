# -*- coding: utf-8 -*-
"""
annotated_function_decomp — single-function annotated decompiler output.

Given one oid and one function (address or name), return the function's
decompiler text with inline trailing comments for known *callee* functions
appearing on each line. Tags are fetched via:
    api.get_field("llm_function_analysis", oid, "tag", {"func_offset": addr})

Notes:
  • We append comments only once per line. If a prior comment already
    contains the same fragments, we do not duplicate them.
  • We do not modify leading whitespace/indentation.
"""

DESC = ""
NAME = "annotated_function_decomp"

import logging
import re
from typing import Dict, Any, List, Optional, Tuple

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

# ---------------------------
# Options
# ---------------------------

opts_doc = {
    "func":     {"type": str,  "mangle": True,  "default": "None"},  # address token, hex, int, or name
    "annotate": {"type": bool, "mangle": True,  "default": True},
}

def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False, "atomic": True}

# ---------------------------
# Regexes
# ---------------------------

_RE_WS    = re.compile(r"\s+")
_RE_FUN   = re.compile(r"\bFUN_([0-9a-fA-F]+)\b")
_FUN_TOKEN_RE = re.compile(r"\bFUN_([0-9a-fA-F]+)\b")

# ---------------------------
# Public entry
# ---------------------------

def results(oid_list: List[str], opts: dict) -> Dict[str, Any]:
    oid_list = api.expand_oids(oid_list)
    if not oid_list or len(oid_list) < 1:
        raise ValueError("annotated_function_decomp requires one OID: [oid]")

    oid = oid_list[0]
    func_spec = opts.get("func")

    # Retrieve ORIGINAL decompiler lines (no trailing newlines)
    lines = retrieve_function_decomp_lines(oid, func_spec)
    if not lines:
        return {"error": "Could not retrieve function decompiler lines."}

    # Build a name->addr map for all functions in this binary
    name_to_addr_all = _all_function_names_to_addrs(oid)

    # Restrict to callees actually present in the decomp text
    present_names = _extract_called_names(lines, name_to_addr_all)

    # Also include any explicit FUN_XXXXXXXX tokens present in the text
    present_names.update(_fun_tokens_in_lines(lines))

    # Annotate
    if opts.get("annotate", True) and present_names:
        annotated = _annotate_lines_with_tags(lines, present_names, oid)
    else:
        annotated = "\n".join(lines) + ("\n" if lines else "")

    fn_name = _get_function_name(oid, func_spec) or str(func_spec)

    return {
        "annotated": annotated,
        "meta": {
            "oid": oid,
            "function": fn_name,
        },
    }

# ---------------------------
# Annotation helpers
# ---------------------------

def _annotate_lines_with_tags(
    lines: List[str],
    name_to_addr: Dict[str, int],
    oid: str,
) -> str:
    """
    Append short tags to lines that contain calls to known functions.
    We only annotate once at the end of the line, preserving any existing
    comment (we append after it). We de-duplicate fragments.
    """
    if not lines or not name_to_addr:
        return "\n".join(lines) + ("\n" if lines else "")

    # Pre-fetch tags
    name_to_tag: Dict[str, Optional[str]] = {
        name: _get_tag_for_addr(oid, addr)
        for name, addr in name_to_addr.items()
    }

    # Build a regex that matches only names we know about
    names_sorted = sorted(name_to_addr.keys(), key=len, reverse=True)
    call_pat = re.compile(r"\b(" + "|".join(re.escape(n) for n in names_sorted) + r")\b\s*\(") if names_sorted else None

    out_lines: List[str] = []
    for line in lines:
        if not call_pat:
            out_lines.append(line)
            continue

        # Preserve leading indentation
        leading_ws = len(line) - len(line.lstrip(" \t"))
        prefix_ws = line[:leading_ws]
        body = line[leading_ws:]

        # Split off any existing trailing comment
        code_part, sep, trailing = body.partition("//")

        matches = [m.group(1) for m in call_pat.finditer(code_part)]
        if not matches:
            out_lines.append(line)
            continue

        # Deduplicate while preserving order
        seen: List[str] = []
        for n in matches:
            if n not in seen:
                seen.append(n)

        fragments: List[str] = []
        for n in seen:
            tag = name_to_tag.get(n)
            fragments.append(f"{n}: {tag}" if tag else n)

        # If an existing comment already contains all fragments, keep as-is
        if sep and all(fragment in trailing for fragment in fragments):
            out_lines.append(line)
            continue

        # Rebuild with our appended comment
        annotated = prefix_ws + code_part
        if sep:  # keep original trailing comment
            annotated += sep + trailing
        annotated += (" " if annotated and not annotated.endswith(" ") else "") + "// " + "; ".join(fragments)
        out_lines.append(annotated)

    return "\n".join(out_lines) + ("\n" if out_lines else "")

# ---------------------------
# Name/address discovery
# ---------------------------

def _all_function_names_to_addrs(oid: str) -> Dict[str, int]:
    """
    Build a {name -> addr_int} map for all functions known in ghidra_disasm.
    """
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    out: Dict[str, int] = {}
    # funcs is usually { offset_str/int : { name: ... } } or { offset : name }
    for k, v in (funcs.items() if isinstance(funcs, dict) else []):
        addr = _parse_addr_any(k)
        name = None
        if isinstance(v, dict):
            name = v.get("name")
        elif isinstance(v, str):
            name = v
        if name and addr is not None:
            out[name] = addr
    return out

def _extract_called_names(lines: List[str], name_to_addr_all: Dict[str, int]) -> Dict[str, int]:
    """
    Find identifiers followed by '(' in code and keep those that are known function names.
    """
    # Generic candidate pattern: identifier '('
    cand_pat = re.compile(r"\b([A-Za-z_.$@][\w.$@+-]*)\s*\(")
    present: Dict[str, int] = {}
    for s in lines:
        # Avoid parsing inside existing comments to reduce false positives
        code_part = s.split("//", 1)[0]
        for m in cand_pat.finditer(code_part):
            name = m.group(1)
            if name in name_to_addr_all:
                present[name] = name_to_addr_all[name]
    return present

def _fun_tokens_in_lines(lines: List[str]) -> Dict[str, int]:
    """
    Collect any FUN_XXXXXXXX tokens from the text and map name->addr.
    """
    out: Dict[str, int] = {}
    for s in lines:
        for m in _RE_FUN.finditer(s):
            try:
                a = int(m.group(1), 16)
                out[f"FUN_{a:08x}"] = a
            except Exception:
                pass
    return out

# ---------------------------
# Tag lookup
# ---------------------------

def _get_tag_for_addr(oid: str, addr: int) -> Optional[str]:
    try:
        return api.get_field("llm_function_analysis", oid, "tag", {"func_offset": addr})
    except Exception:
        return None

# ---------------------------
# Ghidra helpers
# ---------------------------

def retrieve_function_decomp_lines(oid: str, func_spec: Any) -> Optional[List[str]]:
    """
    Return the decompiler text for the function as a list of lines (no trailing newlines).
    Accepts func_spec as address (int/hex/FUN_token) or function name.
    """
    func_name = _get_function_name(oid, func_spec)
    if not func_name and isinstance(func_spec, str):
        # If the caller gave us a *name* that isn't resolvable via _get_function_name,
        # try using it directly (some pipelines key decmap by name only).
        func_name = func_spec

    if not func_name:
        return None

    decmap = api.retrieve("ghidra_decmap", [oid], {"org_by_func": True})
    if not decmap:
        return None

    dm = decmap
    if isinstance(decmap, dict) and oid in decmap and isinstance(decmap[oid], dict):
        dm = decmap[oid]

    func_blocks = (dm.get("decompile") or {}).get(func_name)
    if not func_blocks:
        return None

    decomp_map: Dict[int, str] = {}
    for _block_id, block in func_blocks.items():
        lines = block.get("line", [])
        for line in lines:
            split = line.find(": ")
            if split <= 0:
                continue
            try:
                ln = int(line[:split])
                code = line[split + 2 :]
                decomp_map[ln] = code
            except Exception:
                continue

    if not decomp_map:
        return None

    out: List[str] = []
    indent = 0
    for ln in sorted(decomp_map):
        code = decomp_map[ln]
        if "}" in code:
            indent -= 1
        out.append(("    " * max(indent, 0)) + code)
        if "{" in code:
            indent += 1
    return out

def _get_function_name(oid: str, spec: Any) -> Optional[str]:
    """
    Resolve a function *name* from a variety of specs (addr int/hex/FUN_token or name).
    """
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    # If spec is already a name and exists, return it
    if isinstance(spec, str) and not _FUN_TOKEN_RE.fullmatch(spec) and not spec.lower().startswith("0x") and not spec.isdigit():
        # Make sure the name exists in disasm table; otherwise fall through
        for k, v in (funcs.items() if isinstance(funcs, dict) else []):
            if isinstance(v, dict) and v.get("name") == spec:
                return spec
            if isinstance(v, str) and v == spec:
                return spec

    meta = funcs.get(str(spec)) or funcs.get(spec)
    if isinstance(meta, dict):
        name = meta.get("name")
        if name:
            return name
    if isinstance(meta, str):
        return meta

    # Try to parse address-like input and look up by address
    addr = _parse_addr_any(spec)
    if addr is not None:
        meta = funcs.get(str(addr)) or funcs.get(addr)
        if isinstance(meta, dict):
            return meta.get("name")
        if isinstance(meta, str):
            return meta

    return None

# ---------------------------
# Generic address parsing
# ---------------------------

def _parse_addr_any(v: Any) -> Optional[int]:
    try:
        if isinstance(v, int):
            return v
        if isinstance(v, str):
            s = v.strip()
            m = _FUN_TOKEN_RE.fullmatch(s) or _FUN_TOKEN_RE.search(s)
            if m:
                return int(m.group(1), 16)
            if s.lower().startswith("0x"):
                return int(s, 16)
            if s.isdigit():
                return int(s, 10)
        if isinstance(v, dict):
            for k in ("addr", "address", "start", "start_addr", "ea"):
                if k in v:
                    a = _parse_addr_any(v[k])
                    if a is not None:
                        return a
            for k in ("name", "label"):
                if k in v and isinstance(v[k], str):
                    m = _FUN_TOKEN_RE.search(v[k])
                    if m:
                        return int(m.group(1), 16)
        return None
    except Exception:
        return None
