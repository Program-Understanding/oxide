"""
Copyright 2023 National Technology & Engineering Solutions
of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS,
the U.S. Government retains certain rights in this software.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
"""

DESC = "Analyze high-level DWARF debug data: functions, inlined functions, globals, types."
NAME = "high_dwarf"

import logging
from typing import Dict, Any

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc: Dict[str, Any] = {}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True}


# ---------------------------------------------------------------------------
# Attribute helpers
# ---------------------------------------------------------------------------

def _attr(attrs: list, name: str):
    """Return the value of the first attribute matching name, or None."""
    for k, v in attrs:
        if k == name:
            return v
    return None


# ---------------------------------------------------------------------------
# Type-chain resolver
# ---------------------------------------------------------------------------

def _type_str(ref, all_dies: dict, cu_offset: int, depth: int = 0) -> str:
    """Walk a DW_AT_type reference chain and return a human-readable type string.

    DW_FORM_ref* values are CU-relative; we try cu_offset+ref first, then ref
    directly (handles ref_addr and single-CU binaries where cu_offset==0).
    """
    if depth > 8 or not isinstance(ref, int):
        return "..."
    die = all_dies.get(cu_offset + ref) or all_dies.get(ref)
    if die is None:
        return f"<{ref:#x}>"

    tag = die.get("Tag", "")
    attrs = die.get("Attributes", [])
    inner = _attr(attrs, "DW_AT_type")

    if tag == "DW_TAG_base_type":
        return _attr(attrs, "DW_AT_name") or "?"

    if tag == "DW_TAG_pointer_type":
        if inner is None:
            return "void *"
        return _type_str(inner, all_dies, cu_offset, depth + 1) + " *"

    if tag == "DW_TAG_reference_type":
        base = _type_str(inner, all_dies, cu_offset, depth + 1) if inner is not None else "void"
        return f"{base} &"

    if tag == "DW_TAG_rvalue_reference_type":
        base = _type_str(inner, all_dies, cu_offset, depth + 1) if inner is not None else "void"
        return f"{base} &&"

    if tag == "DW_TAG_const_type":
        base = _type_str(inner, all_dies, cu_offset, depth + 1) if inner is not None else "void"
        return f"const {base}"

    if tag == "DW_TAG_volatile_type":
        base = _type_str(inner, all_dies, cu_offset, depth + 1) if inner is not None else "void"
        return f"volatile {base}"

    if tag == "DW_TAG_restrict_type":
        base = _type_str(inner, all_dies, cu_offset, depth + 1) if inner is not None else "void"
        return f"restrict {base}"

    if tag == "DW_TAG_array_type":
        base = _type_str(inner, all_dies, cu_offset, depth + 1) if inner is not None else "?"
        return f"{base}[]"

    if tag in ("DW_TAG_typedef", "DW_TAG_structure_type", "DW_TAG_union_type",
               "DW_TAG_enumeration_type", "DW_TAG_class_type"):
        return _attr(attrs, "DW_AT_name") or tag.replace("DW_TAG_", "")

    if tag == "DW_TAG_subroutine_type":
        return "func_ptr"

    return _attr(attrs, "DW_AT_name") or "?"


# ---------------------------------------------------------------------------
# Cross-reference resolver (abstract_origin / specification)
# ---------------------------------------------------------------------------

def _resolve_ref_name(ref, all_dies: dict, cu_offset: int) -> str | None:
    """Resolve a DIE reference to its DW_AT_name, or None."""
    if not isinstance(ref, int):
        return None
    die = all_dies.get(cu_offset + ref) or all_dies.get(ref)
    if die:
        return _attr(die.get("Attributes", []), "DW_AT_name")
    return None


# ---------------------------------------------------------------------------
# Parameter scan
# ---------------------------------------------------------------------------

def _formal_params(dies: dict, func_off: int, sorted_offsets: list) -> list:
    """Return DW_TAG_formal_parameter DIEs that immediately follow func_off.

    Stops at the first die whose tag is not DW_TAG_formal_parameter.
    This works without requiring DW_AT_sibling to be present.
    """
    try:
        idx = sorted_offsets.index(func_off)
    except ValueError:
        return []
    result = []
    for off in sorted_offsets[idx + 1:]:
        die = dies[off]
        if die.get("Tag") != "DW_TAG_formal_parameter":
            break
        result.append(die)
    return result


# ---------------------------------------------------------------------------
# high_pc normalisation
# ---------------------------------------------------------------------------

def _resolve_high_pc(low_pc: int, high_pc: int) -> int:
    """DW_AT_high_pc may be an absolute address or a byte-count offset.
    When it is smaller than low_pc it must be an offset (DWARF4+ constant form).
    """
    return low_pc + high_pc if high_pc < low_pc else high_pc


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def results(oid_list: list, opts: dict) -> Dict[str, Any]:
    logger.debug("results()")
    res = {}

    for oid in oid_list:
        header = api.get_field("object_header", oid, oid)
        if not header:
            logger.debug("No header for %s", oid)
            continue

        debug_info = api.get_field("dwarf5", oid, ".debug_info")
        if not debug_info:
            logger.debug("%s has no .debug_info", oid)
            continue

        # Flat die lookup used by type and ref resolvers.
        all_dies: dict = {}
        for cu_dies in debug_info.values():
            all_dies.update(cu_dies)

        compile_units = []
        functions = []
        inlined_funcs = []
        globals_list = []

        for cu_offset, dies in debug_info.items():
            sorted_offsets = sorted(dies.keys())

            # --- Compile-unit summary (first DW_TAG_compile_unit DIE) ---
            for off in sorted_offsets:
                die = dies[off]
                if die.get("Tag") == "DW_TAG_compile_unit":
                    a = die.get("Attributes", [])
                    compile_units.append({
                        "name":      _attr(a, "DW_AT_name"),
                        "language":  _attr(a, "DW_AT_language"),
                        "producer":  _attr(a, "DW_AT_producer"),
                        "comp_dir":  _attr(a, "DW_AT_comp_dir"),
                    })
                    break

            # --- Walk all DIEs ---
            for die_off in sorted_offsets:
                die = dies[die_off]
                tag = die.get("Tag", "")
                attrs = die.get("Attributes", [])

                # ---- Functions ----
                if tag == "DW_TAG_subprogram":
                    low_pc  = _attr(attrs, "DW_AT_low_pc")
                    high_pc = _attr(attrs, "DW_AT_high_pc")

                    # Skip pure declarations (no address) and extern declarations
                    if low_pc is None or _attr(attrs, "DW_AT_declaration"):
                        continue

                    if isinstance(high_pc, int):
                        high_pc = _resolve_high_pc(low_pc, high_pc)

                    # Collect formal parameters (scan forward until non-param tag)
                    params = []
                    for child in _formal_params(dies, die_off, sorted_offsets):
                        ca = child.get("Attributes", [])
                        p_type_ref = _attr(ca, "DW_AT_type")
                        params.append({
                            "name": _attr(ca, "DW_AT_name"),
                            "type": _type_str(p_type_ref, all_dies, cu_offset)
                                    if p_type_ref is not None else "?",
                        })

                    type_ref = _attr(attrs, "DW_AT_type")
                    functions.append({
                        "name":        _attr(attrs, "DW_AT_name"),
                        "low_pc":      header.get_offset(low_pc),
                        "high_pc":     header.get_offset(high_pc) if high_pc is not None else None,
                        "return_type": _type_str(type_ref, all_dies, cu_offset)
                                       if type_ref is not None else "void",
                        "parameters":  params,
                        "decl_file":   _attr(attrs, "DW_AT_decl_file"),
                        "decl_line":   _attr(attrs, "DW_AT_decl_line"),
                        "external":    bool(_attr(attrs, "DW_AT_external")),
                        "prototyped":  bool(_attr(attrs, "DW_AT_prototyped")),
                        "inline":      bool(_attr(attrs, "DW_AT_inline")),
                    })

                # ---- Inlined subroutines ----
                elif tag == "DW_TAG_inlined_subroutine":
                    low_pc  = _attr(attrs, "DW_AT_low_pc")
                    high_pc = _attr(attrs, "DW_AT_high_pc")
                    if low_pc is None:
                        continue
                    if isinstance(high_pc, int):
                        high_pc = _resolve_high_pc(low_pc, high_pc)

                    origin = _attr(attrs, "DW_AT_abstract_origin")
                    name   = _resolve_ref_name(origin, all_dies, cu_offset)

                    inlined_funcs.append({
                        "name":      name,
                        "low_pc":    header.get_offset(low_pc),
                        "high_pc":   header.get_offset(high_pc) if high_pc is not None else None,
                        "call_file": _attr(attrs, "DW_AT_call_file"),
                        "call_line": _attr(attrs, "DW_AT_call_line"),
                    })

                # ---- Global variables ----
                elif tag == "DW_TAG_variable" and _attr(attrs, "DW_AT_external"):
                    type_ref = _attr(attrs, "DW_AT_type")
                    globals_list.append({
                        "name":      _attr(attrs, "DW_AT_name"),
                        "type":      _type_str(type_ref, all_dies, cu_offset)
                                     if type_ref is not None else "?",
                        "location":  _attr(attrs, "DW_AT_location"),
                        "decl_file": _attr(attrs, "DW_AT_decl_file"),
                        "decl_line": _attr(attrs, "DW_AT_decl_line"),
                    })

        res[oid] = {
            "compile_units":     compile_units,
            "functions":         functions,
            "inlined_functions": inlined_funcs,
            "globals":           globals_list,
        }

    return res
