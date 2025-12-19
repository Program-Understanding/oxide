# -*- coding: utf-8 -*-
"""
function_decomp_diff — unified diff with target-centric call syncing + post-diff annotations.

Pipeline:
  1) Retrieve baseline/target decompiler text.
  2) Build call pairing from function_call_diff (target-centric).
  3) Normalize both sides to stable labels for alignment (optional).
  4) Align with SequenceMatcher to get opcodes.
  5) Infer mappings and project baseline ORIGINAL into target namespace.
  6) Emit unified diff with replace-refinement.
  7) Optionally post-annotate '+' lines with LLM tags.
  8) Optionally compact for LLM context budget.
"""

from __future__ import annotations

import logging
import os
import sys
from difflib import SequenceMatcher
from typing import Any, Dict, List

from oxide.core import api

# Ensure sibling package imports work even if cwd is different
sys.path.insert(0, os.path.dirname(__file__))

from text_tools import normalize_lines, lines_equal_ignoring_ws
from ghidra_io import get_function_name, retrieve_function_decomp_lines, strip_decmap_prefix_if_present
from mapping import (
    build_fun_projection_map,
    build_lab_map_from_opcodes,
    build_var_map,
    project_fun_tokens,
    project_lab_tokens,
    project_var_tokens,
)
from emit import emit_refined
from postproc import get_function_calls, annotate_unified_with_tags, maybe_compact_unified

DESC = ""
NAME = "function_decomp_diff"

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {
    "target": {"type": str, "mangle": True, "default": "None"},
    "baseline": {"type": str, "mangle": True, "default": "None"},
    "annotate": {"type": bool, "mangle": True, "default": False},
    "normalize": {"type": bool, "mangle": True, "default": True},
    "compact": {"type": bool, "mangle": True, "default": True},
}


def documentation() -> Dict[str, Any]:
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }


# LLM budget (approx)
_LLM_NUM_CTX_TOKENS = 8192
_LLM_RESERVED_TOKENS = 1024
_APPROX_CHARS_PER_TOKEN = 4
_MAX_UNIFIED_CHARS = (_LLM_NUM_CTX_TOKENS - _LLM_RESERVED_TOKENS) * _APPROX_CHARS_PER_TOKEN
_LLM_DIFF_CHAR_BUDGET = min(_MAX_UNIFIED_CHARS, 20000)


def results(oid_list: List[str], opts: dict) -> Dict[str, Any]:
    oid_list = api.expand_oids(oid_list)
    if not oid_list or len(oid_list) < 2:
        raise ValueError("function_decomp_diff requires two OIDs: [target_oid, baseline_oid]")

    target_oid, baseline_oid = oid_list[0], oid_list[1]
    target_addr = opts["target"]
    baseline_addr = opts["baseline"]

    tgt_orig = retrieve_function_decomp_lines(target_oid, target_addr)
    base_orig = retrieve_function_decomp_lines(baseline_oid, baseline_addr)

    tgt_orig = strip_decmap_prefix_if_present(tgt_orig or [])
    base_orig = strip_decmap_prefix_if_present(base_orig or [])

    if not tgt_orig or not base_orig:
        return {"error": "Could not retrieve function decomp lines for one or both sides."}

    do_norm = bool(opts.get("normalize", True))
    if do_norm:
        base_norm = normalize_lines(base_orig)
        tgt_norm = normalize_lines(tgt_orig)
    else:
        base_norm = base_orig
        tgt_norm = tgt_orig

    sm = SequenceMatcher(
        None,
        [l + "\n" for l in base_norm],
        [l + "\n" for l in tgt_norm],
        autojunk=False,
    )
    opcodes = sm.get_opcodes()

    projmap_base = build_fun_projection_map(baseline_oid, target_oid, baseline_addr, target_addr)
    lab_map = build_lab_map_from_opcodes(base_orig, tgt_orig, opcodes)
    var_map = build_var_map(base_orig, tgt_orig, base_norm, tgt_norm, opcodes)

    base_proj = project_fun_tokens(base_orig, projmap_base)
    base_proj = project_lab_tokens(base_proj, lab_map)
    base_proj = project_var_tokens(base_proj, var_map)

    a_len = len(base_orig)
    b_len = len(tgt_orig)
    a_start_disp = 1 if a_len else 0
    b_start_disp = 1 if b_len else 0

    fn_b = get_function_name(baseline_oid, baseline_addr) or f"{baseline_addr}"
    fn_t = get_function_name(target_oid, target_addr) or f"{target_addr}"
    fromfile = f"{fn_b} (baseline {baseline_oid})"
    tofile = f"{fn_t} (target   {target_oid})"

    out: List[str] = [
        f"--- {fromfile}",
        f"+++ {tofile}",
        f"@@ -{a_start_disp},{a_len} +{b_start_disp},{b_len} @@",
    ]

    for tag, i1, i2, j1, j2 in opcodes:
        base_slice = base_proj[i1:i2]
        tgt_slice = tgt_orig[j1:j2]

        if tag == "equal":
            # Guard: normalized-equal must also be truly equal in ORIGINAL text
            if lines_equal_ignoring_ws(base_slice, tgt_slice):
                for s in tgt_slice:
                    out.append(" " + s)
            else:
                emit_refined(out, base_slice, tgt_slice)
        else:
            emit_refined(out, base_slice, tgt_slice)

    unified = "\n".join(out) + ("\n" if out else "")

    if opts.get("annotate", False):
        name_to_addr = get_function_calls(target_oid, baseline_oid, target_addr, baseline_addr)
        if name_to_addr:
            unified = annotate_unified_with_tags(
                unified,
                name_to_addr,
                target_oid,
                annotate_kinds=("+",),
            )

    unified_full = unified
    unified_compact = maybe_compact_unified(unified_full, budget=_LLM_DIFF_CHAR_BUDGET)

    if opts.get("compact", True):
        unified = unified_compact
    else:
        unified = unified_full

    return {
        "unified": unified,
        "meta": {
            "baseline_func": fn_b,
            "baseline_oid": baseline_oid,
            "target_func": fn_t,
            "target_oid": target_oid,
            "normalized_alignment": do_norm,
            "unified_full_len": len(unified_full),
            "unified_compact_len": len(unified_compact),
            "unified_truncated": len(unified_compact) < len(unified_full),
        },
    }
