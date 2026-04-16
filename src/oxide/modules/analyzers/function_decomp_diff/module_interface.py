# -*- coding: utf-8 -*-
DESC = ""
NAME = "function_decomp_diff"

import logging
from typing import Any, Dict, List

from oxide.core import api

from align import (
    build_lab_map,
    build_maps,
    build_var_map,
    normalize_lines,
    project_fun_tokens,
    project_lab_tokens,
    project_var_tokens,
)
from annotate import annotate_with_tags, get_function_calls
from emit import (
    LLM_DIFF_CHAR_BUDGET,
    emit_unified_header,
    emit_unified_raw,
    lines_equal_canon,
    make_sequence_matcher,
    emit_refined,
    maybe_compact_unified,
)
from ghidra import get_function_name, retrieve_function_decomp_lines, strip_decmap_prefix_if_present

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {
    "target": {"type": str, "mangle": True, "default": "None"},
    "baseline": {"type": str, "mangle": True, "default": "None"},
    "annotate": {"type": bool, "mangle": True, "default": False},
    "compact": {"type": bool, "mangle": True, "default": False},
    "raw": {"type": bool, "mangle": True, "default": False},
    "max_chars": {"type": int, "mangle": True, "default": 0},
}


def documentation() -> Dict[str, Any]:
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }


def results(oid_list: List[str], opts: dict) -> Dict[str, Any]:
    oid_list = api.expand_oids(oid_list)
    if not oid_list or len(oid_list) < 2:
        raise ValueError("function_decomp_diff requires two OIDs: [target_oid, baseline_oid]")

    target_oid, baseline_oid = oid_list[0], oid_list[1]
    target_addr = opts["target"]
    baseline_addr = opts["baseline"]

    # Read-through cache stored under target_oid, keyed by baseline_oid.
    # Guard with api.exists() to avoid oxide falling through to single_call_module
    # with only 1 OID (which would raise ValueError).
    cache: Dict[str, Any] = {}
    if api.exists(NAME, target_oid, opts):
        cache = api.retrieve(NAME, target_oid, opts) or {}
        if not isinstance(cache, dict):
            cache = {}
        if baseline_oid in cache:
            return cache[baseline_oid]

    raw = bool(opts.get("raw", False))

    tgt_orig = retrieve_function_decomp_lines(target_oid, target_addr)
    base_orig = retrieve_function_decomp_lines(baseline_oid, baseline_addr)

    if tgt_orig is None or base_orig is None:
        return {
            "error": "Could not retrieve function decomp lines for one or both sides.",
            "error_kind": "missing_function_or_decmap",
            "meta": {
                "target_oid": target_oid,
                "baseline_oid": baseline_oid,
                "target_addr": str(target_addr),
                "baseline_addr": str(baseline_addr),
                "target_none": tgt_orig is None,
                "baseline_none": base_orig is None,
            },
        }

    tgt_orig = strip_decmap_prefix_if_present(tgt_orig)
    base_orig = strip_decmap_prefix_if_present(base_orig)

    fn_b = get_function_name(baseline_oid, baseline_addr) or f"{baseline_addr}"
    fn_t = get_function_name(target_oid, target_addr) or f"{target_addr}"
    fromfile = f"{fn_b} (baseline {baseline_oid})"
    tofile = f"{fn_t} (target   {target_oid})"

    base_meta = {
        "baseline_func": fn_b,
        "baseline_oid": baseline_oid,
        "target_func": fn_t,
        "target_oid": target_oid,
        "target_decomp_empty": len(tgt_orig) == 0,
        "baseline_decomp_empty": len(base_orig) == 0,
    }

    if raw:
        unified_raw = emit_unified_raw(base_orig, tgt_orig, fromfile, tofile)
        return {
            "unified": unified_raw,
            "meta": {
                **base_meta,
                "pipeline": "raw",
                "normalized_alignment": False,
                "raw": True,
                "unified_len": len(unified_raw),
            },
        }

    # Normalize both sides for alignment, then project baseline tokens into
    # the target namespace so semantic equality is visible to the differ.
    base_norm = normalize_lines(base_orig)
    tgt_norm = normalize_lines(tgt_orig)

    sm = make_sequence_matcher(base_norm, tgt_norm)
    opcodes = sm.get_opcodes()

    try:
        call_diff = api.retrieve(
            "function_call_diff",
            [target_oid, baseline_oid],
            {"target": str(target_addr), "baseline": str(baseline_addr)},
        ) or {}
    except Exception as e:
        logger.warning(f"[{NAME}] function_call_diff retrieval failed: {e}")
        call_diff = {}

    projmap = build_maps(baseline_addr, target_addr, call_diff)
    lab_map = build_lab_map(base_orig, tgt_orig, opcodes)
    var_map = build_var_map(base_orig, tgt_orig, base_norm, tgt_norm, opcodes)

    base_proj = project_fun_tokens(base_orig, projmap)
    base_proj = project_lab_tokens(base_proj, lab_map)
    base_proj = project_var_tokens(base_proj, var_map)

    out = emit_unified_header(fromfile, tofile, len(base_orig), len(tgt_orig))

    for tag, i1, i2, j1, j2 in opcodes:
        base_slice = base_proj[i1:i2]
        tgt_slice = tgt_orig[j1:j2]

        if tag == "equal":
            # Canonical collapsing: equal-by-norm blocks that differ only in
            # noise tokens (types, addresses) are emitted as context lines.
            if lines_equal_canon(base_slice, tgt_slice):
                for s in tgt_slice:
                    out.append(" " + s)
            else:
                emit_refined(out, base_slice, tgt_slice)
        else:
            emit_refined(out, base_slice, tgt_slice)

    unified = "\n".join(out) + ("\n" if out else "")

    if opts.get("annotate", False):
        name_to_addr = get_function_calls(call_diff)
        if name_to_addr:
            unified = annotate_with_tags(unified, name_to_addr, target_oid)

    unified_full = unified
    char_budget = int(opts.get("max_chars") or 0) or LLM_DIFF_CHAR_BUDGET
    unified_compact = maybe_compact_unified(unified_full, max_chars=char_budget)

    if opts.get("compact", False):
        unified = unified_compact

    output = {
        "unified": unified,
        "meta": {
            **base_meta,
            "pipeline": "full",
            "normalized_alignment": True,
            "raw": False,
            "unified_full_len": len(unified_full),
            "unified_compact_len": len(unified_compact),
            "unified_truncated": len(unified_compact) < len(unified_full),
        },
    }

    cache[baseline_oid] = output
    api.store(NAME, target_oid, cache, opts)

    return output
