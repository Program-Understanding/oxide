DESC = "Diff call-graph edges for a single function pair with explicit target/baseline labeling."
NAME = "function_call_diff"

# imports
import logging
from typing import Dict, Any, List, Set, Tuple, Optional
from functools import lru_cache

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {
    "target":   {"type": str, "mangle": True, "default": "None"},
    "baseline": {"type": str, "mangle": True, "default": "None"},
}

def documentation() -> Dict[str, Any]:
    """ Documentation for this module
        private - Whether module shows up in help
        set     - Whether this module accepts collections
        atomic  - Analyzers are atomic and do not persist results
    """
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }

def results(oid_list: List[str], opts: dict) -> Optional[Dict[str, Any]]:
    """Entry point for analyzers (non-persistent)."""
    logger.debug("process()")
    oid_list = api.expand_oids(oid_list)
    if len(oid_list) < 2:
        logger.error("function_call_diff requires two OIDs: [target, baseline]")
        return None

    target_file = oid_list[0]
    baseline_file = oid_list[1]
    target_func = opts["target"]
    baseline_func = opts["baseline"]

    diff = api.retrieve("bindiff", [target_file, baseline_file]) or {}
    out = diff_func_calls(diff, target_file, target_func, baseline_file, baseline_func)
    return out

# ---------------- Core ----------------

def diff_func_calls(
    diff: Dict[str, Any],
    target_file: str,
    target_function: str,
    baseline_file: str,
    baseline_func: str,
) -> Dict[str, Any]:
    """
    Compute call-edge deltas for one function pair.

    Returns:
      {
        "summary": {
          "paired": int,
          "added_existing": int,
          "added_new": int,
          "removed_existing": int,
          "removed_deleted": int
        },
        "fc_paired": [
          {"target": {...}, "baseline": {...}}, ...
        ],
        "fc_add_existing": [
          {"target": {...}, "baseline": {...}}, ...
        ],
        "fc_add_new": [
          {"target": {...}}, ...
        ],
        "fc_removed_existing": [
          {"target": {...}, "baseline": {...}}, ...
        ],
        "fc_removed_deleted": [
          {"baseline": {...}}, ...
        ],
      }
    """
    add_existing, add_new, paired = _get_fc_new(
        diff, target_file=target_file, target_func=target_function, baseline_file=baseline_file, baseline_func=baseline_func
    )
    removed_existing, removed_deleted = _get_fc_removed(
        diff, target_file, target_function, baseline_file, baseline_func
    )

    summary = {
        "paired": len(paired),
        "added_existing": len(add_existing),
        "added_new": len(add_new),
        "removed_existing": len(removed_existing),
        "removed_deleted": len(removed_deleted),
    }

    return {
        "summary": summary,
        "fc_paired": paired,
        "fc_add_existing": add_existing,
        "fc_add_new": add_new,
        "fc_removed_existing": removed_existing,
        "fc_removed_deleted": removed_deleted,
    }

# --------------- Internals ---------------

def _iter_match_pairs(diff: Dict[str, Any]) -> List[Tuple[Any, Any]]:
    """
    Normalize diff['function_matches'] into a list of (t_addr, b_addr) pairs.
    Accepts either a dict keyed by (t_addr, b_addr) or a list of such tuples.
    """
    fm = diff.get("function_matches", {})
    if isinstance(fm, dict):
        # Keys may already be tuples (t, b); values are metadata. Keep keys.
        return list(fm.keys())
    if isinstance(fm, list):
        return list(fm)
    return []

def _get_tag(oid: str, addr: Any) -> Optional[str]:
    """
    Cached wrapper for LLM tag retrieval to avoid repeated round-trips.
    """
    try:
        tag = api.get_field("llm_function_analysis", oid, "tag", {"func_offset": addr})
        why = api.get_field("llm_function_analysis", oid, "why", {"func_offset": addr})
    except Exception as e:
        logger.debug(f"tag lookup failed for {oid}@{addr}: {e}")
    return tag, why

def _mk_side(oid: str, addr: Any) -> Dict[str, Any]:
    """
    Uniform per-side payload.
    """
    tag, why = _get_tag(oid, addr)
    return {
        "addr": addr,
        "name": _get_function_name(oid, addr),
        "tag": tag,
        "why": why
    }

def _get_fc_new(
    diff: Dict[str, Any],
    target_file: str, target_func: str,
    baseline_file: str, baseline_func: str,
) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]], List[Dict[str, Any]]]:
    """
    Return lists of new call-edges in target:
      • add_existing: calls to functions that existed in baseline
      • add_new:      calls to brand-new functions (no baseline match)
      • paired:       calls that were already present in both
    (All entries are explicit dicts labeling target/baseline sides.)
    """
    target_calls: Set[Any] = set(api.get_field("function_call_targets", target_file,  int(target_func)) or [])
    baseline_calls: Set[Any] = set(api.get_field("function_call_targets", baseline_file, int(baseline_func)) or [])

    match_pairs = _iter_match_pairs(diff)
    t2b = {t: b for (t, b) in match_pairs}

    add_existing: List[Dict[str, Any]] = []
    add_new: List[Dict[str, Any]] = []
    paired: List[Dict[str, Any]] = []

    for t_callee in sorted(target_calls):
        b_callee = t2b.get(t_callee)
        if b_callee is not None:
            if b_callee in baseline_calls:
                paired.append({
                    "target": _mk_side(target_file, t_callee),
                    "baseline": _mk_side(baseline_file, b_callee),
                })
            else:
                add_existing.append({
                    "target": _mk_side(target_file, t_callee),
                    "baseline": _mk_side(baseline_file, b_callee),
                })
        else:
            add_new.append({
                "target": _mk_side(target_file, t_callee),
            })

    return add_existing, add_new, paired

def _get_fc_removed(
    diff: Dict[str, Any],
    target_file: str, target_func: str,
    baseline_file: str, baseline_func: str,
) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    """
    Return lists of removed call-edges from baseline:
      • removed_existing: callee survived but edge removed (callee still exists in target)
      • removed_deleted:  callee function no longer exists (no match in target)
    (All entries are explicit dicts labeling target/baseline sides.)
    """
    baseline_calls: Set[Any] = set(api.get_field("function_call_targets", baseline_file, int(baseline_func)) or [])
    target_calls:   Set[Any] = set(api.get_field("function_call_targets", target_file,   int(target_func))   or [])

    match_pairs = _iter_match_pairs(diff)
    b2t = {b: t for (t, b) in match_pairs}

    removed_existing: List[Dict[str, Any]] = []
    removed_deleted:  List[Dict[str, Any]] = []

    for b_callee in sorted(baseline_calls):
        t_callee = b2t.get(b_callee)
        if t_callee is not None:
            if t_callee not in target_calls:
                removed_existing.append({
                    "target": _mk_side(target_file, t_callee),
                    "baseline": _mk_side(baseline_file, b_callee),
                })
        else:
            removed_deleted.append({
                "baseline": _mk_side(baseline_file, b_callee),
            })

    return removed_existing, removed_deleted

def _get_function_name(oid: str, offset: Any) -> Optional[str]:
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    return funcs.get(offset, {}).get("name")