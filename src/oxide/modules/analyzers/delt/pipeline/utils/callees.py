import logging
import os
from typing import Any, Dict, List, NamedTuple, Optional

from oxide.core import api

from oxide.modules.analyzers.delt.config import NAME
from oxide.modules.analyzers.delt.pipeline.utils.text_utils import ensure_decimal_str, write_text

logger = logging.getLogger(NAME)


def normalize_added_function_ref(raw_item: Any) -> Optional[Dict[str, str]]:
    """ Normalize an already-built added_functions entry (from drift_adapter.build_drift_file_pairs,
        keys "address"/"name") into {"target_func_addr", "target_func_name"}.
    """
    if isinstance(raw_item, dict):
        raw_addr = raw_item.get("target_func_addr", raw_item.get("address"))
        raw_name = raw_item.get("target_func_name", raw_item.get("name"))
    else:
        raw_addr = raw_item
        raw_name = None

    if raw_addr is None:
        return None

    target_addr = ensure_decimal_str(raw_addr)
    if not target_addr or target_addr.lower() == "none":
        return None

    out = {"target_func_addr": target_addr}
    if raw_name is not None:
        name_s = str(raw_name).strip()
        if name_s:
            out["target_func_name"] = name_s
    return out


def _extract_function_decomp_text(resp: Any, oid: Optional[str] = None) -> str:
    data = getattr(resp, "content", resp)

    if isinstance(data, dict) and oid and oid in data:
        data = data[oid]

    if isinstance(data, dict):
        decomp = data.get("decomp")
        if isinstance(decomp, list):
            return "\n".join(str(line) for line in decomp)
        if isinstance(decomp, str):
            return decomp
        return "" if decomp is None else str(decomp)

    if isinstance(data, list):
        return "\n".join(str(line) for line in data)

    if data is None:
        return ""

    return str(data)


def _retrieve_single_decomp(target_oid: str, addr: str) -> str:
    try:
        resp = api.retrieve("function_decomp", [target_oid], {"function_addr": addr})
        return _extract_function_decomp_text(resp, oid=target_oid)
    except Exception as exc:
        logger.warning(
            "function_decomp retrieval failed for function %s in %s: %s",
            addr, target_oid, exc,
        )
        return ""


def fetch_added_func_decomps(target_oid: str, added_functions: List[Dict[str, Any]]) -> Dict[str, str]:
    """ Fetch decompilations for all added functions. Returns {addr: decomp_text}. """
    result: Dict[str, str] = {}
    for item in added_functions:
        normalized = normalize_added_function_ref(item)
        if not normalized:
            continue
        addr = normalized["target_func_addr"]
        result[addr] = _retrieve_single_decomp(target_oid, addr)
    return result


def _as_int(value: Any) -> Optional[int]:
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        try:
            return int(value, 0) if value.lower().startswith("0x") else int(value)
        except ValueError:
            return None
    return None


class AddedCalleeIndex(NamedTuple):
    """ Per-binary index backing added-callee attachment.

        edges maps a function address to the addresses of the added functions it calls,
        so the whole-binary call map is filtered down to added-only edges once rather than
        once per candidate. decomps maps an added function's address to its decompilation,
        keyed as callee_added_funcs returns it.
    """
    edges: Dict[int, List[int]]
    decomps: Dict[int, str]
    keys: Dict[int, str]


def build_added_callee_index(target_oid: str, added_func_decomp: Dict[str, str]) -> Optional[AddedCalleeIndex]:
    """ Build the added-only call-edge index for one binary, or None when there is nothing
        to attach or the call map is unavailable.

        Call edges come from function_call_targets, which derives each function's outgoing
        calls from the disassembled basic-block destinations, the same source
        function_diff_features uses for its call-edge features.
    """
    if not added_func_decomp:
        return None

    call_targets = api.retrieve("function_call_targets", target_oid) or {}
    if not call_targets:
        logger.warning(
            "function_call_targets unavailable for %s, no added callees will be attached",
            target_oid,
        )
        return None

    # The call map is keyed by ghidra_disasm function address, added_func_decomp by the
    # decimal string form, so index the added set by address to join the two.
    decomps: Dict[int, str] = {}
    keys: Dict[int, str] = {}
    for key, text in added_func_decomp.items():
        as_int = _as_int(key)
        if as_int is not None:
            decomps[as_int] = text
            keys[as_int] = key

    edges: Dict[int, List[int]] = {}
    for caller, callees in call_targets.items():
        caller_int = _as_int(caller)
        if caller_int is None:
            continue
        added_callees = [
            callee_int for callee_int in (_as_int(c) for c in (callees or []))
            if callee_int in decomps
        ]
        if added_callees:
            edges[caller_int] = added_callees

    return AddedCalleeIndex(edges=edges, decomps=decomps, keys=keys)


def callee_added_funcs(target_func_addr: Any, index: Optional[AddedCalleeIndex]) -> Dict[str, str]:
    """ Return the newly-added functions reachable from the changed function along call
        edges, following calls through newly-added functions transitively.

        The seed set is the added functions the changed function calls. The closure then
        follows the call targets of each added function it reaches, until no new added
        function is reached. Expansion never leaves the newly-added set, so it stops at the
        boundary of pre-existing code, and every added function on a call chain rooted at
        the changed function is attached and reviewed with that candidate.

        Reachability is therefore control flow only. An added function the update reaches
        without a recovered call edge, as when a modified function installs it into a
        dispatch table for a later indirect call, is not attached.
    """
    if index is None:
        return {}

    anchor = _as_int(target_func_addr)
    if anchor is None:
        return {}

    # Seed: the added functions the changed function calls. Every address on the frontier
    # comes from index.edges, so it is always an added function.
    frontier: List[int] = list(index.edges.get(anchor, []))
    called = len(frontier)

    # Transitive closure over added-only call edges. Bounded by the finite added set, so the
    # visited check guarantees termination.
    reached: Dict[int, str] = {}
    while frontier:
        addr = frontier.pop()
        if addr in reached:
            continue
        reached[addr] = index.decomps[addr]
        frontier.extend(index.edges.get(addr, []))

    if reached:
        logger.debug(
            "callee closure for function %s: %d added function(s) attached (%d called directly)",
            target_func_addr, len(reached), called,
        )
    return {index.keys[addr]: text for addr, text in reached.items()}


def save_added_function_artifacts(
    target_oid: str,
    added_functions: List[Dict[str, Any]],
    fp_idx: int,
    outdir: str,
    decomp_map: Optional[Dict[str, str]] = None,
) -> None:
    if not added_functions:
        return

    filepair_dir = os.path.join(outdir, f"filepair_{fp_idx:02d}")
    added_dir = os.path.join(filepair_dir, "added_functions")
    os.makedirs(added_dir, exist_ok=True)

    for added_idx, item in enumerate(added_functions, 1):
        normalized = normalize_added_function_ref(item)
        if not normalized:
            continue
        target_addr = normalized["target_func_addr"]
        func_dir = os.path.join(
            added_dir,
            f"added_func_{added_idx:02d}__t{target_addr}",
        )
        os.makedirs(func_dir, exist_ok=True)

        if decomp_map is not None and target_addr in decomp_map:
            decomp_text = decomp_map[target_addr]
        else:
            decomp_text = _retrieve_single_decomp(target_oid, target_addr)

        write_text(os.path.join(func_dir, "function_decomp.txt"), decomp_text)
