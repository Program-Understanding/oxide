import logging
import os
from typing import Any, Dict, List, Optional

from oxide.core import api

from oxide.modules.analyzers.backdoor_triage.config import NAME
from oxide.modules.analyzers.backdoor_triage.pipeline.utils.text_utils import ensure_decimal_str, write_text

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


def callee_added_funcs(diff_text: str, added_func_decomp: Dict[str, str], target_oid: str) -> Dict[str, str]:
    """ Return the subset of added_func_decomp whose Ghidra names appear in the + lines of diff_text. """
    if not added_func_decomp or not diff_text:
        return {}
    plus_text = " ".join(
        line[1:] for line in diff_text.splitlines()
        if line.startswith("+") and not line.startswith("+++")
    )
    funcs = api.get_field("ghidra_disasm", target_oid, "functions") or {}
    result: Dict[str, str] = {}
    for addr, text in added_func_decomp.items():
        try:
            addr_int = int(addr)
        except (ValueError, TypeError):
            continue
        meta = funcs.get(addr_int) or {}
        name = meta.get("name") if isinstance(meta, dict) else (meta if isinstance(meta, str) else None)
        if name and name in plus_text:
            result[addr] = text
    return result


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
