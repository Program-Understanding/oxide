"""
Smoke tests for MCP-relevant Oxide operations used by agent retrieval workflows.
"""

import json
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from oxide.core import api

NAME = "fuse_mcp_test"


def _as_int(value: Any, default: int, *, min_value: Optional[int] = None) -> int:
    try:
        out = int(value)
    except Exception:
        out = int(default)
    if min_value is not None and out < min_value:
        out = min_value
    return out


def _as_bool(value: Any, default: bool = False) -> bool:
    if isinstance(value, bool):
        return value
    if value is None:
        return default
    s = str(value).strip().lower()
    if s in {"1", "true", "yes", "y", "on"}:
        return True
    if s in {"0", "false", "no", "n", "off"}:
        return False
    return default


def _write_artifact(outdir: str, filename: str, payload: Dict[str, Any]) -> Optional[str]:
    outdir = str(outdir or "").strip()
    if not outdir:
        return None
    p = Path(outdir)
    p.mkdir(parents=True, exist_ok=True)
    target = p / filename
    target.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    return str(target)


def _filter_executables(oids: List[str]) -> List[str]:
    exes: List[str] = []
    for oid in oids:
        cat = api.get_field("categorize", oid, oid)
        if cat != "executable":
            continue
        names = list(api.get_names_from_oid(oid))
        if any(ext in n for n in names for ext in (".so", ".ko")):
            continue
        exes.append(oid)
    return exes


def _resolve_cids(args: List[str], opts: Dict[str, Any]) -> Tuple[List[str], Optional[str]]:
    if args:
        cids: List[str] = []
        for token in args:
            cid = api.get_cid_from_name(token) or token
            if cid:
                cids.append(cid)
        return cids, None

    comp_path = str(opts.get("comp_path", "") or "").strip()
    if comp_path:
        try:
            raw = json.loads(Path(comp_path).read_text(encoding="utf-8"))
        except Exception as e:
            return [], f"Failed to read comp_path: {e}"
        if not isinstance(raw, dict):
            return [], "comp_path JSON must be collection_name -> component map."

        cids = []
        for colname in raw.keys():
            cid = api.get_cid_from_name(colname)
            if cid:
                cids.append(cid)
        if not cids:
            return [], "No collection names from comp_path were found in Oxide datastore."
        return cids, None

    cids = api.collection_cids()
    if not cids:
        return [], "No collections are currently loaded in Oxide datastore."
    return list(cids), None


def _tool_check_strings(oid: str) -> Dict[str, Any]:
    try:
        strings = api.get_field("strings", oid, oid) or {}
        ok = isinstance(strings, dict)
        return {
            "tool": "strings",
            "ok": bool(ok),
            "count": len(strings) if ok else 0,
            "error": None if ok else "Unexpected strings payload type",
        }
    except Exception as e:
        return {"tool": "strings", "ok": False, "count": 0, "error": str(e)}


def _tool_check_file_stats(oid: str) -> Dict[str, Any]:
    try:
        out = api.retrieve("file_stats", [oid]) or {}
        row = out.get(oid) if isinstance(out, dict) else None
        ok = isinstance(row, dict)
        return {
            "tool": "file_stats",
            "ok": bool(ok),
            "keys": sorted(list(row.keys()))[:10] if ok else [],
            "error": None if ok else "file_stats unavailable for oid",
        }
    except Exception as e:
        return {"tool": "file_stats", "ok": False, "keys": [], "error": str(e)}


def _tool_check_function_summaries(oid: str) -> Dict[str, Any]:
    try:
        out = api.retrieve("function_summary", [oid]) or {}
        row = out.get(oid) if isinstance(out, dict) else None
        ok = isinstance(row, dict)
        return {
            "tool": "function_summaries",
            "ok": bool(ok),
            "num_functions": len(row) if ok else 0,
            "error": None if ok else "function_summary unavailable for oid",
        }
    except Exception as e:
        return {
            "tool": "function_summaries",
            "ok": False,
            "num_functions": 0,
            "error": str(e),
        }


def mcp_tool_smoke(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Smoke-test MCP-relevant capabilities over one or more collections.

    Options:
      - comp_path: optional collection_name keyed JSON to scope tested collections
      - sample_per_collection: executable samples per collection (default 3)
      - require_function_summary: mark missing function summaries as hard failures
      - outdir: optional output directory for `mcp_tool_smoke.json`
    """
    cids, err = _resolve_cids(args, opts)
    if err:
        return {"error": err}
    if not cids:
        return {"error": "No collections to test."}

    sample_per_collection = _as_int(opts.get("sample_per_collection"), 3, min_value=1)
    require_fn = _as_bool(opts.get("require_function_summary"), False)

    started = time.perf_counter_ns()
    per_collection: Dict[str, Any] = {}
    hard_failures = 0

    for cid in cids:
        colname = api.get_colname_from_oid(cid)
        oids = list(api.expand_oids(cid))
        exes = _filter_executables(oids)
        sample_oids = exes[:sample_per_collection]

        rows = []
        col_failures = 0
        for oid in sample_oids:
            names = list(api.get_names_from_oid(oid))
            checks = [
                _tool_check_strings(oid),
                _tool_check_file_stats(oid),
                _tool_check_function_summaries(oid),
            ]

            for c in checks:
                if not c.get("ok"):
                    if c.get("tool") == "function_summaries" and not require_fn:
                        continue
                    col_failures += 1

            rows.append(
                {
                    "oid": oid,
                    "names": names,
                    "checks": checks,
                }
            )

        hard_failures += col_failures
        per_collection[colname or cid] = {
            "cid": cid,
            "num_oids": len(oids),
            "num_executables": len(exes),
            "sampled": len(sample_oids),
            "hard_failures": col_failures,
            "rows": rows,
        }

    elapsed_ms = (time.perf_counter_ns() - started) / 1_000_000.0
    payload: Dict[str, Any] = {
        "analysis": "mcp_tool_smoke",
        "collections": len(cids),
        "sample_per_collection": sample_per_collection,
        "require_function_summary": require_fn,
        "hard_failures": hard_failures,
        "ok": hard_failures == 0,
        "runtime_ms": float(f"{elapsed_ms:.3f}"),
        "per_collection": per_collection,
    }

    artifact = _write_artifact(
        str(opts.get("outdir", "") or ""), "mcp_tool_smoke.json", payload
    )
    if artifact:
        payload["artifact"] = artifact
    return payload


def mcp_tool_inventory(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Return MCP tool inventory expected by the firmware agent evaluation flow.
    """
    return {
        "analysis": "mcp_tool_inventory",
        "required_tools": [
            "collection_names",
            "get_cid_from_name",
            "get_oids_in_col",
            "get_names_from_oid",
            "strings",
            "file_stats",
        ],
        "recommended_tools": [
            "function_summaries",
            "call_graph",
            "control_flow_graph",
        ],
        "note": (
            "For retrieval-only experiments, required_tools are sufficient. "
            "Function-level reasoning experiments should include recommended_tools."
        ),
    }


exports = [
    mcp_tool_smoke,
    mcp_tool_inventory,
]
