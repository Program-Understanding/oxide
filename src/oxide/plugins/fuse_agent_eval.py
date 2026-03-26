from __future__ import annotations

"""
MCP adapter for agentic FUSE retrieval evaluation.

Design constraints:
- Fixed analysis tool interface across profiles.
- No filename/path leakage.
- Retrieval tool surface selected via environment/config.
- Trace includes retrieve candidate OIDs for first-correct-call analysis.
"""

import csv
import json
import logging
import math
import os
import random
import re
import subprocess
import threading
import time
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Sequence, Set, Tuple

from oxide.core import api

try:
    from pydantic import BaseModel, Field
except Exception:  # pragma: no cover
    class BaseModel:  # type: ignore
        @classmethod
        def model_validate(cls, value: Any):
            if isinstance(value, cls):
                return value
            if isinstance(value, dict):
                obj = cls()
                for k, v in value.items():
                    setattr(obj, k, v)
                return obj
            return cls()

        def model_dump(self) -> Dict[str, Any]:
            return dict(getattr(self, "__dict__", {}))

    def Field(default: Any = None, **_: Any) -> Any:  # type: ignore
        return default

try:
    from deepagents import create_deep_agent
    from langchain.agents.structured_output import ToolStrategy
    from langchain_core.callbacks import BaseCallbackHandler
    from langchain_core.messages import AIMessage, HumanMessage
    from langchain_core.tools import tool
    from langchain_ollama import ChatOllama
    from langgraph.errors import GraphRecursionError
    _DEEP_AGENT_IMPORT_ERROR: Optional[Exception] = None
except Exception as e:  # pragma: no cover
    create_deep_agent = None  # type: ignore
    ToolStrategy = None  # type: ignore
    _DEEP_AGENT_IMPORT_ERROR = e

    class BaseCallbackHandler:  # type: ignore
        pass

    class AIMessage:  # type: ignore
        content: Any = ""

    class HumanMessage:  # type: ignore
        def __init__(self, content: Any = "") -> None:
            self.content = content

    def tool(*decorator_args: Any, **decorator_kwargs: Any):  # type: ignore
        if decorator_args and callable(decorator_args[0]) and len(decorator_args) == 1 and not decorator_kwargs:
            return decorator_args[0]

        def _wrap(fn: Callable[..., Any]) -> Callable[..., Any]:
            return fn

        return _wrap

    class ChatOllama:  # type: ignore
        def __init__(self, *_: Any, **__: Any) -> None:
            raise RuntimeError(f"Deep-agent dependencies unavailable: {_DEEP_AGENT_IMPORT_ERROR!r}")

    class GraphRecursionError(Exception):  # type: ignore
        pass


TRACE_LOCK = threading.Lock()
CALL_GRAPH_CACHE: Dict[str, Dict[str, Any]] = {}
FUNC_ID_RE = re.compile(r"(?:func_)?(?:0x)?([0-9a-fA-F]+)$")
VALID_RETRIEVAL_TOOLS = {"search_binaries", "search_strings", "bm25", "emb"}
AGENT_CONDITION_LABELS: Dict[str, str] = {
    "base": "BASE",
    "bm25": "BM25",
    "emb": "EMB",
    "both": "BOTH",
    "oracle": "ORACLE",
}

SEARCH_BINARIES_LEXICAL_DESCRIPTION = (
    "Query and return candidate binaries ranked by lexical overlap between "
    "the query and extracted strings, with optional per-binary string matches "
    "and optional filtering. Use offset to page through results."
)
SEARCH_BINARIES_SEMANTIC_DESCRIPTION = (
    "Query and return candidate binaries ranked by semantic similarity between the "
    "query and extracted string evidence, with optional per-binary string "
    "matches and optional filtering. Use offset to page through results."
)
SEARCH_FUNCTIONS_DESCRIPTION = (
    "Search decompiled functions by query across all binaries or within a specific binary. "
    "search_mode: 'semantic' (default), 'literal' (substring), or 'both'. "
    "Always returns semantic_total and literal_total to help decide which mode to use. "
    "similarity_threshold filters semantic results (0.0-1.0). "
    "Use offset to page through results. "
    "Returns ranked functions with score, preview, match_type, and candidate_oids."
)
GET_FUNCTION_LIST_DESCRIPTION = (
    "Return function IDs, addresses, and names for a binary. "
    "Use this to inspect the size and layout of a binary, not to select functions for decompilation."
)
GET_CALL_GRAPH_DESCRIPTION = (
    "Return call graph nodes and edges for a binary, including function_name and "
    "function_addr on nodes. Optional function_name focuses "
    "output to one-hop callers and callees."
)
GREP_STRINGS_DESCRIPTION = (
    "Run regex or exact matching over extracted strings for one binary, a list of "
    "binaries, or all binaries."
)
GET_STRINGS_DESCRIPTION = (
    "Return all extracted strings for a binary. "
    "Use this to inspect a candidate binary's string content without needing a pattern. "
    "Results are capped at max_strings (default 400) and filtered to min_len (default 4)."
)
GET_FUNC_DECOMP_DESCRIPTION = (
    "Return decompiled code for a specific function in a binary. "
    "Pass function_name (required). "
)




def _append_jsonl_event(path: str, event: Dict[str, Any], *, lock: Optional[threading.Lock] = None) -> None:
    if not path:
        return
    try:
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
        line = json.dumps(event, ensure_ascii=False) + "\n"
        if lock is not None:
            with lock:
                with open(path, "a", encoding="utf-8") as f:
                    f.write(line)
            return
        with open(path, "a", encoding="utf-8") as f:
            f.write(line)
    except Exception:
        return


def _safe_int(value: Any, default: int = 0, *, min_value: Optional[int] = None) -> int:
    try:
        out = int(value)
    except Exception:
        out = int(default)
    if min_value is not None and out < min_value:
        out = min_value
    return out



def _normalize_strings_payload(raw: Any, *, min_len: int, max_len: int) -> List[str]:
    out: List[str] = []

    def _push(value: Any) -> None:
        text = str(value or "").strip()
        if len(text) < min_len:
            return
        if len(text) > max_len:
            text = text[:max_len]
        out.append(text)

    if isinstance(raw, dict):
        for v in raw.values():
            _push(v)
    elif isinstance(raw, list):
        for v in raw:
            _push(v)
    elif raw is not None:
        _push(raw)

    return list(dict.fromkeys(out))


def _get_strings_for_oid(
    api: Any,
    oid: str,
    *,
    max_strings: int = 400,
    min_len: int = 4,
    max_len: int = 512,
) -> List[str]:
    raw = api.get_field("strings", str(oid), str(oid)) or []
    strings = _normalize_strings_payload(raw, min_len=max(1, int(min_len)), max_len=max(8, int(max_len)))
    limit = _safe_int(max_strings, 400, min_value=1)
    return strings[:limit]


def _filter_executable_oids(api: Any, oids: Sequence[str]) -> List[str]:
    exes: List[str] = []
    for oid in oids:
        oid_s = str(oid or "").strip()
        if not oid_s:
            continue
        cat = api.get_field("categorize", oid_s, oid_s)
        if cat != "executable":
            continue
        names = list(api.get_names_from_oid(oid_s) or [])
        if any(
            str(n).endswith(".so")
            or str(n).endswith(".ko")
            or ".so." in str(n)
            or ".ko." in str(n)
            for n in names
        ):
            continue
        exes.append(oid_s)
    return exes


def _int_addr(value: Any) -> Optional[int]:
    if isinstance(value, int):
        return value
    s = str(value or "").strip()
    if not s:
        return None
    try:
        if s.startswith("0x") or s.startswith("0X"):
            return int(s, 16)
        if all(ch in "0123456789abcdefABCDEF" for ch in s):
            return int(s, 16)
        return int(s)
    except Exception:
        return None


def _parse_query_func_addr(value: Any) -> Optional[int]:
    """Parse query_function addresses; bare digits are decimal there."""
    if isinstance(value, int):
        return value
    s = str(value or "").strip()
    if not s:
        return None
    try:
        if s.startswith("0x") or s.startswith("0X"):
            return int(s, 16)
        if s.isdigit():
            return int(s, 10)
        if all(ch in "0123456789abcdefABCDEF" for ch in s):
            return int(s, 16)
        return int(s)
    except Exception:
        return None


def _extract_qf_candidates(raw: Any, top_k: int) -> List[Dict[str, Any]]:
    payload = raw if isinstance(raw, dict) else {}
    if payload and len(payload) == 1:
        only = next(iter(payload.values()))
        if isinstance(only, dict) and "results" in only:
            payload = only
    results = payload.get("results") if isinstance(payload, dict) else None
    cands = results.get("candidates") if isinstance(results, dict) else None
    if not isinstance(cands, list):
        return []

    out: List[Dict[str, Any]] = []
    for cand in cands:
        if not isinstance(cand, dict):
            continue
        oid = str(cand.get("oid") or "").strip()
        if not oid:
            continue
        score = float(cand.get("score", 0.0) or 0.0)
        addr_i = _parse_query_func_addr(
            cand.get("function_addr")
            or cand.get("func_addr")
            or cand.get("address")
            or cand.get("addr")
        )
        if addr_i is None:
            continue
        out.append(
            {
                "oid": oid,
                "func_id": f"func_{addr_i:x}",
                "address": f"0x{addr_i:x}",
                "function_addr": f"0x{addr_i:x}",
                "function_name": str(cand.get("func_name") or cand.get("function_name") or ""),
                "score": score,
                "preview": str(cand.get("preview") or ""),
                "match_type": str(cand.get("match_type") or "semantic"),
            }
        )
    out.sort(key=lambda x: float(x.get("score", 0.0)), reverse=True)
    k = _safe_int(top_k, 10, min_value=1)
    return out[:k]


def _iter_call_addrs(raw: Any) -> List[int]:
    if isinstance(raw, dict):
        items = raw.keys()
    elif isinstance(raw, (list, tuple, set)):
        items = raw
    else:
        items = []
    out: List[int] = []
    for x in items:
        addr = _int_addr(x)
        if addr is None:
            continue
        out.append(int(addr))
    return out


def run_search_functions_query(
    api: Any,
    cid: str,
    query: str,
    *,
    top_k: int = 20,
    offset: int = 0,
    oid: str = "",
    oids: Optional[Sequence[str]] = None,
    search_mode: str = "semantic",
    similarity_threshold: float = 0.0,
) -> Dict[str, Any]:
    """
    Function-level semantic search with optional file scope.
    If oid/oids are omitted, search all executable OIDs in the collection.
    """
    cid_s = str(cid or "").strip()
    if not cid_s:
        raise RuntimeError("OXIDE_FUSE_EVAL_CID is not set for this run.")
    q = str(query or "").strip()
    if not q:
        raise RuntimeError("query is required.")

    scope: List[str] = []
    one = str(oid or "").strip()
    if one:
        scope.append(one)
    for x in (oids or []):
        sx = str(x or "").strip()
        if sx:
            scope.append(sx)
    if not scope:
        scope = _filter_executable_oids(api, list(api.expand_oids(cid_s) or []))
    scope = list(dict.fromkeys(scope))
    if not scope:
        return {
            "candidates": [],
            "file_candidates": [],
            "candidate_oids": [],
            "total_candidates": 0,
            "total_files": 0,
            "scope_size": 0,
        }

    k = _safe_int(top_k, 10, min_value=1)
    off = max(0, _safe_int(offset, 0, min_value=0))
    mode = str(search_mode or "semantic").strip().lower()
    if mode not in ("semantic", "literal", "both"):
        mode = "semantic"
    # Request k+off so we have enough results to slice after applying offset.
    out = api.retrieve(
        "query_function",
        scope,
        {
            "query": q,
            "top_k": k + off,
            "search_mode": mode,
            "similarity_threshold": float(similarity_threshold),
            "timing": False,
            "progress": False,
        },
    )
    all_funcs = _extract_qf_candidates(out, k + off)

    # Ensure each candidate has a usable function_name key.
    name_cache: Dict[str, Dict[int, str]] = {}

    def _name_map_for_oid(oid_s: str) -> Dict[int, str]:
        cached = name_cache.get(oid_s)
        if cached is not None:
            return cached
        mapping: Dict[int, str] = {}
        raw_funcs = api.get_field("ghidra_disasm", oid_s, "functions") or {}
        if isinstance(raw_funcs, dict):
            for f_addr, meta in raw_funcs.items():
                addr_i = _int_addr(f_addr)
                if addr_i is None:
                    continue
                name = ""
                if isinstance(meta, dict):
                    name = str(meta.get("name") or "")
                elif isinstance(meta, str):
                    name = str(meta)
                if name:
                    mapping[int(addr_i)] = name
        name_cache[oid_s] = mapping
        return mapping

    for row in all_funcs:
        name = str(row.get("function_name") or "").strip()
        addr_i = _int_addr(row.get("function_addr") or row.get("address"))
        oid_i = str(row.get("oid") or "")
        if (not name) and addr_i is not None and oid_i:
            name = _name_map_for_oid(oid_i).get(int(addr_i), "")
        if (not name) and addr_i is not None:
            name = f"FUN_{int(addr_i):x}"
        row["function_name"] = name

    for idx, row in enumerate(all_funcs, start=1):
        row["rank"] = idx

    funcs = all_funcs[off:off + k]

    file_best: Dict[str, float] = {}
    for row in funcs:
        oo = str(row.get("oid") or "")
        sc = float(row.get("score", 0.0) or 0.0)
        if oo not in file_best or sc > file_best[oo]:
            file_best[oo] = sc
    file_candidates = [
        {"oid": oo, "rank": idx, "score": float(sc)}
        for idx, (oo, sc) in enumerate(
            sorted(file_best.items(), key=lambda kv: kv[1], reverse=True),
            start=1,
        )
    ]
    candidate_oids = [x["oid"] for x in file_candidates]

    return {
        "candidates": funcs,
        "file_candidates": file_candidates,
        "candidate_oids": candidate_oids,
        "total_candidates": len(all_funcs),
        "returned_count": len(funcs),
        "offset": off,
        "total_files": len(file_candidates),
        "scope_size": len(scope),
        "semantic_total": int((out or {}).get("semantic_total", 0) or 0),
        "literal_total": int((out or {}).get("literal_total", 0) or 0),
        "search_mode": mode,
    }


def run_grep_strings_query(
    api: Any,
    oid: str = "",
    *,
    oids: Optional[Sequence[str]] = None,
    cid: str = "",
    pattern: str = "",
    patterns: Optional[Sequence[str]] = None,
    case_sensitive: bool = False,
    max_matches: int = 100,
    min_len: int = 4,
    max_strings: int = 400,
) -> Dict[str, Any]:
    """
    Shared grep-style string inspection helper used by MCP and in-process runtimes.
    """
    oid_s = str(oid or "").strip()
    cid_s = str(cid or "").strip()
    scope: List[str] = []
    if oid_s:
        scope.append(oid_s)
    for x in (oids or []):
        sx = str(x or "").strip()
        if sx:
            scope.append(sx)
    if not scope:
        if not cid_s:
            raise RuntimeError("cid is required when oid/oids are not provided.")
        scope = _filter_executable_oids(api, list(api.expand_oids(cid_s) or []))
    scope = list(dict.fromkeys(scope))
    if not scope:
        return {
            "patterns": [],
            "scope_size": 0,
            "results": [],
            "total_searched_strings": 0,
            "total_matched_strings": 0,
            "matched_oids": [],
            "matched_oid_count": 0,
        }
    pats: List[str] = []
    one = str(pattern or "").strip()
    if one:
        pats.append(one)
    for p in (patterns or []):
        s = str(p or "").strip()
        if s:
            pats.append(s)
    pats = [p for i, p in enumerate(pats) if p and p not in pats[:i]]
    if not pats:
        raise RuntimeError("At least one pattern is required.")

    hit_limit = _safe_int(max_matches, 100, min_value=1)

    def _grep_match_indices(lines: Sequence[str]) -> List[int]:
        if not lines:
            return []
        text = "\n".join(str(x) for x in lines)

        # Use native grep semantics for regex matching over extracted strings.
        grep_cmd: List[str] = ["grep", "-nE"]
        if not case_sensitive:
            grep_cmd.append("-i")
        for p in pats:
            grep_cmd.extend(["-e", p])

        def _parse_line_numbers(stdout: str) -> List[int]:
            out: List[int] = []
            seen_ln = set()
            for raw in (stdout or "").splitlines():
                token = raw.split(":", 1)[0].strip()
                try:
                    ln = int(token)
                except Exception:
                    continue
                if ln <= 0 or ln in seen_ln:
                    continue
                seen_ln.add(ln)
                out.append(ln)
                if len(out) >= hit_limit:
                    break
            return out

        try:
            grep_proc = subprocess.run(
                grep_cmd,
                input=text,
                text=True,
                capture_output=True,
                check=False,
            )
            # grep exits 0 on match, 1 on no match.
            if grep_proc.returncode in (0, 1):
                return _parse_line_numbers(grep_proc.stdout)
        except FileNotFoundError:
            pass

        # Fallback to ripgrep only if grep is unavailable.
        rg_cmd: List[str] = ["rg", "--line-number", "--no-heading", "--color", "never"]
        if not case_sensitive:
            rg_cmd.append("-i")
        for p in pats:
            rg_cmd.extend(["-e", p])
        try:
            rg_proc = subprocess.run(
                rg_cmd,
                input=text,
                text=True,
                capture_output=True,
                check=False,
            )
            if rg_proc.returncode in (0, 1):
                return _parse_line_numbers(rg_proc.stdout)
        except FileNotFoundError:
            return []
        return []

    results: List[Dict[str, Any]] = []
    total_searched = 0
    total_matched = 0
    matched_oids: List[str] = []
    for oo in scope:
        all_strings = _get_strings_for_oid(
            api,
            oo,
            max_strings=max_strings,
            min_len=min_len,
        )
        total_searched += len(all_strings)
        idxs = _grep_match_indices(all_strings)
        matched: List[str] = []
        for ln in idxs:
            i = ln - 1
            if i < 0 or i >= len(all_strings):
                continue
            matched.append(all_strings[i])
            if len(matched) >= hit_limit:
                break
        matched_count = len(matched)
        total_matched += matched_count
        if matched_count > 0:
            matched_oids.append(oo)
        results.append(
            {
                "oid": oo,
                "searched_strings": len(all_strings),
                "matched_count": matched_count,
                "matches": matched,
                "truncated": bool(matched_count >= hit_limit),
            }
        )

    results.sort(key=lambda x: int(x.get("matched_count", 0) or 0), reverse=True)
    return {
        "patterns": pats,
        "scope_size": len(scope),
        "results": results,
        "total_searched_strings": int(total_searched),
        "total_matched_strings": int(total_matched),
        "matched_oids": matched_oids,
        "matched_oid_count": len(matched_oids),
    }


def _parse_func_addr(func_id: str) -> Optional[int]:
    cands = _parse_func_addr_candidates(func_id)
    return cands[0] if cands else None


def _parse_func_addr_candidates(func_id: str) -> List[int]:
    s = str(func_id or "").strip()
    if not s:
        return []
    sl = s.lower()
    if not FUNC_ID_RE.search(s) and not sl.startswith("fun_"):
        return []
    token = s[5:] if s.lower().startswith("func_") else s
    from_fun_prefix = token.upper().startswith("FUN_")
    token = token[4:] if from_fun_prefix else token
    token = token.strip()
    if not token:
        return []
    out: List[int] = []
    seen = set()

    def _add(v: Optional[int]) -> None:
        if v is None:
            return
        iv = int(v)
        if iv in seen:
            return
        seen.add(iv)
        out.append(iv)

    try:
        if token.startswith(("0x", "0X")):
            _add(int(token, 16))
            return out
        if token.isdigit():
            # Ambiguous token: try decimal and hexadecimal forms.
            if from_fun_prefix:
                _add(int(token, 16))
                _add(int(token, 10))
            else:
                _add(int(token, 10))
                _add(int(token, 16))
            return out
        if all(ch in "0123456789abcdefABCDEF" for ch in token):
            _add(int(token, 16))
            return out
        _add(int(token, 10))
    except Exception:
        return out
    return out


def _function_name_from_meta(meta: Any) -> str:
    if isinstance(meta, dict):
        return str(meta.get("name") or "")
    if isinstance(meta, str):
        return str(meta)
    return ""


def _resolve_function_addr_from_name(names_by_addr: Dict[int, str], function_name: str) -> Optional[int]:
    want = str(function_name or "").strip()
    if not want:
        return None
    items = sorted((int(addr), str(name or "")) for addr, name in names_by_addr.items())
    for addr, name in items:
        if name == want:
            return addr

    want_short = want.split("::")[-1]
    for addr, name in items:
        if name.split("::")[-1] == want_short:
            return addr

    want_l = want.lower()
    for addr, name in items:
        if name.lower() == want_l:
            return addr
    return None


def _get_function_list_rows(api: Any, oid: str, max_functions: int) -> List[Dict[str, str]]:
    functions = api.get_field("ghidra_disasm", oid, "functions") or {}
    if not isinstance(functions, dict):
        return []

    by_addr: Dict[int, str] = {}
    for key, meta in functions.items():
        addr = _int_addr(key)
        if addr is None:
            continue
        addr_i = int(addr)
        name = _function_name_from_meta(meta)
        if addr_i not in by_addr:
            by_addr[addr_i] = name

    addrs = sorted(by_addr.keys())[:max_functions]
    rows = []
    for a in addrs:
        rows.append(
            {
                "func_id": f"func_{a:x}",
                "address": f"0x{a:x}",
                "function_addr": f"0x{a:x}",
                "function_name": str(by_addr.get(a) or ""),
            }
        )
    return rows


def _get_raw_call_graph(api: Any, oid: str) -> Dict[str, Any]:
    key = str(oid or "").strip()
    cached = CALL_GRAPH_CACHE.get(key)
    if cached is not None:
        return cached

    functions = api.get_field("ghidra_disasm", key, "functions") or {}
    addr_set = set()
    names_by_addr: Dict[int, str] = {}
    if isinstance(functions, dict):
        for k, meta in functions.items():
            addr = _int_addr(k)
            if addr is None:
                continue
            addr_i = int(addr)
            addr_set.add(addr_i)
            if addr_i not in names_by_addr:
                names_by_addr[addr_i] = _function_name_from_meta(meta)
    nodes = sorted(addr_set)

    call_map = api.retrieve("call_mapping", [key]) or {}
    if isinstance(call_map, dict) and len(call_map) == 1 and key in call_map and isinstance(call_map.get(key), dict):
        call_map = call_map.get(key) or {}
    if not isinstance(call_map, dict):
        call_map = {}

    edge_set = set()
    for caller_raw, rec in call_map.items():
        caller = _int_addr(caller_raw)
        if caller is None:
            continue
        caller_i = int(caller)
        if caller_i not in addr_set:
            continue
        entry = rec if isinstance(rec, dict) else {}
        callees = _iter_call_addrs(entry.get("calls_to") or entry.get("calls") or {})
        for callee in callees:
            callee_i = int(callee)
            if callee_i not in addr_set:
                continue
            edge_set.add((caller_i, callee_i))

    out = {
        "nodes": nodes,
        "edges": sorted(edge_set),
        "names_by_addr": names_by_addr,
    }
    CALL_GRAPH_CACHE[key] = out
    return out


def _normalize_decomp_text(raw: Any) -> str:
    if isinstance(raw, str):
        return raw
    if isinstance(raw, list):
        return "\n".join(str(x) for x in raw)
    if isinstance(raw, dict):
        if "decomp" in raw:
            return _normalize_decomp_text(raw.get("decomp"))
        return json.dumps(raw, ensure_ascii=False, indent=2)
    return str(raw)


def _get_func_decomp_text(
    api: Any,
    oid: str,
    *,
    func_addr: Optional[int] = None,
    func_name: str = "",
) -> str:
    opts: Dict[str, str] = {}
    name_s = str(func_name or "").strip()
    if name_s:
        opts["function_name"] = name_s
    elif func_addr is not None:
        opts["function_addr"] = str(int(func_addr))
    else:
        raise RuntimeError("Either func_addr or func_name is required.")

    out = api.retrieve("function_decomp", [oid], opts) or {}
    if isinstance(out, dict):
        if oid in out:
            return _normalize_decomp_text(out.get(oid))
        return _normalize_decomp_text(out)
    return _normalize_decomp_text(out)


def _extract_ranked_candidates(out: Any) -> List[Dict[str, Any]]:
    results = out.get("results") if isinstance(out, dict) else None
    raw_candidates = results.get("candidates") if isinstance(results, dict) else []
    candidates: List[Dict[str, Any]] = []
    if not isinstance(raw_candidates, list):
        return candidates

    for idx, cand in enumerate(raw_candidates, start=1):
        if not isinstance(cand, dict):
            continue
        oid_s = str(cand.get("oid") or "").strip()
        if not oid_s:
            continue
        row = dict(cand)
        row["oid"] = oid_s
        row["rank"] = int(idx)
        candidates.append(row)
    return candidates


def _normalize_oids_opt(raw: Any) -> List[str]:
    if raw is None:
        return []
    vals: List[Any]
    if isinstance(raw, str):
        s = raw.strip()
        if not s:
            return []
        parsed = None
        if s.startswith("[") and s.endswith("]"):
            try:
                parsed = json.loads(s)
            except Exception:
                parsed = None
        if isinstance(parsed, list):
            vals = list(parsed)
        else:
            vals = [x.strip() for x in s.split(",")]
    elif isinstance(raw, (list, tuple, set)):
        vals = list(raw)
        if vals and all(isinstance(x, str) and len(x) == 1 for x in vals):
            joined = "".join(vals).strip()
            if joined:
                return _normalize_oids_opt(joined)
    else:
        vals = [raw]
    out: List[str] = []
    for v in vals:
        s = str(v or "").strip()
        if s:
            out.append(s)
    return list(dict.fromkeys(out))


def run_retrieval_query(
    api: Any,
    cid: str,
    query: str,
    *,
    top_k: int = 10,
    offset: int = 0,
    retrieval_tool: str = "search_binaries",
    oids: Optional[Sequence[str]] = None,
    include_string_rankings: bool = True,
    strings_for_top_n_oids: int = 0,
    top_k_strings_per_oid: int = 25,
) -> Dict[str, Any]:
    """
    Shared retrieval helper used by both MCP and in-process agent runtimes.
    Returns ranked opaque candidate OIDs with stable schema.
    """
    cid_s = str(cid or "").strip()
    if not cid_s:
        raise RuntimeError("OXIDE_FUSE_EVAL_CID is not set for this run.")
    k_raw = _safe_int(top_k, 10)
    off = max(0, _safe_int(offset, 0, min_value=0))
    query_s = str(query or "")
    retrieval_backend = str(retrieval_tool or "").strip().lower()
    if retrieval_backend not in VALID_RETRIEVAL_TOOLS:
        retrieval_backend = "search_binaries"
    scope_oids = _normalize_oids_opt(oids or [])

    if retrieval_backend == "emb":
        k_fuse = max(0, int(k_raw) + off)
        all_exes = _filter_executable_oids(api, list(api.expand_oids(cid_s) or []))
        if not all_exes:
            return {"candidates": [], "total_candidates": 0, "offset": off}

        fuse_scope = list(all_exes)
        if scope_oids:
            allowed = set(all_exes)
            invalid = [x for x in scope_oids if x not in allowed]
            if invalid:
                raise RuntimeError(
                    "Invalid scope OID(s): "
                    + ", ".join(str(x) for x in invalid)
                    + ". OID scope must be executable OIDs in this collection."
                )
            scoped_set = set(scope_oids)
            fuse_scope = [x for x in all_exes if x in scoped_set]

        fuse_opts: Dict[str, Any] = {
            "prompt": query_s,
            "top_k": int(k_fuse),
            "include_string_rankings": bool(include_string_rankings),
            "strings_for_top_n_oids": int(strings_for_top_n_oids),
            "top_k_strings_per_oid": int(top_k_strings_per_oid),
        }
        out = api.retrieve("fuse", fuse_scope, fuse_opts) or {}
        if isinstance(out, dict) and out.get("error"):
            raise RuntimeError(str(out.get("error")))
        all_candidates = _extract_ranked_candidates(out)
        candidates = all_candidates[off:off + k_raw]
        return {
            "candidates": candidates,
            "total_candidates": len(all_candidates),
            "returned_count": len(candidates),
            "offset": off,
        }

    k_lexical = max(0, int(k_raw) + off)
    all_exes = _filter_executable_oids(api, list(api.expand_oids(cid_s) or []))
    if not all_exes:
        return {"candidates": [], "total_candidates": 0, "offset": off}

    bm25_opts: Dict[str, Any] = {
        "prompt": query_s,
        "top_k": int(k_lexical),
        "oids": list(scope_oids),
        "include_string_rankings": bool(include_string_rankings),
        "strings_for_top_n_oids": int(strings_for_top_n_oids),
        "top_k_strings_per_oid": int(top_k_strings_per_oid),
    }
    out = api.retrieve("bm25", all_exes, bm25_opts) or {}
    if isinstance(out, dict) and out.get("error"):
        raise RuntimeError(str(out.get("error")))
    all_candidates = _extract_ranked_candidates(out)
    candidates = all_candidates[off:off + k_raw]
    return {
        "candidates": candidates,
        "total_candidates": len(all_candidates),
        "returned_count": len(candidates),
        "offset": off,
    }


def run_function_list_query(api: Any, oid: str, *, max_functions: int = 50) -> List[Dict[str, str]]:
    """
    Shared function-list helper used by both MCP and in-process agent runtimes.
    """
    max_functions_i = _safe_int(max_functions, 50, min_value=1)
    return _get_function_list_rows(api, str(oid), max_functions_i)


def run_decompiled_function_query(
    api: Any,
    oid: str,
    *,
    function_name: str,
    max_chars: int = 2000,
) -> str:
    """
    Shared decompilation helper used by both MCP and in-process agent runtimes.
    """
    name_s = str(function_name or "").strip()
    if not name_s:
        raise RuntimeError("function_name is required.")

    text = _get_func_decomp_text(api, str(oid), func_name=name_s)

    cap = _safe_int(max_chars, 2000, min_value=64)
    if len(text) > cap:
        text = text[:cap] + "\n...[truncated]..."
    return text


def run_call_graph_query(
    api: Any,
    oid: str,
    *,
    function_name: str = "",
    func_id: str = "",
    max_functions: int = 200,
    max_edges: int = 1000,
) -> Dict[str, Any]:
    """
    Shared call-graph helper used by both MCP and in-process agent runtimes.
    Optional function_name (preferred) or func_id focuses output to one-hop
    callers/callees of that function.
    """
    oid_s = str(oid or "").strip()
    if not oid_s:
        raise RuntimeError("oid is required.")
    max_functions_i = _safe_int(max_functions, 200, min_value=1)
    max_edges_i = _safe_int(max_edges, 1000, min_value=1)

    raw = _get_raw_call_graph(api, oid_s)
    all_nodes = list(raw.get("nodes") or [])
    all_edges = list(raw.get("edges") or [])
    names_raw = raw.get("names_by_addr") or {}
    names_by_addr: Dict[int, str] = {}
    if isinstance(names_raw, dict):
        for k, v in names_raw.items():
            addr_i: Optional[int]
            if isinstance(k, int):
                addr_i = int(k)
            else:
                addr_i = _int_addr(k)
            if addr_i is None:
                continue
            names_by_addr[int(addr_i)] = str(v or "")

    focus_addr: Optional[int] = None
    focus_name = str(function_name or "").strip()
    focus_func = str(func_id or "").strip()
    if focus_name:
        focus_addr = _resolve_function_addr_from_name(names_by_addr, focus_name)
        if focus_addr is None:
            raise RuntimeError(f"Unknown function_name '{function_name}'")
    elif focus_func:
        focus_candidates = _parse_func_addr_candidates(focus_func)
        if not focus_candidates:
            raise RuntimeError(f"Invalid func_id '{func_id}'")
        node_set_all = {int(x) for x in all_nodes}
        for cand in focus_candidates:
            if int(cand) in node_set_all:
                focus_addr = int(cand)
                break
        if focus_addr is None:
            focus_addr = int(focus_candidates[0])

    if focus_addr is not None:
        edge_source = [(u, v) for (u, v) in all_edges if (u == focus_addr or v == focus_addr)]
        node_set = {int(focus_addr)}
        for u, v in edge_source:
            node_set.add(int(u))
            node_set.add(int(v))
        source_nodes = sorted(node_set)
    else:
        source_nodes = list(all_nodes)
        selected_set = set(source_nodes[:max_functions_i])
        edge_source = [(u, v) for (u, v) in all_edges if (u in selected_set and v in selected_set)]

    source_node_count_before_limit = len(source_nodes)
    source_nodes = source_nodes[:max_functions_i]
    if focus_addr is not None and source_nodes and int(focus_addr) not in set(source_nodes):
        source_nodes[-1] = int(focus_addr)
        source_nodes = sorted(set(source_nodes))
    node_set_final = set(source_nodes)
    edge_rows_raw = [(u, v) for (u, v) in edge_source if (u in node_set_final and v in node_set_final)]
    source_edge_count_before_limit = len(edge_rows_raw)
    edge_rows_raw = edge_rows_raw[:max_edges_i]

    nodes = [
        {
            "func_id": f"func_{a:x}",
            "address": f"0x{a:x}",
            "function_addr": f"0x{a:x}",
            "function_name": str(names_by_addr.get(int(a)) or ""),
        }
        for a in source_nodes
    ]
    edges = [
        {
            "caller_func_id": f"func_{u:x}",
            "caller_address": f"0x{u:x}",
            "caller_function_addr": f"0x{u:x}",
            "caller_function_name": str(names_by_addr.get(int(u)) or ""),
            "callee_func_id": f"func_{v:x}",
            "callee_address": f"0x{v:x}",
            "callee_function_addr": f"0x{v:x}",
            "callee_function_name": str(names_by_addr.get(int(v)) or ""),
        }
        for (u, v) in edge_rows_raw
    ]

    return {
        "oid": oid_s,
        "focus_func_id": (f"func_{int(focus_addr):x}" if focus_addr is not None else ""),
        "focus_function_addr": (f"0x{int(focus_addr):x}" if focus_addr is not None else ""),
        "focus_function_name": (str(names_by_addr.get(int(focus_addr)) or "") if focus_addr is not None else ""),
        "nodes": nodes,
        "edges": edges,
        "node_count": len(nodes),
        "edge_count": len(edges),
        "total_node_count": len(all_nodes),
        "total_edge_count": len(all_edges),
        "truncated_nodes": bool(source_node_count_before_limit > len(source_nodes)),
        "truncated_edges": bool(source_edge_count_before_limit > len(edge_rows_raw)),
    }


# ---- Deep-agent runtime (unified) ----
OXIDE_API_LOCK = threading.RLock()

OID_RE = re.compile(r"^[0-9a-fA-F]{40}$")
EVAL_TOOL_NAMES = {
    "search_functions",
    "search_binaries",
    "search_binaries_lexical",
    "search_binaries_semantic",
    "grep_strings",
    "get_function_list",
    "get_call_graph",
    "get_func_decomp",
}
RETRIEVAL_TOOL_NAMES = {
    "search_functions",
    "search_binaries",
    "search_binaries_lexical",
    "search_binaries_semantic",
}
INTERNAL_AGENT_TOOL_NAMES = {
    "write_todos",
    "read_todos",
}
TRANSIENT_LOCK_ERROR_MARKERS = (
    "bad file descriptor",
    "lockfile",
    "__collections.lock",
    "__src_type.lock",
    "__file_meta.lock",
    "unexpected os error trying to get lockfile",
)
TRANSIENT_RETRY_DELAYS_S = (0.10, 0.25)
TRANSIENT_MODEL_ERROR_MARKERS = (
    "500 internal server error",
    "httpx.remoteprotocolerror",
    "server disconnected without sending a response",
    "no data received from ollama stream",
    "connection reset",
    "connection aborted",
    "temporarily unavailable",
    "gateway timeout",
    "service unavailable",
)
TRANSIENT_MODEL_RETRY_DELAYS_S = (0.25, 0.50, 1.00)

# Context window for local Qwen3-coder models.
# deepagent checks model.profile["max_input_tokens"] to choose summarization
# thresholds. Without a profile it falls back to 170K trigger / 6-message keep,
# which causes the model to lose investigated-OID history on every summarization
# event. Providing the real context size switches it to fraction-based settings
# (85% trigger, 10% keep) which is far more appropriate for long sessions.
_QWEN3_CONTEXT_TOKENS = 131072

# Per-model-call HTTP timeout in seconds. Note: when Ollama streams tokens
# (including Qwen3 thinking tokens), httpx resets the read timeout on every
# chunk — so this only fires on truly stalled connections, not slow generation.
# Use num_predict to bound total output length instead.
_OLLAMA_CALL_TIMEOUT_S = 180

# Max output tokens per Ollama call. Qwen3 "thinking" models can generate
# thousands of reasoning tokens before a tool call. Capping this prevents
# per-call hangs and keeps the agent loop moving.
_OLLAMA_NUM_PREDICT = 8192


FINALIZER_RETRY_MESSAGE = (
    "Your structured output was invalid. Immediately call FinalizerOutput again with "
    "valid fields only: answer must be exactly 40 hexadecimal characters, reasoning "
    "must be 1-3 sentences, and confidence must be an integer from 1 to 5. "
    "Do not run additional analysis tools before resubmitting."
)

def _deep_agent_system() -> str:
    return (
        "You are identifying a binary in a firmware image. Use the available tools "
        "to find the best matching OID, then call FinalizerOutput with your best guess. "
        "Use the confidence score to "
        "reflect uncertainty. Do not keep searching once you have the most likely candidate.\n\n"
        "Submit your answer using FinalizerOutput with: answer (40 hex char OID), "
        "reasoning (1-3 sentences), and confidence (1-5)."
    )


class FinalizerOutput(BaseModel):
    answer: str = Field(
        min_length=40,
        max_length=40,
        pattern=OID_RE.pattern,
        description="The best binary OID as exactly 40 hexadecimal characters.",
    )
    reasoning: str = Field(
        min_length=1,
        max_length=4000,
        description="Concise justification in 1-3 sentences for the selected OID.",
    )
    confidence: int = Field(
        ge=1,
        le=5,
        description="Confidence score from 1 (low) to 5 (high).",
    )


@dataclass
class RuntimeState:
    trace_path: str
    started_at: float
    gold_oid: str
    gold_oids: Set[str] = field(default_factory=set)
    stop_reason: str = ""
    eval_tool_calls: int = 0
    non_eval_tool_calls: int = 0
    retrieve_calls: int = 0
    first_call_gold_rank_by_tool: Dict[str, Optional[int]] = field(default_factory=dict)
    per_tool: Dict[str, int] = field(default_factory=lambda: defaultdict(int))
    input_tokens: int = 0
    output_tokens: int = 0
    total_tokens: int = 0
    model_calls: int = 0
    model_errors: int = 0
    agent_text: str = ""
    structured_output: Any = None
    candidate_oids_seen: List[str] = field(default_factory=list)
    _candidate_oid_set: Set[str] = field(default_factory=set)

    @property
    def elapsed_s(self) -> float:
        return float(time.perf_counter() - self.started_at)

    @property
    def total_tool_calls(self) -> int:
        return int(self.eval_tool_calls + self.non_eval_tool_calls)

    def remember_candidates(self, oids: List[str]) -> None:
        for oid in oids or []:
            s = str(oid or "").strip()
            if not OID_RE.match(s):
                continue
            if s in self._candidate_oid_set:
                continue
            self._candidate_oid_set.add(s)
            self.candidate_oids_seen.append(s)

    def remember_first_call_gold_rank(self, tool_name: str, candidate_oids: List[str]) -> None:
        if tool_name not in RETRIEVAL_TOOL_NAMES:
            return
        if tool_name in self.first_call_gold_rank_by_tool:
            return
        gold_set = {str(x).strip() for x in (self.gold_oids or set()) if str(x).strip()}
        gold = str(self.gold_oid or "").strip()
        if gold:
            gold_set.add(gold)
        rank: Optional[int] = None
        if gold_set:
            for idx, oid in enumerate(candidate_oids or [], start=1):
                if str(oid or "").strip() in gold_set:
                    rank = int(idx)
                    break
        self.first_call_gold_rank_by_tool[tool_name] = rank


def _append_trace(path: str, event: Dict[str, Any]) -> None:
    _append_jsonl_event(path, event)


def _annotate_with_step(result: Any, step: int) -> Any:
    """Append a running step counter to tool results.

    Gives the model lightweight budget awareness that persists even after
    summarization events (the counter lives in the ToolMessage content, not
    in the AI message, so it is always part of the summarized history).
    """
    if isinstance(result, dict):
        return {**result, "_step": step}
    if isinstance(result, str):
        return f"{result}\n---\n[step {step}]"
    # Lists (e.g. get_function_list) are returned unchanged to preserve their schema.
    return result


def _truncate_text(value: Any, max_chars: int = 1200) -> str:
    text = str(value or "")
    if len(text) <= max_chars:
        return text
    return text[:max_chars] + "...[truncated]"


def _extract_text_content(content: Any) -> str:
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        parts: List[str] = []
        for item in content:
            if isinstance(item, str):
                parts.append(item)
            elif isinstance(item, dict):
                txt = item.get("text")
                if isinstance(txt, str):
                    parts.append(txt)
        return "\n".join([p for p in parts if p.strip()]).strip()
    return str(content or "")


def _extract_last_ai_text(messages: Any) -> str:
    if not isinstance(messages, list):
        return ""
    for msg in reversed(messages):
        if isinstance(msg, AIMessage):
            text = _extract_text_content(getattr(msg, "content", ""))
            if text.strip():
                return text.strip()
    for msg in reversed(messages):
        text = _extract_text_content(getattr(msg, "content", ""))
        if text.strip():
            return text.strip()
    return ""


def _extract_usage_from_message(message: Any) -> Tuple[int, int, int]:
    input_tokens = 0
    output_tokens = 0
    total_tokens = 0

    usage = getattr(message, "usage_metadata", None)
    if isinstance(usage, dict):
        input_tokens = int(usage.get("input_tokens") or 0)
        output_tokens = int(usage.get("output_tokens") or 0)
        total_tokens = int(usage.get("total_tokens") or 0)

    response_metadata = getattr(message, "response_metadata", None)
    if isinstance(response_metadata, dict):
        if input_tokens <= 0:
            input_tokens = int(response_metadata.get("prompt_eval_count") or 0)
        if output_tokens <= 0:
            output_tokens = int(response_metadata.get("eval_count") or 0)

    if total_tokens <= 0:
        total_tokens = max(0, input_tokens + output_tokens)
    return input_tokens, output_tokens, total_tokens


def _extract_usage_from_chat_result(output: Any) -> Tuple[int, int, int]:
    try:
        generations = getattr(output, "generations", None)
        if (
            isinstance(generations, list)
            and generations
            and isinstance(generations[0], list)
            and generations[0]
        ):
            msg = getattr(generations[0][0], "message", None)
            if msg is not None:
                return _extract_usage_from_message(msg)
    except Exception:
        pass
    return 0, 0, 0


def _reserve_tool_budget(state: RuntimeState, tool_name: str, params: Dict[str, Any]) -> float:
    state.eval_tool_calls += 1
    state.per_tool[tool_name] += 1
    if tool_name in RETRIEVAL_TOOL_NAMES:
        state.retrieve_calls += 1

    started = time.perf_counter()
    _append_trace(
        state.trace_path,
        {
            "event": "tool_start",
            "tool": tool_name,
            "params": params,
            "ts_unix_s": time.time(),
            "elapsed_s": state.elapsed_s,
        },
    )
    return started


def _finish_tool_success(
    state: RuntimeState,
    tool_name: str,
    started: float,
    result_meta: Optional[Dict[str, Any]] = None,
) -> None:
    dt = float(time.perf_counter() - started)
    _append_trace(
        state.trace_path,
        {
            "event": "tool_end",
            "tool": tool_name,
            "ok": True,
            "duration_s": dt,
            "result_meta": result_meta or {},
            "ts_unix_s": time.time(),
            "elapsed_s": state.elapsed_s,
        },
    )


def _finish_tool_error(
    state: RuntimeState,
    tool_name: str,
    started: float,
    error: Exception,
) -> None:
    dt = float(time.perf_counter() - started)
    _append_trace(
        state.trace_path,
        {
            "event": "tool_end",
            "tool": tool_name,
            "ok": False,
            "duration_s": dt,
            "error": repr(error),
            "ts_unix_s": time.time(),
            "elapsed_s": state.elapsed_s,
        },
    )


def _is_transient_lock_error(error: Exception) -> bool:
    text = repr(error).lower()
    return any(marker in text for marker in TRANSIENT_LOCK_ERROR_MARKERS)


def _is_transient_model_error(error: Exception) -> bool:
    status_code = getattr(error, "status_code", None)
    try:
        status_code_i = int(status_code)
    except Exception:
        status_code_i = 0
    if status_code_i in {429, 500, 502, 503, 504}:
        return True
    text = repr(error).lower()
    return any(marker in text for marker in TRANSIENT_MODEL_ERROR_MARKERS)


def _run_model_with_retry(
    *,
    state: RuntimeState,
    stage: str,
    fn: Callable[[], Any],
) -> Any:
    for attempt, delay_s in enumerate(TRANSIENT_MODEL_RETRY_DELAYS_S, start=1):
        try:
            return fn()
        except Exception as e:
            if not _is_transient_model_error(e):
                raise
            _append_trace(
                state.trace_path,
                {
                    "event": "model_retry",
                    "stage": stage,
                    "attempt": int(attempt),
                    "delay_s": float(delay_s),
                    "error": _truncate_text(repr(e), 400),
                    "elapsed_s": state.elapsed_s,
                    "ts_unix_s": time.time(),
                },
            )
            time.sleep(float(delay_s))
    return fn()


def _run_with_transient_retry(
    *,
    state: RuntimeState,
    tool_name: str,
    fn: Callable[[], Any],
) -> Any:
    for attempt, delay_s in enumerate(TRANSIENT_RETRY_DELAYS_S, start=1):
        try:
            return fn()
        except Exception as e:
            if not _is_transient_lock_error(e):
                raise
            _append_trace(
                state.trace_path,
                {
                    "event": "tool_retry",
                    "tool": tool_name,
                    "attempt": int(attempt),
                    "delay_s": float(delay_s),
                    "error": _truncate_text(repr(e), 400),
                    "elapsed_s": state.elapsed_s,
                    "ts_unix_s": time.time(),
                },
            )
            time.sleep(float(delay_s))
    return fn()


class AgentTraceCallback(BaseCallbackHandler):
    def __init__(self, state: RuntimeState):
        self.state = state
        self._model_start_ts: Dict[str, float] = {}
        self._model_end_seen: set[str] = set()

    def on_chat_model_start(
        self,
        serialized: Dict[str, Any],
        messages: List[Any],
        **kwargs: Any,
    ) -> None:
        run_id = str(kwargs.get("run_id") or kwargs.get("id") or f"model_{time.time()}")
        self._model_start_ts[run_id] = time.perf_counter()
        self.state.model_calls += 1
        _append_trace(
            self.state.trace_path,
            {
                "event": "model_start",
                "run_id": run_id,
                "message_count": len(messages or []),
                "serialized": _truncate_text(serialized, 1000),
                "ts_unix_s": time.time(),
                "elapsed_s": self.state.elapsed_s,
            },
        )

    def _record_model_end(self, output: Any, **kwargs: Any) -> None:
        run_id = str(kwargs.get("run_id") or kwargs.get("id") or "")
        if run_id and run_id in self._model_end_seen:
            return
        if run_id:
            self._model_end_seen.add(run_id)
        started = self._model_start_ts.get(run_id)
        dt = float(time.perf_counter() - started) if started else 0.0
        in_tok, out_tok, total_tok = _extract_usage_from_chat_result(output)
        self.state.input_tokens += max(0, int(in_tok))
        self.state.output_tokens += max(0, int(out_tok))
        self.state.total_tokens += max(0, int(total_tok))
        _append_trace(
            self.state.trace_path,
            {
                "event": "model_end",
                "run_id": run_id,
                "duration_s": dt,
                "usage": {
                    "input_tokens": int(in_tok),
                    "output_tokens": int(out_tok),
                    "total_tokens": int(total_tok),
                },
                "ts_unix_s": time.time(),
                "elapsed_s": self.state.elapsed_s,
            },
        )

    # Some LangChain versions dispatch chat completions via on_llm_end.
    def on_llm_end(self, response: Any, **kwargs: Any) -> None:
        self._record_model_end(response, **kwargs)

    # Keep this for compatibility with stacks that dispatch on_chat_model_end.
    def on_chat_model_end(self, output: Any, **kwargs: Any) -> None:
        self._record_model_end(output, **kwargs)

    def on_llm_error(self, error: BaseException, **kwargs: Any) -> None:
        self.state.model_errors += 1
        _append_trace(
            self.state.trace_path,
            {
                "event": "model_error",
                "error": repr(error),
                "ts_unix_s": time.time(),
                "elapsed_s": self.state.elapsed_s,
            },
        )

    def on_tool_start(self, serialized: Dict[str, Any], input_str: Any = None, **kwargs: Any) -> None:
        name = str((serialized or {}).get("name") or (serialized or {}).get("id") or "tool")
        if name in EVAL_TOOL_NAMES:
            return
        self.state.non_eval_tool_calls += 1
        _append_trace(
            self.state.trace_path,
            {
                "event": "internal_tool_start",
                "tool": name,
                "known_internal": bool(name in INTERNAL_AGENT_TOOL_NAMES),
                "input_preview": _truncate_text(input_str, 800),
                "ts_unix_s": time.time(),
                "elapsed_s": self.state.elapsed_s,
            },
        )


def _build_tools(
    *,
    state: RuntimeState,
    cid: str,
    profile: str,
) -> List[Any]:
    @tool(description=SEARCH_FUNCTIONS_DESCRIPTION)
    def search_functions(
        query: str,
        top_k: int = 10,
        offset: int = 0,
        oid: str = "",
        oids: Optional[List[str]] = None,
        search_mode: str = "semantic",
        similarity_threshold: float = 0.0,
    ) -> Dict[str, Any]:
        """Return functions ranked by semantic similarity to the query."""
        params = {
            "query": str(query or ""),
            "top_k": int(top_k),
            "offset": int(offset),
            "oid": str(oid or ""),
            "oids": list(oids or []),
            "search_mode": str(search_mode or "semantic"),
            "similarity_threshold": float(similarity_threshold),
        }
        started = _reserve_tool_budget(state, "search_functions", params)
        try:
            with OXIDE_API_LOCK:
                result = _run_with_transient_retry(
                    state=state,
                    tool_name="search_functions",
                    fn=lambda: run_search_functions_query(
                        api,
                        cid,
                        str(query or ""),
                        top_k=top_k,
                        offset=offset,
                        oid=str(oid or ""),
                        oids=list(oids or []),
                        search_mode=str(search_mode or "semantic"),
                        similarity_threshold=float(similarity_threshold),
                    ),
                )
            candidate_oids = [str(x or "") for x in (result.get("candidate_oids") or [])]
            state.remember_candidates(candidate_oids)
            state.remember_first_call_gold_rank("search_functions", candidate_oids)
            _finish_tool_success(
                state,
                "search_functions",
                started,
                {
                    "candidate_oids": candidate_oids,
                    "total_candidates": int(result.get("total_candidates", 0) or 0),
                    "total_files": int(result.get("total_files", 0) or 0),
                },
            )
            return _annotate_with_step(result, state.eval_tool_calls)
        except Exception as e:
            _finish_tool_error(state, "search_functions", started, e)
            raise

    def _search_binaries_impl(
        query: str,
        top_k: int = 10,
        offset: int = 0,
        *,
        tool_name: str = "search_binaries",
        backend_override: str = "",
        oids: Optional[List[str]] = None,
        include_string_rankings: bool = True,
        strings_for_top_n_oids: int = 0,
        top_k_strings_per_oid: int = 25,
    ) -> Dict[str, Any]:
        params = {
            "query": str(query or ""),
            "top_k": int(top_k),
            "offset": int(offset),
            "oids": list(oids or []),
            "include_string_rankings": bool(include_string_rankings),
            "strings_for_top_n_oids": int(strings_for_top_n_oids),
            "top_k_strings_per_oid": int(top_k_strings_per_oid),
        }
        started = _reserve_tool_budget(state, tool_name, params)
        retrieval_backend = backend_override or ("emb" if profile == "emb" else "bm25")
        try:
            with OXIDE_API_LOCK:
                result = _run_with_transient_retry(
                    state=state,
                    tool_name=tool_name,
                    fn=lambda: run_retrieval_query(
                        api,
                        cid,
                        str(query or ""),
                        top_k=top_k,
                        offset=offset,
                        retrieval_tool=retrieval_backend,
                        oids=list(oids or []),
                        include_string_rankings=bool(include_string_rankings),
                        strings_for_top_n_oids=int(strings_for_top_n_oids),
                        top_k_strings_per_oid=int(top_k_strings_per_oid),
                    ),
                )
            candidates = result.get("candidates") or []
            candidate_oids = [str(c.get("oid") or "") for c in candidates if isinstance(c, dict)]
            state.remember_candidates(candidate_oids)
            state.remember_first_call_gold_rank(tool_name, candidate_oids)
            _finish_tool_success(
                state,
                tool_name,
                started,
                {
                    "backend": retrieval_backend,
                    "candidate_oids": candidate_oids,
                    "total_candidates": len(candidates),
                },
            )
            return _annotate_with_step(result, state.eval_tool_calls)
        except Exception as e:
            _finish_tool_error(state, tool_name, started, e)
            raise

    if profile == "emb":

        @tool(description=SEARCH_BINARIES_SEMANTIC_DESCRIPTION)
        def search_binaries(
            query: str,
            top_k: int = 10,
            offset: int = 0,
            oids: Optional[List[str]] = None,
            include_string_rankings: bool = True,
            strings_for_top_n_oids: int = 0,
            top_k_strings_per_oid: int = 25,
        ) -> Dict[str, Any]:
            """Return candidate binary OIDs ranked semantically."""
            return _search_binaries_impl(
                query,
                top_k,
                offset,
                oids=oids,
                include_string_rankings=include_string_rankings,
                strings_for_top_n_oids=strings_for_top_n_oids,
                top_k_strings_per_oid=top_k_strings_per_oid,
            )

    else:

        @tool(description=SEARCH_BINARIES_LEXICAL_DESCRIPTION)
        def search_binaries(
            query: str,
            top_k: int = 10,
            offset: int = 0,
            oids: Optional[List[str]] = None,
            include_string_rankings: bool = True,
            strings_for_top_n_oids: int = 0,
            top_k_strings_per_oid: int = 25,
        ) -> Dict[str, Any]:
            """Return candidate binary OIDs ranked lexically (BM25)."""
            return _search_binaries_impl(
                query,
                top_k,
                offset,
                oids=oids,
                include_string_rankings=include_string_rankings,
                strings_for_top_n_oids=strings_for_top_n_oids,
                top_k_strings_per_oid=top_k_strings_per_oid,
            )

    if profile == "both":
        @tool("search_binaries_lexical", description=SEARCH_BINARIES_LEXICAL_DESCRIPTION)
        def search_binaries_lexical(
            query: str,
            top_k: int = 10,
            offset: int = 0,
            oids: Optional[List[str]] = None,
            include_string_rankings: bool = True,
            strings_for_top_n_oids: int = 0,
            top_k_strings_per_oid: int = 25,
        ) -> Dict[str, Any]:
            """Return candidate binary OIDs ranked lexically (BM25)."""
            return _search_binaries_impl(
                query,
                top_k,
                offset,
                tool_name="search_binaries_lexical",
                backend_override="bm25",
                oids=oids,
                include_string_rankings=include_string_rankings,
                strings_for_top_n_oids=strings_for_top_n_oids,
                top_k_strings_per_oid=top_k_strings_per_oid,
            )

        @tool("search_binaries_semantic", description=SEARCH_BINARIES_SEMANTIC_DESCRIPTION)
        def search_binaries_semantic(
            query: str,
            top_k: int = 10,
            offset: int = 0,
            oids: Optional[List[str]] = None,
            include_string_rankings: bool = True,
            strings_for_top_n_oids: int = 0,
            top_k_strings_per_oid: int = 25,
        ) -> Dict[str, Any]:
            """Return candidate binary OIDs ranked semantically."""
            return _search_binaries_impl(
                query,
                top_k,
                offset,
                tool_name="search_binaries_semantic",
                backend_override="emb",
                oids=oids,
                include_string_rankings=include_string_rankings,
                strings_for_top_n_oids=strings_for_top_n_oids,
                top_k_strings_per_oid=top_k_strings_per_oid,
            )

    @tool(description=GET_FUNCTION_LIST_DESCRIPTION)
    def get_function_list(oid: str, max_functions: int = 50) -> List[Dict[str, str]]:
        """Return function IDs and addresses for an OID."""
        params = {"oid": str(oid or ""), "max_functions": int(max_functions)}
        started = _reserve_tool_budget(state, "get_function_list", params)
        try:
            with OXIDE_API_LOCK:
                rows = _run_with_transient_retry(
                    state=state,
                    tool_name="get_function_list",
                    fn=lambda: run_function_list_query(
                        api,
                        str(oid),
                        max_functions=max_functions,
                    ),
                )
            _finish_tool_success(state, "get_function_list", started, {"count": len(rows)})
            return rows
        except Exception as e:
            _finish_tool_error(state, "get_function_list", started, e)
            raise

    @tool(description=GET_CALL_GRAPH_DESCRIPTION)
    def get_call_graph(
        oid: str,
        function_name: str = "",
        func_id: str = "",
        max_functions: int = 200,
        max_edges: int = 1000,
    ) -> Dict[str, Any]:
        """Return call graph with optional focus by function_name (preferred) or func_id."""
        params = {
            "oid": str(oid or ""),
            "function_name": str(function_name or ""),
            "func_id": str(func_id or ""),
            "max_functions": int(max_functions),
            "max_edges": int(max_edges),
        }
        started = _reserve_tool_budget(state, "get_call_graph", params)
        try:
            with OXIDE_API_LOCK:
                result = _run_with_transient_retry(
                    state=state,
                    tool_name="get_call_graph",
                    fn=lambda: run_call_graph_query(
                        api,
                        str(oid),
                        function_name=str(function_name or ""),
                        func_id=str(func_id or ""),
                        max_functions=max_functions,
                        max_edges=max_edges,
                    ),
                )
            _finish_tool_success(
                state,
                "get_call_graph",
                started,
                {
                    "node_count": int(result.get("node_count", 0) or 0),
                    "edge_count": int(result.get("edge_count", 0) or 0),
                    "focus_func_id": str(result.get("focus_func_id", "") or ""),
                    "focus_function_addr": str(result.get("focus_function_addr", "") or ""),
                    "focus_function_name": str(result.get("focus_function_name", "") or ""),
                },
            )
            return _annotate_with_step(result, state.eval_tool_calls)
        except Exception as e:
            _finish_tool_error(state, "get_call_graph", started, e)
            raise

    @tool(description=GREP_STRINGS_DESCRIPTION)
    def grep_strings(
        oid: str = "",
        oids: Optional[List[str]] = None,
        pattern: str = "",
        patterns: Optional[List[str]] = None,
        case_sensitive: bool = False,
        max_matches: int = 100,
        min_len: int = 4,
        max_strings: int = 400,
    ) -> Dict[str, Any]:
        """Run regex/exact matching over extracted strings for one OID, a list of OIDs, or all OIDs."""
        params = {
            "oid": str(oid or ""),
            "oids": list(oids or []),
            "pattern": str(pattern or ""),
            "patterns": patterns or [],
            "case_sensitive": bool(case_sensitive),
            "max_matches": int(max_matches),
            "min_len": int(min_len),
            "max_strings": int(max_strings),
        }
        started = _reserve_tool_budget(state, "grep_strings", params)
        try:
            with OXIDE_API_LOCK:
                result = _run_with_transient_retry(
                    state=state,
                    tool_name="grep_strings",
                    fn=lambda: run_grep_strings_query(
                        api,
                        str(oid),
                        oids=oids or [],
                        cid=cid,
                        pattern=str(pattern or ""),
                        patterns=patterns or [],
                        case_sensitive=bool(case_sensitive),
                        max_matches=max_matches,
                        min_len=min_len,
                        max_strings=max_strings,
                    ),
                )
            _finish_tool_success(
                state,
                "grep_strings",
                started,
                {
                    "scope_size": int(result.get("scope_size", 0) or 0),
                    "matched_oid_count": int(result.get("matched_oid_count", 0) or 0),
                    "total_matched_strings": int(result.get("total_matched_strings", 0) or 0),
                    "total_searched_strings": int(result.get("total_searched_strings", 0) or 0),
                },
            )
            return _annotate_with_step(result, state.eval_tool_calls)
        except Exception as e:
            _finish_tool_error(state, "grep_strings", started, e)
            raise

    @tool(description=GET_FUNC_DECOMP_DESCRIPTION)
    def get_func_decomp(
        oid: str,
        function_name: str,
        max_chars: int = 2000,
    ) -> str:
        """Return decompiled code for a function in an OID."""
        params = {
            "oid": str(oid or ""),
            "function_name": str(function_name or ""),
            "max_chars": int(max_chars),
        }
        started = _reserve_tool_budget(state, "get_func_decomp", params)
        try:
            with OXIDE_API_LOCK:
                text = _run_with_transient_retry(
                    state=state,
                    tool_name="get_func_decomp",
                    fn=lambda: run_decompiled_function_query(
                        api,
                        str(oid),
                        function_name=str(function_name or ""),
                        max_chars=max_chars,
                    ),
                )
            _finish_tool_success(
                state,
                "get_func_decomp",
                started,
                {"chars": len(text)},
            )
            return _annotate_with_step(text, state.eval_tool_calls)
        except Exception as e:
            _finish_tool_error(state, "get_func_decomp", started, e)
            raise

    @tool(description=GET_STRINGS_DESCRIPTION)
    def get_strings(
        oid: str,
        max_strings: int = 400,
        min_len: int = 4,
    ) -> List[str]:
        """Return all extracted strings for a binary OID."""
        params = {"oid": str(oid or ""), "max_strings": int(max_strings), "min_len": int(min_len)}
        started = _reserve_tool_budget(state, "get_strings", params)
        try:
            with OXIDE_API_LOCK:
                result = _get_strings_for_oid(api, str(oid or ""), max_strings=max_strings, min_len=min_len)
            _finish_tool_success(state, "get_strings", started, {"count": len(result)})
            return _annotate_with_step(result, state.eval_tool_calls)
        except Exception as e:
            _finish_tool_error(state, "get_strings", started, e)
            raise

    # Full function-level analysis toolkit — shared across all conditions
    func_toolkit = [search_functions, get_function_list, get_call_graph, get_func_decomp, grep_strings, get_strings]

    if profile == "both":
        tools = [search_binaries_lexical, search_binaries_semantic] + func_toolkit
    elif profile == "base":
        tools = list(func_toolkit)  # baseline: function-level only, no file-level retrieval
    elif profile == "emb":
        tools = [search_binaries] + func_toolkit
    else:  # bm25
        tools = [search_binaries] + func_toolkit
    return tools


def _normalize_answer(value: str) -> Tuple[str, bool]:
    answer = str(value or "").strip()
    if OID_RE.match(answer):
        return answer, False
    return "", True


def _normalize_confidence(value: Any) -> Tuple[int, bool]:
    try:
        out = int(value)
    except Exception:
        return 1, True
    if out < 1:
        return 1, True
    if out > 5:
        return 5, True
    return out, False


def _normalize_gold_oids(value: Any) -> List[str]:
    if value is None:
        return []
    raw_vals = value if isinstance(value, list) else [value]
    out: List[str] = []
    seen: Set[str] = set()
    for raw in raw_vals:
        oid = str(raw or "").strip()
        if not oid or oid in seen:
            continue
        seen.add(oid)
        out.append(oid)
    return out


def _coerce_finalizer_output(value: Any) -> FinalizerOutput:
    if isinstance(value, FinalizerOutput):
        return value
    if isinstance(value, BaseModel):
        return FinalizerOutput.model_validate(value.model_dump())
    if isinstance(value, dict):
        return FinalizerOutput.model_validate(value)
    return FinalizerOutput.model_validate(value)


def run_deep_agent_task(
    *,
    task: Dict[str, Any],
    condition: str,
    trace_path: str,
    agent_model: str,
    ollama_base_url: str,
    agent_recursion_limit: int,
) -> Dict[str, Any]:
    started = time.perf_counter()
    cid = str(task.get("cid") or "")
    gold_oid = str(task.get("gold_oid") or "").strip()
    gold_oids = _normalize_gold_oids(task.get("gold_oids"))
    if gold_oid and gold_oid not in gold_oids:
        gold_oids = [gold_oid] + [x for x in gold_oids if x != gold_oid]
    if (not gold_oid) and gold_oids:
        gold_oid = str(gold_oids[0]).strip()
    task_prompt = str(task.get("prompt") or "").strip()
    condition_norm = str(condition or "bm25").strip().lower()
    if condition_norm in {"baseline"}:
        condition_norm = "bm25"
    if condition_norm == "fuse":
        condition_norm = "emb"
    if condition_norm not in {"bm25", "emb", "both", "base"}:
        condition_norm = "bm25"
    state = RuntimeState(
        trace_path=trace_path,
        started_at=started,
        gold_oid=gold_oid,
        gold_oids=set(gold_oids),
    )
    Path(trace_path).parent.mkdir(parents=True, exist_ok=True)
    Path(trace_path).write_text("", encoding="utf-8")
    callback = AgentTraceCallback(state)

    answer = ""
    reasoning = ""
    confidence = 1
    parse_error = False
    stop_reason = ""
    runtime_error = ""
    raw_state: Dict[str, Any] = {}

    tools = _build_tools(
        state=state,
        cid=cid,
        profile=condition_norm,
    )

    prompt = f"What binary acts as {task_prompt}?"

    try:
        # Provide the model's context window size so deepagent uses fraction-based
        # summarization thresholds (85% trigger / 10% keep) instead of the default
        # 170K token trigger with 6-message keep. The 6-message fallback erases the
        # model's entire investigated-OID history on every summarization event.
        model = ChatOllama(
            model=agent_model,
            base_url=ollama_base_url,
            temperature=0.0,
            keep_alive=-1,
            num_predict=_OLLAMA_NUM_PREDICT,
            client_kwargs={"timeout": _OLLAMA_CALL_TIMEOUT_S},
            profile={"max_input_tokens": _QWEN3_CONTEXT_TOKENS},
        )

        agent = create_deep_agent(
            model=model,
            tools=tools,
            system_prompt=_deep_agent_system(),
            response_format=ToolStrategy(
                FinalizerOutput,
                handle_errors=FINALIZER_RETRY_MESSAGE,
            ),
            debug=False,
            name="fuse_eval_deep_agent",
        )
        attempt_prompts = [
            prompt,
            (
                f"{prompt}\n"
                "You must call at least one available tool before your final answer. "
                "Do not output pseudo tool-call tags."
            ),
        ]
        for attempt_idx, attempt_prompt in enumerate(attempt_prompts, start=1):
            out = _run_model_with_retry(
                state=state,
                stage="agent_invoke",
                fn=lambda p=attempt_prompt: agent.invoke(
                    {"messages": [HumanMessage(content=p)]},
                    config={
                        "callbacks": [callback],
                        "recursion_limit": int(max(1, agent_recursion_limit)),
                    },
                ),
            )
            if isinstance(out, dict):
                raw_state = out
                state.agent_text = _extract_last_ai_text(out.get("messages"))
                # Extract structured response directly if available
                structured = out.get("structured_response")
                if structured is not None:
                    state.structured_output = structured
            else:
                state.agent_text = _extract_text_content(out)
            if state.total_tool_calls > 0 or state.structured_output is not None:
                break
            if attempt_idx < len(attempt_prompts):
                _append_trace(
                    state.trace_path,
                    {
                        "event": "agent_retry_no_tool_calls",
                        "attempt": attempt_idx,
                        "elapsed_s": state.elapsed_s,
                        "ts_unix_s": time.time(),
                    },
                )

        if state.structured_output is not None:
            # Agent submitted structured answer directly — extract it
            parsed = _coerce_finalizer_output(state.structured_output)
            answer = parsed.answer
            reasoning = parsed.reasoning
            confidence = parsed.confidence
            _append_trace(state.trace_path, {
                "event": "structured_output_extracted",
                "answer": answer,
                "confidence": confidence,
                "reasoning_preview": reasoning[:200],
                "elapsed_s": state.elapsed_s,
                "ts_unix_s": time.time(),
            })
        else:
            # Agent stopped without structured output — try to extract from text
            reasoning = state.agent_text or "Agent did not provide structured output."
            confidence = 1
            parse_error = True
    except GraphRecursionError:
        state.stop_reason = "recursion_limit"
        reasoning = "Stopped due to recursion limit."
        confidence = 1
    except Exception as e:  # pragma: no cover
        runtime_error = repr(e)
        parse_error = True
        reasoning = "Agent execution failed before producing a valid answer."
        confidence = 1
        LOGGER.exception("Deep-agent run failed for task=%s condition=%s", task.get("task_id"), condition_norm)

    answer, bad_answer = _normalize_answer(answer)
    no_final_answer = False
    if bad_answer or (not answer):
        answer = ""
        no_final_answer = True
    confidence, bad_confidence = _normalize_confidence(confidence)
    if no_final_answer:
        confidence = 1
        _append_trace(
            state.trace_path,
            {
                "event": "missing_final_answer_no_fallback",
                "reason": "invalid_or_missing_final_answer",
                "elapsed_s": state.elapsed_s,
                "ts_unix_s": time.time(),
            },
        )
    parse_error = bool(parse_error or bad_answer or bad_confidence)
    answered_unknown = False
    if state.stop_reason:
        stop_reason = str(state.stop_reason)
    elif parse_error and not runtime_error:
        stop_reason = "finalizer_parse_error"
    elif runtime_error:
        stop_reason = "runtime_error"
    else:
        stop_reason = ""
    accepted_gold_oids = set(_normalize_gold_oids(gold_oids))
    if gold_oid:
        accepted_gold_oids.add(gold_oid)
    success = bool(answer and answer in accepted_gold_oids)
    success_strict = bool(answer and gold_oid and answer == gold_oid)
    wrong_answer = bool((not success) and (not answered_unknown))

    wall_time_s = float(f"{(time.perf_counter() - started):.6f}")
    first_rank_by_tool = dict(state.first_call_gold_rank_by_tool or {})
    row = {
        "success": bool(success),
        "success_any": bool(success),
        "success_strict": bool(success_strict),
        "wrong_answer": bool(wrong_answer),
        "answered_unknown": bool(answered_unknown),
        "parse_error": bool(parse_error),
        "retrieve_calls": int(state.retrieve_calls),
        "first_search_functions_gold_rank": first_rank_by_tool.get("search_functions"),
        "first_search_binaries_gold_rank": first_rank_by_tool.get("search_binaries"),
        "first_search_binaries_lexical_gold_rank": first_rank_by_tool.get("search_binaries_lexical"),
        "first_search_binaries_semantic_gold_rank": first_rank_by_tool.get("search_binaries_semantic"),
        "grep_strings_calls": int(state.per_tool.get("grep_strings", 0)),
        "get_function_list_calls": int(state.per_tool.get("get_function_list", 0)),
        "get_call_graph_calls": int(state.per_tool.get("get_call_graph", 0)),
        "get_func_decomp_calls": int(state.per_tool.get("get_func_decomp", 0)),
        "total_tool_calls": int(state.total_tool_calls),
        "input_tokens": int(state.input_tokens),
        "output_tokens": int(state.output_tokens),
        "total_tokens": int(state.total_tokens),
        "wall_time_s": wall_time_s,
        "answer": answer,
        "reasoning": reasoning,
        "confidence": int(confidence),
        "stop_reason": str(stop_reason),
        "runtime_error": runtime_error,
        "agent_text": state.agent_text,
        "gold_oids": sorted(accepted_gold_oids),
        "non_eval_tool_calls": int(state.non_eval_tool_calls),
        "raw_state_preview": _truncate_text(raw_state, 5000),
    }
    return row

# ---- Eval orchestrator (unified) ----
NAME = "fuse_agent_eval"
DEFAULT_OUTDIR = "out/agent_eval"
DEFAULT_AGENTIC_CONDITIONS = [
    "base",
    "bm25",
    "emb",
    "both",
]
# Note: "none" (no retrieval at all) is intentionally excluded — it is not
# part of the paper's evaluation design. base is the control baseline.
DEFAULT_AGENTIC_MODEL = "qwen3-coder-next:ca06e9e4087c"
DEFAULT_OLLAMA_BASE_URL = "http://localhost:11434"
DEFAULT_AGENTIC_TOP_K = 10
DEFAULT_AGENTIC_EXPECTED_PAIRS = 225
DEFAULT_AGENTIC_SERVER_PREFIX = "oxide_fuse_eval"
DEFAULT_AGENT_RECURSION_LIMIT = 500
FUNC_TOOLKIT_TOOL_NAMES = [
    "search_functions",
    "get_function_list",
    "get_call_graph",
    "get_func_decomp",
    "grep_strings",
    "get_strings",
]
EVAL_TOOLS_BY_CONDITION = {
    "base": list(FUNC_TOOLKIT_TOOL_NAMES),
    "bm25":     ["search_binaries"] + list(FUNC_TOOLKIT_TOOL_NAMES),
    "emb":      ["search_binaries"] + list(FUNC_TOOLKIT_TOOL_NAMES),
    "both":     ["search_binaries_lexical", "search_binaries_semantic"] + list(FUNC_TOOLKIT_TOOL_NAMES),
}
EVAL_TOOL_NAMES_LIST = sorted({x for vals in EVAL_TOOLS_BY_CONDITION.values() for x in vals})

LOGGER = logging.getLogger(NAME)
if not LOGGER.handlers:
    _handler = logging.StreamHandler()
    _handler.setFormatter(
        logging.Formatter(
            "[%(asctime)s] %(levelname)s %(name)s: %(message)s",
            "%H:%M:%S",
        )
    )
    LOGGER.addHandler(_handler)
LOGGER.setLevel(logging.INFO)
LOGGER.propagate = False

AGENTIC_RUN_DEFAULTS: Dict[str, Any] = {
    "outdir": DEFAULT_OUTDIR,
    "conditions": ",".join(DEFAULT_AGENTIC_CONDITIONS),
    "agent_model": DEFAULT_AGENTIC_MODEL,
    "ollama_base_url": DEFAULT_OLLAMA_BASE_URL,
    "agent_recursion_limit": DEFAULT_AGENT_RECURSION_LIMIT,
    "top_k": DEFAULT_AGENTIC_TOP_K,
    "run_topk5": False,
    "top_k_sensitivity": 5,
    "force_local_ollama": True,
    "allow_nonlocal_backend": False,
    "components": "",
    "collections": "",
    "task_ids": "",
    "max_tasks": 0,
    "fail_fast": False,
    "expected_pairs": DEFAULT_AGENTIC_EXPECTED_PAIRS,
    "mcp_server_name_prefix": DEFAULT_AGENTIC_SERVER_PREFIX,
    "log_progress": True,
    "log_every_n": 10,
    "log_level": "INFO",
}

DEFAULT_MAIN_AGENT_EVAL_OUTDIR = "out/agent_eval/main_9col"
DEFAULT_ROBUSTNESS_AGENT_EVAL_OUTDIR = "out/agent_eval/robustness_agent"
DEFAULT_AGENT_FIGURE_OUTDIR = "out/agent_eval/figures"
DEFAULT_ROBUSTNESS_AGENT_CONDITIONS = ["bm25", "emb", "both"]

# Standalone retrieval P@1 references used by the paper's delta columns.
# BOTH uses the better of BM25 and EMB, matching evaluation.tex.
MAIN_AGENT_P1_REFERENCE: Dict[str, Optional[float]] = {
    "base": float(56 / 225),
    "bm25": float(118 / 225),
    "emb": float(129 / 225),
    "both": float(129 / 225),
}

ROBUSTNESS_AGENT_P1_REFERENCE: Dict[str, Dict[str, float]] = {
    "dnsmasq": {
        "bm25": float(79 / 99),
        "emb": float(76 / 99),
    },
    "px5g-mbedtls": {
        "bm25": float(38 / 66),
        "emb": float(55 / 66),
    },
    "usign": {
        "bm25": float(49 / 99),
        "emb": float(92 / 99),
    },
    "dropbear": {
        "bm25": float(56 / 99),
        "emb": float(77 / 99),
    },
    "mtd": {
        "bm25": float(18 / 99),
        "emb": float(8 / 99),
    },
}

ROBUSTNESS_AGENT_COMPONENT_ORDER = [
    "dnsmasq",
    "px5g-mbedtls",
    "usign",
    "dropbear",
    "mtd",
]



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


def _with_defaults(opts: Dict[str, Any], defaults: Dict[str, Any]) -> Dict[str, Any]:
    merged = dict(defaults)
    for k, v in (opts or {}).items():
        if v is not None:
            merged[k] = v
    return merged


def _set_log_level(level_raw: Any) -> None:
    level_name = str(level_raw or "INFO").strip().upper()
    level = getattr(logging, level_name, logging.INFO)
    LOGGER.setLevel(level)


def _write_artifact(outdir: str, filename: str, payload: Dict[str, Any]) -> Optional[str]:
    outdir = str(outdir or "").strip()
    if not outdir:
        return None
    p = Path(outdir)
    p.mkdir(parents=True, exist_ok=True)
    target = p / filename
    target.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    return str(target)


def _resolve_outdir(opts: Dict[str, Any]) -> str:
    outdir = str(opts.get("outdir", DEFAULT_OUTDIR) or DEFAULT_OUTDIR).strip() or DEFAULT_OUTDIR

    # Default output path is timestamped to avoid clobbering previous runs.
    if Path(outdir).as_posix().rstrip("/") == Path(DEFAULT_OUTDIR).as_posix().rstrip("/"):
        ts = time.strftime("%Y%m%d_%H%M%S", time.localtime())
        base = Path(DEFAULT_OUTDIR)
        candidate = base / ts
        suffix = 1
        while candidate.exists():
            candidate = base / f"{ts}_{suffix:02d}"
            suffix += 1
        return str(candidate)
    return outdir


def _filter_executables(oids: List[str]) -> List[str]:
    return _filter_executable_oids(api, oids)


def _build_col_gt(exes: Sequence[str], basename_map: Dict[str, List[str]]) -> Dict[str, List[str]]:
    matched_by_basename: Dict[str, List[str]] = defaultdict(list)
    matched_seen_by_basename: Dict[str, Set[str]] = defaultdict(set)
    for oid in exes:
        oid_s = str(oid or "").strip()
        if not oid_s:
            continue
        for name in api.get_names_from_oid(oid_s):
            base = Path(str(name)).name.strip()
            if not base or oid_s in matched_seen_by_basename[base]:
                continue
            matched_seen_by_basename[base].add(oid_s)
            matched_by_basename[base].append(oid_s)

    col_gt: Dict[str, List[str]] = {}
    for component, basenames in basename_map.items():
        oids: List[str] = []
        seen_oids: Set[str] = set()
        for base in basenames:
            for oid_s in matched_by_basename.get(str(base).strip(), []):
                if oid_s in seen_oids:
                    continue
                seen_oids.add(oid_s)
                oids.append(oid_s)
        if oids:
            col_gt[component] = oids
    return col_gt


def _create_ground_truth(comp_path: str) -> Dict[str, Dict[str, List[str]]]:
    data = json.loads(Path(comp_path).read_text(encoding="utf-8"))
    ground_truth: Dict[str, Dict[str, List[str]]] = {}

    cids = api.collection_cids()
    if not cids:
        return {}

    for cid in cids:
        colname = api.get_colname_from_oid(cid)
        if colname not in data:
            continue
        collection_data = data[colname]
        basename_map: Dict[str, List[str]] = {}
        for component, paths in collection_data.items():
            if not isinstance(component, str):
                continue
            candidates = paths if isinstance(paths, list) else [paths]
            ordered_basenames: List[str] = []
            seen: Set[str] = set()
            for p in candidates:
                base = Path(str(p)).name.strip()
                if not base or base in seen:
                    continue
                seen.add(base)
                ordered_basenames.append(base)
            if ordered_basenames:
                basename_map[component] = ordered_basenames

        exes = _filter_executables(list(api.expand_oids(cid)))
        ground_truth[cid] = _build_col_gt(exes, basename_map)

    return ground_truth


def _get_required_path(opts: Dict[str, Any], *keys: str) -> Tuple[Optional[str], Optional[str]]:
    for key in keys:
        path = str(opts.get(key) or "").strip()
        if path:
            return path, None
    if not keys:
        return None, "No path option keys provided."
    if len(keys) == 1:
        return None, f"Provide {keys[0]}."
    return None, "Provide one of: " + ", ".join(keys) + "."


def _load_inputs(opts: Dict[str, Any]) -> Tuple[Optional[List[Dict[str, Any]]], Optional[str]]:
    comp_path, comp_err = _get_required_path(opts, "comp_path")
    if comp_err or comp_path is None:
        return None, "Provide comp_path."
    prompt_path, prompt_err = _get_required_path(opts, "prompt_path")
    if prompt_err or prompt_path is None:
        return None, "Provide prompt_path."

    try:
        gt = _create_ground_truth(comp_path)
    except Exception as e:
        return None, f"Failed to build ground truth from comp_path='{comp_path}': {e}"

    try:
        prompt_map_raw = json.loads(Path(prompt_path).read_text(encoding="utf-8"))
    except Exception as e:
        return None, f"Failed to load prompt_path='{prompt_path}': {e}"

    if not isinstance(prompt_map_raw, dict):
        return None, "prompt_path must map component -> prompt string."

    prompt_map: Dict[str, str] = {}
    for k, v in prompt_map_raw.items():
        if isinstance(k, str) and isinstance(v, str) and v.strip():
            prompt_map[k] = v.strip()

    tasks: List[Dict[str, Any]] = []
    for cid in sorted(gt.keys(), key=lambda c: api.get_colname_from_oid(c)):
        colname = api.get_colname_from_oid(cid)
        for component, raw_gold in sorted(gt[cid].items(), key=lambda kv: kv[0]):
            gold_oids = _normalize_gold_oids(raw_gold)
            if not gold_oids:
                continue
            gold_oid = gold_oids[0]
            prompt = prompt_map.get(component, "")
            if not prompt:
                continue
            tasks.append(
                {
                    "task_id": f"{cid}:{component}",
                    "cid": cid,
                    "collection": colname,
                    "component": component,
                    "prompt": prompt,
                    "gold_oid": gold_oid,
                    "gold_oids": gold_oids,
                }
            )

    return tasks, None


def _sanitize_name(value: str) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9._-]+", "_", str(value or ""))
    cleaned = cleaned.strip("._")
    return cleaned or "item"


def _normalize_conditions(opts: Dict[str, Any]) -> List[str]:
    raw = opts.get("conditions")
    if raw is None:
        return list(DEFAULT_AGENTIC_CONDITIONS)
    if isinstance(raw, str):
        items = [x.strip().lower() for x in raw.split(",") if x.strip()]
    elif isinstance(raw, (list, tuple)):
        items = [str(x).strip().lower() for x in raw if str(x).strip()]
    else:
        items = []
    if not items:
        return list(DEFAULT_AGENTIC_CONDITIONS)
    alias = {
        "baseline": "bm25",
        "fuse": "emb",
    }
    items = [alias.get(x, x) for x in items]
    allowed = {"bm25", "emb", "both", "base"}
    invalid = [x for x in items if x not in allowed]
    if invalid:
        raise ValueError(
            "Invalid conditions: "
            + ",".join(sorted(set(invalid)))
            + ". Valid conditions are base, bm25, emb, both."
        )
    out: List[str] = []
    for x in items:
        if x not in out:
            out.append(x)
    return out


def _parse_csv_values(value: Any) -> List[str]:
    if value is None:
        return []
    if isinstance(value, (list, tuple, set)):
        raw = [str(x).strip() for x in value if str(x).strip()]
    else:
        raw = [x.strip() for x in str(value).split(",") if x.strip()]
    return list(dict.fromkeys(raw))


def _apply_task_filters(
    tasks: Sequence[Dict[str, Any]],
    *,
    components: Sequence[str],
    collections: Sequence[str],
    task_ids: Sequence[str],
) -> List[Dict[str, Any]]:
    comp_set = {str(x).strip().lower() for x in components if str(x).strip()}
    col_set = {str(x).strip().lower() for x in collections if str(x).strip()}
    tid_set = {str(x).strip() for x in task_ids if str(x).strip()}

    out: List[Dict[str, Any]] = []
    for task in tasks:
        comp = str(task.get("component") or "").strip().lower()
        col = str(task.get("collection") or "").strip().lower()
        tid = str(task.get("task_id") or "").strip()
        if comp_set and comp not in comp_set:
            continue
        if col_set and col not in col_set:
            continue
        if tid_set and tid not in tid_set:
            continue
        out.append(task)
    return out


def _load_prompt_variants(
    path: str,
) -> Tuple[Optional[Dict[str, List[str]]], Optional[str]]:
    try:
        raw = json.loads(Path(path).read_text(encoding="utf-8"))
    except Exception as e:
        return None, f"Failed to load prompt_variants_path JSON: {e}"
    if not isinstance(raw, dict):
        return None, "prompt_variants_path must map component -> [variants]."
    out: Dict[str, List[str]] = {}
    for comp, vals in raw.items():
        if not isinstance(comp, str):
            continue
        if isinstance(vals, str):
            vals = [vals]
        if not isinstance(vals, list):
            continue
        norm = [str(v).strip() for v in vals if isinstance(v, str) and str(v).strip()]
        if norm:
            out[comp] = norm
    if not out:
        return None, "No usable variants in prompt_variants_path."
    return out, None


_ROBUSTNESS_COMPONENTS = ["dnsmasq", "dropbear", "mtd", "px5g-mbedtls", "usign"]


def _get_robustness_tasks(
    gt: Dict[str, Dict[str, Any]],
    variants_map: Dict[str, List[str]],
    *,
    components: Optional[Sequence[str]] = None,
) -> List[Dict[str, Any]]:
    """Build tasks from robustness variant set.

    Returns tasks for (components) x (variants) x (collections in gt).
    Each task has variant_idx and variant_prompt fields in addition to
    the standard task fields. component defaults to _ROBUSTNESS_COMPONENTS
    if not provided.
    """
    target_components = list(components) if components else list(_ROBUSTNESS_COMPONENTS)
    tasks: List[Dict[str, Any]] = []
    for cid in sorted(gt.keys(), key=lambda c: str(api.get_colname_from_oid(c) or c)):
        colname = api.get_colname_from_oid(cid)
        for component in target_components:
            gold_oids = _normalize_gold_oids(gt[cid].get(component))
            if not gold_oids:
                continue
            gold_oid = gold_oids[0]
            variant_prompts = variants_map.get(component, [])
            for idx, prompt in enumerate(variant_prompts):
                tasks.append({
                    "task_id": f"{cid}:{component}:v{idx}",
                    "cid": cid,
                    "collection": colname,
                    "component": component,
                    "prompt": prompt,
                    "gold_oid": gold_oid,
                    "gold_oids": gold_oids,
                    "variant_idx": idx,
                    "variant_prompt": prompt,
                    "task_set": "robustness",
                })
    return tasks


def _get_case_study_tasks(
    gt: Dict[str, Dict[str, Any]],
    variants_map: Dict[str, List[str]],
) -> List[Dict[str, Any]]:
    """Build tasks from case study variant set.

    Returns tasks for case study implementations x variants x collections in gt.
    """
    tasks: List[Dict[str, Any]] = []
    for cid in sorted(gt.keys(), key=lambda c: str(api.get_colname_from_oid(c) or c)):
        colname = api.get_colname_from_oid(cid)
        for component, raw_gold in sorted(gt[cid].items()):
            gold_oids = _normalize_gold_oids(raw_gold)
            if not gold_oids:
                continue
            gold_oid = gold_oids[0]
            variant_prompts = variants_map.get(component, [])
            for idx, prompt in enumerate(variant_prompts):
                tasks.append({
                    "task_id": f"{cid}:{component}:v{idx}",
                    "cid": cid,
                    "collection": colname,
                    "component": component,
                    "prompt": prompt,
                    "gold_oid": gold_oid,
                    "gold_oids": gold_oids,
                    "variant_idx": idx,
                    "variant_prompt": prompt,
                    "task_set": "case_study",
                })
    return tasks


def _load_inputs_for_mode(
    opts: Dict[str, Any],
) -> Tuple[Optional[List[Dict[str, Any]]], Optional[str]]:
    """Load tasks based on run mode: standard, robustness, or case_study.

    Options:
      robustness       -- bool: use robustness variant task set
      case_study       -- bool: use case study variant task set
      comp_path        -- standard ground truth path (robustness mode uses this)
      case_study_comp_path -- case study ground truth path
      prompt_variants_path -- variant descriptions JSON
      case_study_variants_path -- case study variant descriptions JSON
    """
    run_robustness = _as_bool(opts.get("robustness"), False)
    run_case_study = _as_bool(opts.get("case_study"), False)

    if run_robustness:
        comp_path, comp_err = _get_required_path(opts, "comp_path")
        if comp_err or comp_path is None:
            return None, "Provide comp_path for robustness mode."
        variants_path, variants_err = _get_required_path(opts, "prompt_variants_path", "variants_path")
        if variants_err or variants_path is None:
            return None, "Provide prompt_variants_path (or variants_path) for robustness mode."
        try:
            gt = _create_ground_truth(comp_path)
        except Exception as e:
            return None, f"Failed to build ground truth from comp_path='{comp_path}': {e}"
        variants_map, var_err = _load_prompt_variants(variants_path)
        if var_err or variants_map is None:
            return None, f"Failed loading prompt variants from '{variants_path}': {var_err}"
        tasks = _get_robustness_tasks(gt, variants_map)
        if not tasks:
            return None, "No robustness tasks generated (check comp_path and variants_path)."
        return tasks, None

    if run_case_study:
        cs_comp_path, cs_comp_err = _get_required_path(opts, "case_study_comp_path", "comp_path")
        if cs_comp_err or cs_comp_path is None:
            return None, "Provide case_study_comp_path (or comp_path) for case_study mode."
        cs_variants_path, cs_variants_err = _get_required_path(
            opts,
            "case_study_variants_path",
            "prompt_variants_path",
        )
        if cs_variants_err or cs_variants_path is None:
            return None, "Provide case_study_variants_path (or prompt_variants_path) for case_study mode."
        try:
            gt = _create_ground_truth(cs_comp_path)
        except Exception as e:
            return None, f"Failed to build case study ground truth from '{cs_comp_path}': {e}"
        if not gt:
            return None, f"No collections found matching case study ground truth at '{cs_comp_path}'."
        variants_map, var_err = _load_prompt_variants(cs_variants_path)
        if var_err or variants_map is None:
            return None, f"Failed loading case study variants from '{cs_variants_path}': {var_err}"
        tasks = _get_case_study_tasks(gt, variants_map)
        if not tasks:
            return None, "No case study tasks generated (check case_study_comp_path and case_study_variants_path)."
        return tasks, None

    # Standard mode
    return _load_inputs(opts)


def _run_agentic_task(
    *,
    task: Dict[str, Any],
    condition: str,
    run_id: str,
    top_k: int,
    trace_path: str,
    raw_output_path: str,
    agent_model: str,
    ollama_base_url: str,
    agent_recursion_limit: int,
) -> Dict[str, Any]:
    runtime = run_deep_agent_task(
        task=task,
        condition=condition,
        trace_path=trace_path,
        agent_model=agent_model,
        ollama_base_url=ollama_base_url,
        agent_recursion_limit=int(agent_recursion_limit),
    )

    raw_payload = {
        "run_id": run_id,
        "condition": condition,
        "task_id": task.get("task_id"),
        "runtime": "deep_agent",
        "runtime_result": runtime,
        "limits": {
            "agent_recursion_limit": int(agent_recursion_limit),
        },
        "model": {
            "agent_model": agent_model,
            "ollama_base_url": ollama_base_url,
        },
    }
    Path(raw_output_path).parent.mkdir(parents=True, exist_ok=True)
    Path(raw_output_path).write_text(json.dumps(raw_payload, indent=2), encoding="utf-8")

    row = {
        "run_id": run_id,
        "task_id": task.get("task_id"),
        "cid": task.get("cid"),
        "collection": task.get("collection"),
        "component": task.get("component"),
        "condition": condition,
        "top_k": int(top_k),
        "success": bool(runtime.get("success")),
        "success_any": bool(runtime.get("success_any", runtime.get("success"))),
        "success_strict": bool(runtime.get("success_strict", runtime.get("success"))),
        "wrong_answer": bool(runtime.get("wrong_answer")),
        "answered_unknown": bool(runtime.get("answered_unknown")),
        "parse_error": bool(runtime.get("parse_error")),
        "retrieve_calls": int(runtime.get("retrieve_calls", 0) or 0),
        "first_search_functions_gold_rank": runtime.get("first_search_functions_gold_rank"),
        "first_search_binaries_gold_rank": runtime.get("first_search_binaries_gold_rank"),
        "first_search_binaries_lexical_gold_rank": runtime.get("first_search_binaries_lexical_gold_rank"),
        "first_search_binaries_semantic_gold_rank": runtime.get("first_search_binaries_semantic_gold_rank"),
        "grep_strings_calls": int(runtime.get("grep_strings_calls", 0) or 0),
        "get_function_list_calls": int(runtime.get("get_function_list_calls", 0) or 0),
        "get_call_graph_calls": int(runtime.get("get_call_graph_calls", 0) or 0),
        "get_func_decomp_calls": int(runtime.get("get_func_decomp_calls", 0) or 0),
        "total_tool_calls": int(runtime.get("total_tool_calls", 0) or 0),
        "input_tokens": int(runtime.get("input_tokens", 0) or 0),
        "output_tokens": int(runtime.get("output_tokens", 0) or 0),
        "total_tokens": int(runtime.get("total_tokens", 0) or 0),
        "wall_time_s": float(runtime.get("wall_time_s", 0.0) or 0.0),
        "answer": str(runtime.get("answer", "") or ""),
        "reasoning": str(runtime.get("reasoning", "") or ""),
        "confidence": int(runtime.get("confidence", 1) or 1),
        "stop_reason": str(runtime.get("stop_reason", "") or ""),
        "gold_oid": str(task.get("gold_oid") or ""),
        "gold_oids": _normalize_gold_oids(task.get("gold_oids") or [task.get("gold_oid")]),
        "trace_path": trace_path,
        "raw_output_path": raw_output_path,
        "exit_code": 0 if not runtime.get("runtime_error") else 1,
        "runtime": "deep_agent",
        "non_eval_tool_calls": int(runtime.get("non_eval_tool_calls", 0) or 0),
    }
    return row


def _mean(values: Sequence[float]) -> float:
    if not values:
        return 0.0
    return float(sum(values) / max(len(values), 1))


def _median(values: Sequence[float]) -> float:
    if not values:
        return 0.0
    ordered = sorted(float(v) for v in values)
    mid = len(ordered) // 2
    if len(ordered) % 2 == 1:
        return float(ordered[mid])
    return float((ordered[mid - 1] + ordered[mid]) / 2.0)


def _quantile(values: Sequence[float], q: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(float(v) for v in values)
    if len(ordered) == 1:
        return float(ordered[0])
    frac = max(0.0, min(1.0, float(q)))
    idx = (len(ordered) - 1) * frac
    lo = int(math.floor(idx))
    hi = int(math.ceil(idx))
    if lo == hi:
        return float(ordered[lo])
    weight = idx - lo
    return float((ordered[lo] * (1.0 - weight)) + (ordered[hi] * weight))


def _agent_condition_label(condition: str) -> str:
    cond = str(condition or "").strip().lower()
    if not cond:
        return ""
    return AGENT_CONDITION_LABELS.get(cond, cond.upper())


def _agent_stop_reason(row: Dict[str, Any]) -> str:
    explicit = str(row.get("stop_reason") or "").strip().lower()
    if explicit:
        return explicit
    if bool(row.get("parse_error")):
        return "finalizer_parse_error"
    if bool(row.get("answered_unknown")):
        return "answered_unknown"
    return ""


def _is_agent_run_completed(row: Dict[str, Any]) -> bool:
    return not bool(_agent_stop_reason(row))


def _agent_run_outcome(row: Dict[str, Any]) -> str:
    if not _is_agent_run_completed(row):
        return "stopped"
    if bool(row.get("success")):
        return "success"
    return "wrong"


def _analysis_tool_call_count(row: Dict[str, Any]) -> int:
    return max(
        0,
        int(row.get("grep_strings_calls", 0) or 0)
        + int(row.get("get_function_list_calls", 0) or 0)
        + int(row.get("get_call_graph_calls", 0) or 0)
        + int(row.get("get_func_decomp_calls", 0) or 0),
    )


def _summarize_agentic_rows(rows: List[Dict[str, Any]], conditions: Sequence[str]) -> Dict[str, Any]:
    def _is_stopped(row: Dict[str, Any]) -> bool:
        # "stopped" captures non-completed trajectories.
        return not _is_agent_run_completed(row)

    def _to_pos_int(value: Any) -> Optional[int]:
        try:
            iv = int(value)
            if iv > 0:
                return iv
        except (TypeError, ValueError):
            pass
        return None

    def _rank_stats_for_field(
        rows_for_condition: List[Dict[str, Any]],
        field_name: str,
    ) -> Dict[str, Optional[float]]:
        total = len(rows_for_condition)
        if total <= 0:
            return {
                "hit_rate": 0.0,
                "mean_rank": None,
                "mean_rank_success": None,
                "mean_rank_non_success": None,
            }
        ranks_all: List[float] = []
        ranks_success: List[float] = []
        ranks_non_success: List[float] = []
        hit_count = 0
        for rr in rows_for_condition:
            rank_i = _to_pos_int(rr.get(field_name))
            if rank_i is None:
                continue
            hit_count += 1
            rank_f = float(rank_i)
            ranks_all.append(rank_f)
            if bool(rr.get("success")):
                ranks_success.append(rank_f)
            else:
                ranks_non_success.append(rank_f)
        return {
            "hit_rate": float(hit_count / max(total, 1)),
            "mean_rank": (_mean(ranks_all) if ranks_all else None),
            "mean_rank_success": (_mean(ranks_success) if ranks_success else None),
            "mean_rank_non_success": (_mean(ranks_non_success) if ranks_non_success else None),
        }

    def _fmt_opt(v: Optional[float]) -> Optional[float]:
        if v is None:
            return None
        return float(f"{float(v):.6f}")

    by_condition: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    for row in rows:
        _cond_key = str(row.get("condition") or "")
        if _cond_key == "fuse":
            _cond_key = "emb"
        by_condition[_cond_key].append(row)

    summary_rows: List[Dict[str, Any]] = []
    oracle_mean_tokens_all = 0.0
    oracle_mean_tokens_completed = 0.0
    oracle_rows = by_condition.get("oracle", [])
    if oracle_rows:
        oracle_mean_tokens_all = _mean(
            [float(r.get("total_tokens", 0) or 0) for r in oracle_rows]
        )
        oracle_completed = [
            r
            for r in oracle_rows
            if (not _is_stopped(r))
        ]
        oracle_mean_tokens_completed = _mean(
            [float(r.get("total_tokens", 0) or 0) for r in oracle_completed]
        )

    for condition in conditions:
        cond_rows = by_condition.get(condition, [])
        n = len(cond_rows)
        if n <= 0:
            summary_rows.append(
                {
                    "condition": condition,
                    "runs": 0,
                    "success_rate": 0.0,
                    "miss_rate": 0.0,
                    "stopped_rate": 0.0,
                    "stopped_runs": 0,
                    "mean_total_tokens": 0.0,
                    "mean_total_tokens_completed_only": 0.0,
                    "token_median": 0.0,
                    "token_p25": 0.0,
                    "token_p75": 0.0,
                    "token_p95": 0.0,
                    "mean_confidence_all": 0.0,
                    "mean_confidence_completed_only": 0.0,
                    "mean_tool_calls": 0.0,
                    "mean_retrieve_calls": 0.0,
                    "mean_analysis_tool_calls": 0.0,
                    "tc_p25": 0.0,
                    "tc_median": 0.0,
                    "tc_p75": 0.0,
                    "tc_p95": 0.0,
                    "stopped_recursion_limit": 0,
                    "stopped_parse_error": 0,
                    "stopped_runtime_error": 0,
                    "first_call_gold_hit_rate": 0.0,
                    "first_call_gold_mean_rank": None,
                    "first_call_gold_mean_rank_success": None,
                    "first_call_gold_mean_rank_non_success": None,
                    "first_call_gold_hit_rate_lexical": 0.0,
                    "first_call_gold_mean_rank_lexical": None,
                    "first_call_gold_mean_rank_success_lexical": None,
                    "first_call_gold_mean_rank_non_success_lexical": None,
                    "first_call_gold_hit_rate_semantic": 0.0,
                    "first_call_gold_mean_rank_semantic": None,
                    "first_call_gold_mean_rank_success_semantic": None,
                    "first_call_gold_mean_rank_non_success_semantic": None,
                    "token_multiplier_vs_oracle": None,
                    "token_multiplier_vs_oracle_completed_only": None,
                    "completed_runs": 0,
                    "zero_token_runs": 0,
                    "runs_with_zero_retrieve_calls": 0,
                    "runs_with_zero_eval_tool_calls": 0,
                    "stopped_reason_counts": {},
                }
            )
            continue

        stopped_rows = [r for r in cond_rows if _is_stopped(r)]
        completed_rows = [
            r
            for r in cond_rows
            if (not _is_stopped(r))
        ]
        success_count = sum(1 for r in cond_rows if (not _is_stopped(r)) and bool(r.get("success")))
        stopped_count = len(stopped_rows)
        miss_count = n - success_count - stopped_count
        token_values = [float(r.get("total_tokens", 0) or 0) for r in cond_rows]
        mean_tokens_all = _mean(
            token_values
        )
        mean_tokens_completed = _mean(
            [float(r.get("total_tokens", 0) or 0) for r in completed_rows]
        )
        token_median = _quantile(token_values, 0.5)
        token_p25 = _quantile(token_values, 0.25)
        token_p75 = _quantile(token_values, 0.75)
        token_p95 = _quantile(token_values, 0.95)
        tc_values = [float(r.get("total_tool_calls", 0) or 0) for r in cond_rows]
        mean_tool_calls = _mean(tc_values)
        tc_p25 = _quantile(tc_values, 0.25)
        tc_median = _quantile(tc_values, 0.5)
        tc_p75 = _quantile(tc_values, 0.75)
        tc_p95 = _quantile(tc_values, 0.95)
        mean_retrieve_calls = _mean([float(r.get("retrieve_calls", 0) or 0) for r in cond_rows])
        mean_confidence_all = _mean([float(r.get("confidence", 1) or 1) for r in cond_rows])
        mean_confidence_completed = _mean([float(r.get("confidence", 1) or 1) for r in completed_rows])
        mean_analysis_calls = _mean(
            [
                float(_analysis_tool_call_count(r))
                for r in cond_rows
            ]
        )
        first_rank_stats = {
            "hit_rate": 0.0,
            "mean_rank": None,
            "mean_rank_success": None,
            "mean_rank_non_success": None,
        }
        lexical_first_rank_stats = {
            "hit_rate": 0.0,
            "mean_rank": None,
            "mean_rank_success": None,
            "mean_rank_non_success": None,
        }
        semantic_first_rank_stats = {
            "hit_rate": 0.0,
            "mean_rank": None,
            "mean_rank_success": None,
            "mean_rank_non_success": None,
        }
        if condition == "base":
            first_rank_stats = _rank_stats_for_field(cond_rows, "first_search_functions_gold_rank")
        elif condition in {"bm25", "emb"}:
            first_rank_stats = _rank_stats_for_field(cond_rows, "first_search_binaries_gold_rank")
        elif condition == "both":
            lexical_first_rank_stats = _rank_stats_for_field(cond_rows, "first_search_binaries_lexical_gold_rank")
            semantic_first_rank_stats = _rank_stats_for_field(cond_rows, "first_search_binaries_semantic_gold_rank")
        zero_retrieve_calls = sum(1 for r in cond_rows if int(r.get("retrieve_calls", 0) or 0) <= 0)
        zero_eval_tool_calls = 0
        for r in cond_rows:
            total_calls = int(r.get("total_tool_calls", 0) or 0)
            non_eval_calls = int(r.get("non_eval_tool_calls", 0) or 0)
            eval_calls = max(0, total_calls - non_eval_calls)
            if eval_calls <= 0:
                zero_eval_tool_calls += 1
        stopped_reason_counts: Dict[str, int] = defaultdict(int)
        for r in stopped_rows:
            stopped_reason_counts[_agent_stop_reason(r) or "stopped_unknown"] += 1
        token_mult_all = (
            float(f"{(mean_tokens_all / oracle_mean_tokens_all):.6f}")
            if oracle_mean_tokens_all > 0.0
            else None
        )
        token_mult_completed = (
            float(f"{(mean_tokens_completed / oracle_mean_tokens_completed):.6f}")
            if oracle_mean_tokens_completed > 0.0
            else None
        )
        first_hit_rate = _fmt_opt(first_rank_stats.get("hit_rate"))
        if condition == "both":
            first_hit_rate = None
        summary_rows.append(
            {
                "condition": condition,
                "runs": n,
                "success_rate": float(f"{(success_count / n):.6f}"),
                "miss_rate": float(f"{(miss_count / n):.6f}"),
                "stopped_rate": float(f"{(stopped_count / n):.6f}"),
                "stopped_runs": int(stopped_count),
                "mean_total_tokens": float(f"{mean_tokens_all:.6f}"),
                "mean_total_tokens_completed_only": float(f"{mean_tokens_completed:.6f}"),
                "token_median": float(f"{token_median:.6f}"),
                "token_p25": float(f"{token_p25:.6f}"),
                "token_p75": float(f"{token_p75:.6f}"),
                "token_p95": float(f"{token_p95:.6f}"),
                "mean_confidence_all": float(f"{mean_confidence_all:.6f}"),
                "mean_confidence_completed_only": float(f"{mean_confidence_completed:.6f}"),
                "mean_tool_calls": float(f"{mean_tool_calls:.6f}"),
                "mean_retrieve_calls": float(f"{mean_retrieve_calls:.6f}"),
                "mean_analysis_tool_calls": float(f"{mean_analysis_calls:.6f}"),
                "tc_p25": float(f"{tc_p25:.6f}"),
                "tc_median": float(f"{tc_median:.6f}"),
                "tc_p75": float(f"{tc_p75:.6f}"),
                "tc_p95": float(f"{tc_p95:.6f}"),
                "stopped_recursion_limit": int(stopped_reason_counts.get("recursion_limit", 0)),
                "stopped_parse_error": int(stopped_reason_counts.get("finalizer_parse_error", 0)),
                "stopped_runtime_error": int(stopped_reason_counts.get("runtime_error", 0)),
                "first_call_gold_hit_rate": first_hit_rate,
                "first_call_gold_mean_rank": _fmt_opt(first_rank_stats.get("mean_rank")),
                "first_call_gold_mean_rank_success": _fmt_opt(first_rank_stats.get("mean_rank_success")),
                "first_call_gold_mean_rank_non_success": _fmt_opt(first_rank_stats.get("mean_rank_non_success")),
                "first_call_gold_hit_rate_lexical": _fmt_opt(lexical_first_rank_stats.get("hit_rate")) or 0.0,
                "first_call_gold_mean_rank_lexical": _fmt_opt(lexical_first_rank_stats.get("mean_rank")),
                "first_call_gold_mean_rank_success_lexical": _fmt_opt(
                    lexical_first_rank_stats.get("mean_rank_success")
                ),
                "first_call_gold_mean_rank_non_success_lexical": _fmt_opt(
                    lexical_first_rank_stats.get("mean_rank_non_success")
                ),
                "first_call_gold_hit_rate_semantic": _fmt_opt(semantic_first_rank_stats.get("hit_rate")) or 0.0,
                "first_call_gold_mean_rank_semantic": _fmt_opt(semantic_first_rank_stats.get("mean_rank")),
                "first_call_gold_mean_rank_success_semantic": _fmt_opt(
                    semantic_first_rank_stats.get("mean_rank_success")
                ),
                "first_call_gold_mean_rank_non_success_semantic": _fmt_opt(
                    semantic_first_rank_stats.get("mean_rank_non_success")
                ),
                "token_multiplier_vs_oracle": token_mult_all,
                "token_multiplier_vs_oracle_completed_only": token_mult_completed,
                "completed_runs": int(len(completed_rows)),
                "zero_token_runs": int(sum(1 for r in cond_rows if int(r.get("total_tokens", 0) or 0) <= 0)),
                "runs_with_zero_retrieve_calls": int(zero_retrieve_calls),
                "runs_with_zero_eval_tool_calls": int(zero_eval_tool_calls),
                "stopped_reason_counts": dict(stopped_reason_counts),
            }
        )

    by_collection: List[Dict[str, Any]] = []
    coll_cond: Dict[Tuple[str, str], List[Dict[str, Any]]] = defaultdict(list)
    for row in rows:
        _row_cond = str(row.get("condition") or "")
        if _row_cond == "fuse":
            _row_cond = "emb"
        key = (str(row.get("collection") or ""), _row_cond)
        coll_cond[key].append(row)
    for (collection, condition), cell in sorted(coll_cond.items(), key=lambda kv: (kv[0][0], kv[0][1])):
        n = len(cell)
        by_collection.append(
            {
                "collection": collection,
                "condition": condition,
                "runs": n,
                "success_rate": float(
                    f"{(sum(1 for r in cell if (not _is_stopped(r)) and bool(r.get('success'))) / max(n, 1)):.6f}"
                ),
                "miss_rate": float(
                    f"{(sum(1 for r in cell if (not _is_stopped(r)) and (not bool(r.get('success')))) / max(n, 1)):.6f}"
                ),
                "stopped_rate": float(
                    f"{(sum(1 for r in cell if _is_stopped(r)) / max(n, 1)):.6f}"
                ),
                "mean_total_tokens": float(
                    f"{_mean([float(r.get('total_tokens', 0) or 0) for r in cell]):.6f}"
                ),
                "mean_total_tokens_completed_only": float(
                    f"{_mean([float(r.get('total_tokens', 0) or 0) for r in cell if (not _is_stopped(r))]):.6f}"
                ),
                "mean_confidence_all": float(f"{_mean([float(r.get('confidence', 1) or 1) for r in cell]):.6f}"),
                "mean_tool_calls": float(f"{_mean([float(r.get('total_tool_calls', 0) or 0) for r in cell]):.6f}"),
            }
        )

    by_name = {
        str(r.get("condition") or ""): r
        for r in summary_rows
        if isinstance(r, dict) and str(r.get("condition") or "")
    }
    pairwise_vs_fuse: List[Dict[str, Any]] = []
    pairwise_vs_oracle: List[Dict[str, Any]] = []
    stopped_reason_counts_by_condition: Dict[str, Dict[str, int]] = {
        str(r.get("condition") or ""): dict(r.get("stopped_reason_counts") or {})
        for r in summary_rows
        if isinstance(r, dict)
    }
    ref_fuse = by_name.get("emb") or by_name.get("fuse")
    ref_oracle = by_name.get("oracle")
    for row in summary_rows:
        cond = str(row.get("condition") or "")
        if ref_fuse is not None:
            pairwise_vs_fuse.append(
                {
                    "condition": cond,
                    "reference": "emb",
                    "delta_success": float(
                        f"{(float(row.get('success_rate', 0.0) or 0.0) - float(ref_fuse.get('success_rate', 0.0) or 0.0)):.6f}"
                    ),
                    "delta_miss": float(
                        f"{(float(row.get('miss_rate', 0.0) or 0.0) - float(ref_fuse.get('miss_rate', 0.0) or 0.0)):.6f}"
                    ),
                    "delta_stopped": float(
                        f"{(float(row.get('stopped_rate', 0.0) or 0.0) - float(ref_fuse.get('stopped_rate', 0.0) or 0.0)):.6f}"
                    ),
                    "delta_mean_total_tokens": float(
                        f"{(float(row.get('mean_total_tokens', 0.0) or 0.0) - float(ref_fuse.get('mean_total_tokens', 0.0) or 0.0)):.6f}"
                    ),
                    "delta_mean_total_tokens_completed_only": float(
                        f"{(float(row.get('mean_total_tokens_completed_only', 0.0) or 0.0) - float(ref_fuse.get('mean_total_tokens_completed_only', 0.0) or 0.0)):.6f}"
                    ),
                    "delta_mean_tool_calls": float(
                        f"{(float(row.get('mean_tool_calls', 0.0) or 0.0) - float(ref_fuse.get('mean_tool_calls', 0.0) or 0.0)):.6f}"
                    ),
                }
            )
        if ref_oracle is not None:
            pairwise_vs_oracle.append(
                {
                    "condition": cond,
                    "reference": "oracle",
                    "delta_success": float(
                        f"{(float(row.get('success_rate', 0.0) or 0.0) - float(ref_oracle.get('success_rate', 0.0) or 0.0)):.6f}"
                    ),
                    "delta_miss": float(
                        f"{(float(row.get('miss_rate', 0.0) or 0.0) - float(ref_oracle.get('miss_rate', 0.0) or 0.0)):.6f}"
                    ),
                    "delta_stopped": float(
                        f"{(float(row.get('stopped_rate', 0.0) or 0.0) - float(ref_oracle.get('stopped_rate', 0.0) or 0.0)):.6f}"
                    ),
                    "delta_mean_total_tokens": float(
                        f"{(float(row.get('mean_total_tokens', 0.0) or 0.0) - float(ref_oracle.get('mean_total_tokens', 0.0) or 0.0)):.6f}"
                    ),
                    "delta_mean_total_tokens_completed_only": float(
                        f"{(float(row.get('mean_total_tokens_completed_only', 0.0) or 0.0) - float(ref_oracle.get('mean_total_tokens_completed_only', 0.0) or 0.0)):.6f}"
                    ),
                    "delta_mean_tool_calls": float(
                        f"{(float(row.get('mean_tool_calls', 0.0) or 0.0) - float(ref_oracle.get('mean_tool_calls', 0.0) or 0.0)):.6f}"
                    ),
                }
            )

    return {
        "summary": summary_rows,
        "by_collection": by_collection,
        "pairwise_vs_fuse": pairwise_vs_fuse,
        "pairwise_vs_oracle": pairwise_vs_oracle,
        "stopped_reason_counts_by_condition": stopped_reason_counts_by_condition,
    }


def _build_rank_divergence_analysis(rows: List[Dict[str, Any]], top_k: int = 10) -> Dict[str, Any]:
    """Join bm25 and emb per-run rows by task_id and compute the rank divergence analysis.

    Returns a dict with:
      joined_rows       -- one dict per query with both conditions' data (for CSV)
      excluded_count    -- queries missing one condition
      primary_partition -- metrics table keyed by emb_wins/tied_at_1/tied/both_missed_topk/bm25_wins
      bm25_wins_gap_split -- metrics for small (1-4) and large (5+) BM25 rank advantage
      bm25_wins_component_freq -- {component: count} for bm25_wins subset
    """
    top_k_plus_one = top_k + 1

    by_task: Dict[str, Dict[str, Any]] = {}
    for row in rows:
        cond = str(row.get("condition") or "")
        if cond not in ("bm25", "emb"):
            continue
        tid = str(row.get("task_id") or "")
        if not tid:
            continue
        by_task.setdefault(tid, {})[cond] = row

    joined: List[Dict[str, Any]] = []
    excluded = 0
    for tid, cond_map in sorted(by_task.items()):
        if "bm25" not in cond_map or "emb" not in cond_map:
            excluded += 1
            continue
        b = cond_map["bm25"]
        e = cond_map["emb"]
        bm25_rank = int(b.get("first_search_binaries_gold_rank") or top_k_plus_one)
        emb_rank  = int(e.get("first_search_binaries_gold_rank") or top_k_plus_one)
        rank_gap  = bm25_rank - emb_rank  # positive = EMB ranked better
        bm25_in_top_k = bm25_rank <= top_k
        emb_in_top_k = emb_rank <= top_k
        if bm25_in_top_k and emb_in_top_k and bm25_rank == emb_rank:
            rank_comparison = "tied_at_1" if bm25_rank == 1 else "tied"
        elif not bm25_in_top_k and not emb_in_top_k:
            rank_comparison = "both_missed_topk"
        elif emb_rank < bm25_rank:
            rank_comparison = "emb_wins"
        elif bm25_rank < emb_rank:
            rank_comparison = "bm25_wins"
        else:
            rank_comparison = "both_missed_topk"
        joined.append({
            "task_id":          tid,
            "component":        str(b.get("component") or tid.split(":")[1] if ":" in tid else ""),
            "collection":       str(b.get("collection") or ""),
            "bm25_rank":        bm25_rank,
            "emb_rank":         emb_rank,
            "bm25_in_top_k":    bm25_in_top_k,
            "emb_in_top_k":     emb_in_top_k,
            "rank_gap":         rank_gap,
            "rank_comparison":  rank_comparison,
            "bm25_outcome":     _agent_run_outcome(b),
            "emb_outcome":      _agent_run_outcome(e),
            "bm25_tokens":      int(b.get("total_tokens") or 0),
            "emb_tokens":       int(e.get("total_tokens") or 0),
            "bm25_tool_calls":  int(b.get("total_tool_calls") or 0),
            "emb_tool_calls":   int(e.get("total_tool_calls") or 0),
        })

    def _subset_metrics(subset: List[Dict[str, Any]]) -> Dict[str, Any]:
        n = len(subset)
        if n == 0:
            return {"n": 0}
        return {
            "n":                    n,
            "bm25_success_rate":    float(f"{sum(1 for r in subset if r['bm25_outcome'] == 'success') / n:.6f}"),
            "emb_success_rate":     float(f"{sum(1 for r in subset if r['emb_outcome']  == 'success') / n:.6f}"),
            "bm25_token_median":    _median([float(r["bm25_tokens"]) for r in subset]),
            "emb_token_median":     _median([float(r["emb_tokens"])  for r in subset]),
            "bm25_tool_call_median": _median([float(r["bm25_tool_calls"]) for r in subset]),
            "emb_tool_call_median":  _median([float(r["emb_tool_calls"])  for r in subset]),
        }

    emb_wins  = [r for r in joined if r["rank_comparison"] == "emb_wins"]
    tied_at_1 = [r for r in joined if r["rank_comparison"] == "tied_at_1"]
    tied      = [r for r in joined if r["rank_comparison"] == "tied"]
    both_missed_topk = [r for r in joined if r["rank_comparison"] == "both_missed_topk"]
    bm25_wins = [r for r in joined if r["rank_comparison"] == "bm25_wins"]
    bm25_small = [r for r in bm25_wins if -4 <= r["rank_gap"] <= -1]
    bm25_large = [r for r in bm25_wins if r["rank_gap"] <= -5]

    comp_freq: Dict[str, int] = {}
    for r in bm25_wins:
        comp = r["component"]
        comp_freq[comp] = comp_freq.get(comp, 0) + 1

    return {
        "excluded_count": excluded,
        "joined_rows": joined,
        "primary_partition": {
            "emb_wins":          _subset_metrics(emb_wins),
            "tied_at_1":         _subset_metrics(tied_at_1),
            "tied":              _subset_metrics(tied),
            "both_missed_topk":  _subset_metrics(both_missed_topk),
            "bm25_wins":         _subset_metrics(bm25_wins),
            "all":               _subset_metrics(joined),
        },
        "bm25_wins_gap_split": {
            "small_1_4": _subset_metrics(bm25_small),
            "large_5plus": _subset_metrics(bm25_large),
        },
        "bm25_wins_component_freq": dict(sorted(comp_freq.items(), key=lambda kv: -kv[1])),
    }


def _write_csv(path: str, rows: Sequence[Dict[str, Any]]) -> Optional[str]:
    if not rows:
        return None
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    keys: List[str] = []
    seen = set()
    for row in rows:
        for k in row.keys():
            if k in seen:
                continue
            seen.add(k)
            keys.append(str(k))
    with p.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=keys)
        w.writeheader()
        for row in rows:
            w.writerow(row)
    return str(p)


def agentic_eval_run_matrix(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Run all-task agentic matrix across retrieval conditions using deep-agent runtime.

    Main matrix: tasks x (base,bm25,emb,both)
    Optional sensitivity: rerun with top_k=5.

    Optional task filters:
      - components: comma-separated component names
      - collections: comma-separated collection names
      - args: collection CIDs/OIDs (e.g., `&collection_name` in shell)
      - task_ids: comma-separated exact task ids (<cid>:<component>)

    Run mode options:
      robustness    -- bool: use robustness variant task set (5 components x 11 variants x 9 collections)
      case_study    -- bool: use case study variant task set (SSH implementations x variants)
      prompt_variants_path -- path to variant descriptions JSON (used with robustness=True)
      case_study_comp_path -- path to case study ground truth JSON (used with case_study=True)
      case_study_variants_path -- path to case study variant descriptions JSON (used with case_study=True)
    """
    tasks, err = _load_inputs_for_mode(opts)
    if err:
        return {"error": err}
    if tasks is None:
        return {"error": "No tasks available."}

    cfg = _with_defaults(opts, AGENTIC_RUN_DEFAULTS)
    _set_log_level(cfg.get("log_level"))
    log_progress = _as_bool(cfg.get("log_progress"), True)
    log_every_n = _safe_int(cfg.get("log_every_n"), 10, min_value=1)
    try:
        conditions = _normalize_conditions(cfg)
    except ValueError as e:
        return {"error": str(e)}
    outdir = Path(_resolve_outdir(cfg)).resolve()
    outdir.mkdir(parents=True, exist_ok=True)
    model = str(cfg.get("agent_model", DEFAULT_AGENTIC_MODEL) or DEFAULT_AGENTIC_MODEL).strip()
    ollama_base_url = str(cfg.get("ollama_base_url", DEFAULT_OLLAMA_BASE_URL) or DEFAULT_OLLAMA_BASE_URL).strip()
    agent_recursion_limit = _safe_int(
        cfg.get("agent_recursion_limit"),
        DEFAULT_AGENT_RECURSION_LIMIT,
        min_value=1,
    )
    top_k = _safe_int(cfg.get("top_k"), DEFAULT_AGENTIC_TOP_K, min_value=1)
    run_topk5 = _as_bool(cfg.get("run_topk5"), False)
    top_k_sensitivity = _safe_int(cfg.get("top_k_sensitivity"), 5, min_value=1)
    force_local_ollama = _as_bool(cfg.get("force_local_ollama"), True)
    allow_nonlocal_backend = _as_bool(cfg.get("allow_nonlocal_backend"), False)
    max_tasks = _safe_int(cfg.get("max_tasks"), 0, min_value=0)
    fail_fast = _as_bool(cfg.get("fail_fast"), False)
    wall_start = time.perf_counter()
    filter_components = _parse_csv_values(
        cfg.get("components", cfg.get("include_components"))
    )
    filter_collections = _parse_csv_values(
        cfg.get("collections", cfg.get("include_collections"))
    )
    if args:
        arg_valid, _ = api.valid_oids(args)
        arg_cids = [
            str(oid or "").strip()
            for oid in arg_valid
            if str(oid or "").strip() and api.exists("collections", str(oid or "").strip())
        ]
        if not arg_cids:
            return {"error": "No valid collections found in args."}
        arg_collections = [
            str(api.get_colname_from_oid(cid) or "").strip()
            for cid in arg_cids
            if str(api.get_colname_from_oid(cid) or "").strip()
        ]
        filter_collections = list(dict.fromkeys(filter_collections + arg_collections))
    filter_task_ids = _parse_csv_values(
        cfg.get("task_ids", cfg.get("include_task_ids"))
    )
    filters_active = bool(filter_components or filter_collections or filter_task_ids)
    if filters_active:
        tasks = _apply_task_filters(
            tasks,
            components=filter_components,
            collections=filter_collections,
            task_ids=filter_task_ids,
        )
        if not tasks:
            return {
                "error": "Task filters matched zero tasks.",
                "filters": {
                    "components": filter_components,
                    "collections": filter_collections,
                    "task_ids": filter_task_ids,
                },
            }

    expected_pairs = _safe_int(cfg.get("expected_pairs"), DEFAULT_AGENTIC_EXPECTED_PAIRS, min_value=1)
    if (not filters_active) and expected_pairs > 0 and len(tasks) != expected_pairs:
        # Keep running but annotate mismatch for transparency.
        opts["_task_count_warning"] = f"task_count={len(tasks)} expected={expected_pairs}"

    if force_local_ollama and not allow_nonlocal_backend:
        allowed_prefixes = (
            "http://localhost:",
            "http://127.0.0.1:",
            "http://[::1]:",
            "https://localhost:",
            "https://127.0.0.1:",
            "https://[::1]:",
        )
        if not any(ollama_base_url.startswith(p) for p in allowed_prefixes):
            return {
                "error": (
                    "Privacy guard: ollama_base_url is non-local. "
                    "Set a localhost Ollama URL or pass allow_nonlocal_backend=true."
                ),
                "ollama_base_url": ollama_base_url,
            }

    selected = tasks[:max_tasks] if max_tasks > 0 else tasks
    planned_runs = len(selected) * len(conditions) * (2 if run_topk5 else 1)
    if log_progress:
        LOGGER.info(
            "agentic_eval_run_matrix: runtime=deep_agent tasks=%d conditions=%s top_k=%d run_topk5=%s planned_runs~%d",
            len(selected),
            ",".join(conditions),
            top_k,
            run_topk5,
            planned_runs,
        )
        if filters_active:
            LOGGER.info(
                "agentic_eval_run_matrix filters: components=%s collections=%s task_ids=%s",
                ",".join(filter_components) or "<none>",
                ",".join(filter_collections) or "<none>",
                ",".join(filter_task_ids) or "<none>",
            )

    cfg_by_condition: Dict[str, Dict[str, str]] = {}
    server_prefix = str(cfg.get("mcp_server_name_prefix", DEFAULT_AGENTIC_SERVER_PREFIX) or DEFAULT_AGENTIC_SERVER_PREFIX).strip()
    for condition in conditions:
        cfg_by_condition[condition] = {
            "config_path": "",
            "server_name": f"{server_prefix}_{condition}",
        }
        if log_progress:
            LOGGER.info(
                "prepared deep-agent condition=%s namespace=%s",
                condition,
                cfg_by_condition[condition]["server_name"],
            )

    top_k_values = [top_k]
    if run_topk5 and top_k_sensitivity not in top_k_values:
        top_k_values.append(top_k_sensitivity)

    all_runs: List[Dict[str, Any]] = []
    scenario_artifacts: List[Dict[str, Any]] = []
    run_index = 0
    total_completed = 0

    for top_k_value in top_k_values:
        scenario = f"topk{top_k_value}"
        scenario_rows: List[Dict[str, Any]] = []
        runs_path = outdir / f"agentic_runs_{scenario}.jsonl"
        traces_dir = outdir / "traces" / scenario
        raw_dir = outdir / "raw" / scenario
        traces_dir.mkdir(parents=True, exist_ok=True)
        raw_dir.mkdir(parents=True, exist_ok=True)
        if log_progress:
            LOGGER.info(
                "scenario start: %s (conditions=%d tasks_per_condition=%d)",
                scenario,
                len(conditions),
                len(selected),
            )

        with runs_path.open("w", encoding="utf-8") as jf:
            for condition in conditions:
                if log_progress:
                    LOGGER.info(
                        "scenario=%s condition=%s started (%d tasks)",
                        scenario,
                        condition,
                        len(selected),
                    )
                for task in selected:
                    run_index += 1
                    task_slug = _sanitize_name(str(task.get("task_id") or "task"))
                    run_id = f"{scenario}_{condition}_{run_index:06d}_{task_slug}"
                    trace_path = str((traces_dir / f"{run_id}.jsonl").resolve())
                    raw_output_path = str((raw_dir / f"{run_id}.json").resolve())
                    row = _run_agentic_task(
                        task=task,
                        condition=condition,
                        run_id=run_id,
                        top_k=top_k_value,
                        trace_path=trace_path,
                        raw_output_path=raw_output_path,
                        agent_model=model,
                        ollama_base_url=ollama_base_url,
                        agent_recursion_limit=agent_recursion_limit,
                    )
                    scenario_rows.append(row)
                    jf.write(json.dumps(row, ensure_ascii=False) + "\n")
                    total_completed += 1
                    if log_progress and (
                        total_completed == 1
                        or total_completed % log_every_n == 0
                        or row.get("parse_error")
                        or total_completed == planned_runs
                    ):
                        LOGGER.info(
                            "progress scenario=%s condition=%s global=%d/%d task=%s success=%s parse_error=%s tokens=%s retrieve_calls=%s",
                            scenario,
                            condition,
                            total_completed,
                            planned_runs,
                            row.get("task_id"),
                            row.get("success"),
                            row.get("parse_error"),
                            row.get("total_tokens"),
                            row.get("retrieve_calls"),
                        )
                    if fail_fast and row.get("parse_error"):
                        break
                if fail_fast and scenario_rows and scenario_rows[-1].get("parse_error"):
                    break
            if fail_fast and scenario_rows and scenario_rows[-1].get("parse_error"):
                break

        summary_pack = _summarize_agentic_rows(scenario_rows, conditions)
        summary_rows = summary_pack.get("summary") if isinstance(summary_pack, dict) else []
        by_collection_rows = summary_pack.get("by_collection") if isinstance(summary_pack, dict) else []
        pairwise_vs_fuse = summary_pack.get("pairwise_vs_fuse") if isinstance(summary_pack, dict) else []
        pairwise_vs_oracle = summary_pack.get("pairwise_vs_oracle") if isinstance(summary_pack, dict) else []
        stopped_reason_counts_by_condition = (
            summary_pack.get("stopped_reason_counts_by_condition") if isinstance(summary_pack, dict) else {}
        )

        rank_divergence = _build_rank_divergence_analysis(scenario_rows, top_k=top_k_value)

        summary_payload = {
            "analysis": "agentic_eval_run_matrix",
            "runtime": "deep_agent",
            "scenario": scenario,
            "top_k": top_k_value,
            "conditions": conditions,
            "model": model,
            "agent_model": model,
            "ollama_base_url": ollama_base_url,
            "task_count": len(selected),
            "run_count": len(scenario_rows),
            "summary": summary_rows,
            "by_collection": by_collection_rows,
            "pairwise_vs_fuse": pairwise_vs_fuse,
            "pairwise_vs_oracle": pairwise_vs_oracle,
            "stopped_reason_counts_by_condition": stopped_reason_counts_by_condition,
            "rank_divergence": {k: v for k, v in rank_divergence.items() if k != "joined_rows"},
            "runs_jsonl": str(runs_path),
            "mcp_configs": cfg_by_condition,
            "func_toolkit_tools": list(FUNC_TOOLKIT_TOOL_NAMES),
            "required_tools_by_condition": dict(EVAL_TOOLS_BY_CONDITION),
            "output_format": "json",
            "limits": {
                "agent_recursion_limit": agent_recursion_limit,
            },
            "filters": {
                "components": filter_components,
                "collections": filter_collections,
                "task_ids": filter_task_ids,
            },
            "defaults_used": {
                "conditions": ",".join(DEFAULT_AGENTIC_CONDITIONS),
                "agent_model": DEFAULT_AGENTIC_MODEL,
                "top_k": DEFAULT_AGENTIC_TOP_K,
                "ollama_base_url": DEFAULT_OLLAMA_BASE_URL,
                "agent_recursion_limit": DEFAULT_AGENT_RECURSION_LIMIT,
                "force_local_ollama": True,
                "mcp_server_name_prefix": DEFAULT_AGENTIC_SERVER_PREFIX,
            },
        }
        summary_path = outdir / f"agentic_summary_{scenario}.json"
        summary_path.write_text(json.dumps(summary_payload, indent=2), encoding="utf-8")
        summary_csv = _write_csv(str(outdir / f"agentic_summary_{scenario}.csv"), summary_rows if isinstance(summary_rows, list) else [])
        by_collection_csv = _write_csv(
            str(outdir / f"agentic_by_collection_{scenario}.csv"),
            by_collection_rows if isinstance(by_collection_rows, list) else [],
        )
        pairwise_fuse_csv = _write_csv(
            str(outdir / f"agentic_pairwise_vs_fuse_{scenario}.csv"),
            pairwise_vs_fuse if isinstance(pairwise_vs_fuse, list) else [],
        )
        pairwise_oracle_csv = _write_csv(
            str(outdir / f"agentic_pairwise_vs_oracle_{scenario}.csv"),
            pairwise_vs_oracle if isinstance(pairwise_vs_oracle, list) else [],
        )
        rank_div_path = outdir / f"agentic_rank_divergence_{scenario}.json"
        rank_div_path.write_text(json.dumps(rank_divergence, indent=2, default=str), encoding="utf-8")
        rank_div_csv = _write_csv(
            str(outdir / f"agentic_rank_divergence_{scenario}.csv"),
            rank_divergence.get("joined_rows") or [],
        )
        scenario_artifacts.append(
            {
                "scenario": scenario,
                "top_k": top_k_value,
                "runs_jsonl": str(runs_path),
                "summary_json": str(summary_path),
                "summary_csv": summary_csv,
                "by_collection_csv": by_collection_csv,
                "pairwise_vs_fuse_csv": pairwise_fuse_csv,
                "pairwise_vs_oracle_csv": pairwise_oracle_csv,
                "rank_divergence_json": str(rank_div_path),
                "rank_divergence_csv": rank_div_csv,
            }
        )
        all_runs.extend(scenario_rows)
        if log_progress:
            LOGGER.info(
                "scenario complete: %s runs=%d summary=%s",
                scenario,
                len(scenario_rows),
                summary_path,
            )

    final_payload: Dict[str, Any] = {
        "analysis": "agentic_eval_run_matrix",
        "runtime": "deep_agent",
        "conditions": conditions,
        "model": model,
        "agent_model": model,
        "ollama_base_url": ollama_base_url,
        "task_count": len(selected),
        "expected_pairs": expected_pairs,
        "top_k_values": top_k_values,
        "run_count": len(all_runs),
        "output_format": "json",
        "limits": {
            "agent_recursion_limit": agent_recursion_limit,
        },
        "artifacts": scenario_artifacts,
        "mcp_configs": cfg_by_condition,
        "func_toolkit_tools": list(FUNC_TOOLKIT_TOOL_NAMES),
        "required_tools_by_condition": dict(EVAL_TOOLS_BY_CONDITION),
        "filters": {
            "components": filter_components,
            "collections": filter_collections,
            "task_ids": filter_task_ids,
        },
        "selected_tasks": [
            {
                "task_id": str(t.get("task_id") or ""),
                "collection": str(t.get("collection") or ""),
                "component": str(t.get("component") or ""),
            }
            for t in selected
        ],
        "defaults_used": {
            "outdir": DEFAULT_OUTDIR,
            "conditions": ",".join(DEFAULT_AGENTIC_CONDITIONS),
            "agent_model": DEFAULT_AGENTIC_MODEL,
            "top_k": DEFAULT_AGENTIC_TOP_K,
            "run_topk5": False,
            "ollama_base_url": DEFAULT_OLLAMA_BASE_URL,
            "agent_recursion_limit": DEFAULT_AGENT_RECURSION_LIMIT,
            "force_local_ollama": True,
            "allow_nonlocal_backend": False,
            "expected_pairs": DEFAULT_AGENTIC_EXPECTED_PAIRS,
            "mcp_server_name_prefix": DEFAULT_AGENTIC_SERVER_PREFIX,
        },
    }
    warning = str(opts.get("_task_count_warning", "") or "").strip()
    if warning:
        final_payload["warning"] = warning
    artifact = _write_artifact(str(outdir), "agentic_eval_matrix_manifest.json", final_payload)
    if artifact:
        final_payload["artifact"] = artifact
    if log_progress:
        LOGGER.info(
            "agentic_eval_run_matrix complete runs=%d elapsed_s=%.2f manifest=%s",
            len(all_runs),
            time.perf_counter() - wall_start,
            artifact or "<none>",
        )
    return final_payload

# ---------------------------------------------------------------------------
# Paper report helpers
# ---------------------------------------------------------------------------

def _load_agentic_rows_from_jsonl(path: Path) -> List[Dict[str, Any]]:
    """Load per-run rows from a JSONL file, skipping blank or malformed lines."""
    rows: List[Dict[str, Any]] = []
    try:
        for line in path.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
                if isinstance(obj, dict):
                    rows.append(obj)
            except json.JSONDecodeError:
                continue
    except Exception:
        pass
    return rows


def _load_agentic_summary_bundle(
    outdir: Path,
    scenario: str,
    conditions: Sequence[str],
) -> Tuple[Optional[Dict[str, Any]], Optional[List[Dict[str, Any]]], Optional[Path], Optional[str]]:
    summary_path = outdir / f"agentic_summary_{scenario}.json"
    runs_path = outdir / f"agentic_runs_{scenario}.jsonl"
    summary_payload: Optional[Dict[str, Any]] = None
    rows: Optional[List[Dict[str, Any]]] = None

    if summary_path.exists():
        try:
            loaded = json.loads(summary_path.read_text(encoding="utf-8"))
        except Exception as e:
            return None, None, None, f"Failed to read {summary_path}: {e}"
        if not isinstance(loaded, dict):
            return None, None, None, f"Expected JSON object in {summary_path}"
        summary_payload = dict(loaded)

    if runs_path.exists():
        rows = _load_agentic_rows_from_jsonl(runs_path)
        if not rows:
            return None, None, None, f"No valid rows in {runs_path}"
        summary_pack = _summarize_agentic_rows(rows, conditions)
        if summary_payload is None:
            summary_payload = {
                "scenario": scenario,
                "conditions": list(conditions),
            }
        summary_payload.update(summary_pack)
        summary_payload["task_count"] = len({r.get("task_id") for r in rows})
        summary_payload["run_count"] = len(rows)

    if summary_payload is None:
        return None, None, None, None
    return summary_payload, rows, runs_path if runs_path.exists() else None, None


def _main_agent_p1_reference(condition: str) -> Optional[float]:
    return MAIN_AGENT_P1_REFERENCE.get(str(condition or "").strip().lower())


def _robustness_agent_p1_reference(component: str, condition: str) -> Optional[float]:
    comp_key = str(component or "").strip().lower()
    cond_key = str(condition or "").strip().lower()
    refs = ROBUSTNESS_AGENT_P1_REFERENCE.get(comp_key)
    if not refs:
        return None
    if cond_key == "both":
        values = [float(v) for v in refs.values()]
        return max(values) if values else None
    return refs.get(cond_key)


def _per_component_agent_wide_table(
    rows: List[Dict[str, Any]],
    conditions: Sequence[str],
) -> List[Dict[str, Any]]:
    long_rows = _per_component_agent_summary(rows, list(conditions))
    by_component: Dict[str, Dict[str, Any]] = {}
    for row in long_rows:
        comp = str(row.get("component") or "").strip()
        cond = str(row.get("condition") or "").strip()
        if not comp or not cond:
            continue
        entry = by_component.setdefault(
            comp,
            {
                "component": comp,
                "base_success_rate": None,
                "bm25_success_rate": None,
                "emb_success_rate": None,
                "both_success_rate": None,
            },
        )
        entry[f"{cond}_success_rate"] = row.get("success_rate")
    return [by_component[comp] for comp in sorted(by_component)]


def _paper_first_call_rank_row(condition: str, summary_row: Dict[str, Any]) -> Dict[str, Any]:
    row: Dict[str, Any] = {
        "condition": condition,
        "mean_total_calls": summary_row.get("mean_tool_calls"),
        "first_call_gold_hit_rate": summary_row.get("first_call_gold_hit_rate"),
        "first_call_gold_mean_rank": summary_row.get("first_call_gold_mean_rank"),
        "first_call_gold_mean_rank_success": summary_row.get("first_call_gold_mean_rank_success"),
        "first_call_gold_mean_rank_non_success": summary_row.get("first_call_gold_mean_rank_non_success"),
        "first_call_gold_hit_rate_lexical": None,
        "first_call_gold_mean_rank_lexical": None,
        "first_call_gold_hit_rate_semantic": None,
        "first_call_gold_mean_rank_semantic": None,
    }
    if condition == "both":
        row["first_call_gold_hit_rate_lexical"] = summary_row.get("first_call_gold_hit_rate_lexical")
        row["first_call_gold_mean_rank_lexical"] = summary_row.get("first_call_gold_mean_rank_lexical")
        row["first_call_gold_hit_rate_semantic"] = summary_row.get("first_call_gold_hit_rate_semantic")
        row["first_call_gold_mean_rank_semantic"] = summary_row.get("first_call_gold_mean_rank_semantic")
        row["first_call_gold_mean_rank_success_lexical"] = summary_row.get(
            "first_call_gold_mean_rank_success_lexical"
        )
        row["first_call_gold_mean_rank_non_success_lexical"] = summary_row.get(
            "first_call_gold_mean_rank_non_success_lexical"
        )
        row["first_call_gold_mean_rank_success_semantic"] = summary_row.get(
            "first_call_gold_mean_rank_success_semantic"
        )
        row["first_call_gold_mean_rank_non_success_semantic"] = summary_row.get(
            "first_call_gold_mean_rank_non_success_semantic"
        )
    return row


def _first_call_rank_field_for_condition(condition: str) -> str:
    """Return the JSONL field name for first-call gold rank for a given condition."""
    if condition == "base":
        return "first_search_functions_gold_rank"
    if condition in ("bm25", "emb"):
        return "first_search_binaries_gold_rank"
    # both: pick the best (minimum) of lexical and semantic
    return "_first_call_rank_both"


def _first_call_rank_bucket(rank: Optional[int]) -> str:
    if rank is None:
        return "miss"
    if rank == 1:
        return "1"
    if rank <= 5:
        return "2-5"
    return "miss"


def _rank_bucket_success_table(
    rows: List[Dict[str, Any]],
    conditions: List[str],
) -> List[Dict[str, Any]]:
    """Compute success rate conditioned on first-call rank bucket per condition.

    Bucket definitions: rank=1, rank in 2-5, miss (rank>5 or None).
    Returns rows: [{condition, bucket, n, success_rate}]
    """
    def _get_rank(row: Dict[str, Any], condition: str) -> Optional[int]:
        if condition == "both":
            lex = row.get("first_search_binaries_lexical_gold_rank")
            sem = row.get("first_search_binaries_semantic_gold_rank")
            vals = [v for v in [lex, sem] if isinstance(v, int) and v > 0]
            return min(vals) if vals else None
        field = _first_call_rank_field_for_condition(condition)
        val = row.get(field)
        if isinstance(val, int) and val > 0:
            return val
        return None

    # Group by (condition, bucket)
    groups: Dict[Tuple[str, str], List[bool]] = defaultdict(list)
    for row in rows:
        cond = str(row.get("condition") or "")
        if cond == "fuse":
            cond = "emb"
        if cond not in conditions:
            continue
        rank = _get_rank(row, cond)
        bucket = _first_call_rank_bucket(rank)
        groups[(cond, bucket)].append(bool(row.get("success")))

    result: List[Dict[str, Any]] = []
    bucket_order = ["1", "2-5", "miss"]
    for cond in conditions:
        for bucket in bucket_order:
            successes = groups.get((cond, bucket), [])
            n = len(successes)
            rate = float(sum(successes) / max(n, 1)) if n > 0 else None
            result.append({
                "condition": cond,
                "bucket": bucket,
                "n": n,
                "success_rate": rate,
            })
    return result


def _per_component_agent_summary(
    rows: List[Dict[str, Any]],
    conditions: List[str],
) -> List[Dict[str, Any]]:
    """Compute per-component agent metrics for the dual-frame table.

    Groups JSONL rows by (component, condition) and computes:
      success_rate, stopped_rate, mean_total_calls.

    Returns rows: [{component, condition, n, success_rate, stopped_rate,
                    mean_total_calls}]
    """
    groups: Dict[Tuple[str, str], List[Dict[str, Any]]] = defaultdict(list)
    for row in rows:
        comp = str(row.get("component") or "").strip()
        cond = str(row.get("condition") or "")
        if cond == "fuse":
            cond = "emb"
        if comp and cond in conditions:
            groups[(comp, cond)].append(row)

    # Collect all unique components, sorted
    components = sorted({k[0] for k in groups})

    result: List[Dict[str, Any]] = []
    for comp in components:
        for cond in conditions:
            group = groups.get((comp, cond), [])
            n = len(group)
            if n == 0:
                result.append({
                    "component": comp,
                    "condition": cond,
                    "n": 0,
                    "success_rate": None,
                    "stopped_rate": None,
                    "mean_total_calls": None,
                })
                continue
            success_rate = float(sum(bool(r.get("success")) for r in group) / n)
            stopped_rate = float(sum((not _is_agent_run_completed(r)) for r in group) / n)
            mean_calls = float(
                sum(int(r.get("total_tool_calls", 0) or 0) for r in group) / n
            )
            result.append({
                "component": comp,
                "condition": cond,
                "n": n,
                "success_rate": success_rate,
                "stopped_rate": stopped_rate,
                "mean_total_calls": mean_calls,
            })
    return result


def _build_agent_figure_data(
    rows: List[Dict[str, Any]],
    condition_order: Sequence[str],
) -> Optional[Dict[str, Any]]:
    order = [str(cond or "").strip() for cond in condition_order if str(cond or "").strip()]
    if not order:
        return None

    by_condition: Dict[str, Dict[str, List[Any]]] = {
        cond: {
            "success": [],
            "wrong": [],
            "stopped": [],
            "tokens_all": [],
            "tokens_success": [],
            "tokens_completed": [],
            "tokens_wrong": [],
            "retrieve_all": [],
            "analysis_all": [],
            "total_all": [],
            "retrieve_completed": [],
            "analysis_completed": [],
            "total_completed": [],
        }
        for cond in order
    }
    saw_rows = False

    for row in rows:
        cond = str(row.get("condition") or "").strip()
        if cond == "fuse":
            cond = "emb"
        if cond not in by_condition:
            continue
        saw_rows = True
        bucket = by_condition[cond]
        retrieve_calls = float(max(0, int(row.get("retrieve_calls", 0) or 0)))
        analysis_calls = float(_analysis_tool_call_count(row))
        total_calls = float(max(0, int(row.get("total_tool_calls", 0) or 0)))
        outcome = _agent_run_outcome(row)
        bucket["success"].append(float(outcome == "success"))
        bucket["wrong"].append(float(outcome == "wrong"))
        bucket["stopped"].append(float(outcome == "stopped"))
        total_tokens = float(row.get("total_tokens", 0) or 0)
        bucket["tokens_all"].append(total_tokens)
        if outcome == "success":
            bucket["tokens_success"].append(total_tokens)
        bucket["retrieve_all"].append(retrieve_calls)
        bucket["analysis_all"].append(analysis_calls)
        bucket["total_all"].append(total_calls)
        if _is_agent_run_completed(row):
            bucket["tokens_completed"].append(total_tokens)
            bucket["retrieve_completed"].append(retrieve_calls)
            bucket["analysis_completed"].append(analysis_calls)
            bucket["total_completed"].append(total_calls)
        if outcome == "wrong":
            bucket["tokens_wrong"].append(total_tokens)

    if not saw_rows:
        return None

    tradeoff_data = [
        {
            "condition": cond,
            "success": _mean(by_condition[cond]["success"]),
            "tokens": _mean(by_condition[cond]["tokens_all"]),
        }
        for cond in order
    ]
    tool_usage_data = [
        {
            "condition": cond,
            "retrieve": _mean(by_condition[cond]["retrieve_all"]),
            "analysis": _mean(by_condition[cond]["analysis_all"]),
            "total": _mean(by_condition[cond]["total_all"]),
        }
        for cond in order
    ]
    cost_metrics = [
        {
            "key": "retrieve_calls",
            "label": "Retrieve calls",
            "value_kind": "count",
            "values_by_condition": {
                cond: [float(f"{v:.6f}") for v in by_condition[cond]["retrieve_all"]]
                for cond in order
            },
        },
        {
            "key": "analysis_tool_calls",
            "label": "Analysis calls",
            "value_kind": "count",
            "values_by_condition": {
                cond: [float(f"{v:.6f}") for v in by_condition[cond]["analysis_all"]]
                for cond in order
            },
        },
        {
            "key": "total_tool_calls",
            "label": "Total tool calls",
            "value_kind": "count",
            "values_by_condition": {
                cond: [float(f"{v:.6f}") for v in by_condition[cond]["total_all"]]
                for cond in order
            },
        },
        {
            "key": "total_tokens",
            "label": "Total Token Budget",
            "value_kind": "tokens",
            "plot_style": "budget_pair",
            "success_values_by_condition": {
                cond: [float(f"{v:.6f}") for v in by_condition[cond]["tokens_success"]]
                for cond in order
            },
            "completion_values_by_condition": {
                cond: [float(f"{v:.6f}") for v in by_condition[cond]["tokens_completed"]]
                for cond in order
            },
            "wrong_values_by_condition": {
                cond: [float(f"{v:.6f}") for v in by_condition[cond]["tokens_wrong"]]
                for cond in order
            },
            "budget_values_by_condition": {
                cond: [float(f"{v:.6f}") for v in by_condition[cond]["tokens_all"]]
                for cond in order
            },
            "denominator_by_condition": {
                cond: len(by_condition[cond]["tokens_all"])
                for cond in order
            },
        },
    ]

    return {
        "tradeoff": tradeoff_data,
        "tool_usage": tool_usage_data,
        "agent_cost": {
            "all_runs": True,
            "condition_order": order,
            "condition_labels": {cond: _agent_condition_label(cond) for cond in order},
            "run_counts_by_condition": {
                cond: len(by_condition[cond]["tokens_all"])
                for cond in order
            },
            "metrics": cost_metrics,
        },
    }


def _build_agentic_paper_report(
    summary_payload: Dict[str, Any],
    conditions: List[str],
    *,
    rows: Optional[List[Dict[str, Any]]] = None,
) -> Dict[str, Any]:
    """Build structured paper report from aggregated summary data."""
    summary_by_cond: Dict[str, Dict[str, Any]] = {
        str(r.get("condition") or ""): r
        for r in (summary_payload.get("summary") or [])
        if isinstance(r, dict)
    }

    agent_summary_table: List[Dict[str, Any]] = []
    outcomes_table: List[Dict[str, Any]] = []
    effort_table: List[Dict[str, Any]] = []
    first_call_rank_table: List[Dict[str, Any]] = []
    delta_table: List[Dict[str, Any]] = []

    for cond in conditions:
        row = summary_by_cond.get(cond, {})
        success = row.get("success_rate")
        miss = row.get("miss_rate")
        stopped = row.get("stopped_rate")

        outcomes_table.append({
            "condition": cond,
            "success_rate": success,
            "miss_rate": miss,
            "stopped_rate": stopped,
            "runs": row.get("runs"),
            "stopped_recursion_limit": row.get("stopped_recursion_limit"),
            "stopped_parse_error": row.get("stopped_parse_error"),
            "stopped_runtime_error": row.get("stopped_runtime_error"),
        })

        effort_table.append({
            "condition": cond,
            "mean_retrieve_calls": row.get("mean_retrieve_calls"),
            "mean_analysis_tool_calls": row.get("mean_analysis_tool_calls"),
            "mean_tool_calls": row.get("mean_tool_calls"),
            "tc_p25": row.get("tc_p25"),
            "tc_median": row.get("tc_median"),
            "tc_p75": row.get("tc_p75"),
            "tc_p95": row.get("tc_p95"),
            "mean_total_tokens": row.get("mean_total_tokens"),
            "token_median": row.get("token_median"),
            "token_p25": row.get("token_p25"),
            "token_p75": row.get("token_p75"),
            "token_p95": row.get("token_p95"),
        })

        first_call_rank_table.append(_paper_first_call_rank_row(cond, row))

        e1_p1 = _main_agent_p1_reference(cond)
        delta: Optional[float] = None
        if success is not None and e1_p1 is not None:
            try:
                delta = float(success) - float(e1_p1)
            except (TypeError, ValueError):
                delta = None

        agent_summary_table.append({
            "condition": cond,
            "condition_label": _agent_condition_label(cond),
            "success_rate": success,
            "fail_rate": miss,
            "miss_rate": miss,
            "timeout_rate": stopped,
            "stopped_rate": stopped,
            "delta_vs_p1": delta,
            "tc_p25": row.get("tc_p25"),
            "tc_median": row.get("tc_median"),
            "tc_p75": row.get("tc_p75"),
            "tc_p95": row.get("tc_p95"),
            "token_p25": row.get("token_p25"),
            "token_median": row.get("token_median"),
            "token_p75": row.get("token_p75"),
            "token_p95": row.get("token_p95"),
            "runs": row.get("runs"),
        })

        delta_table.append({
            "condition": cond,
            "agentic_success_rate": success,
            "e1_p1": e1_p1,
            "delta": delta,
            "mean_total_tokens": row.get("mean_total_tokens"),
        })

    # New tables requiring raw rows
    rank_bucket_table: List[Dict[str, Any]] = []
    per_component_table: List[Dict[str, Any]] = []
    per_component_wide_table: List[Dict[str, Any]] = []
    figure_payloads: Dict[str, Any] = {}
    if rows is not None:
        rank_bucket_table = _rank_bucket_success_table(rows, conditions)
        per_component_table = _per_component_agent_summary(rows, conditions)
        per_component_wide_table = _per_component_agent_wide_table(rows, conditions)
        figure_data = _build_agent_figure_data(rows, conditions)
        if figure_data is not None:
            figure_payloads["fig_agent_cost"] = figure_data.get("agent_cost")

    return {
        "report_type": "agentic_paper_report",
        "scenario": summary_payload.get("scenario"),
        "conditions": conditions,
        "task_count": summary_payload.get("task_count"),
        "run_count": summary_payload.get("run_count"),
        "tables": {
            "tab_agent_summary": agent_summary_table,
            "tab_agent_outcomes": outcomes_table,
            "tab_agent_effort": effort_table,
            "tab_first_call_gold_rank": first_call_rank_table,
            "tab_agent_delta": delta_table,
            "tab_rank_bucket_success": rank_bucket_table,
            "tab_per_component_agent": per_component_table,
            "tab_per_component_agent_wide": per_component_wide_table,
        },
        "figures": figure_payloads,
    }


def _print_agentic_paper_report(report: Dict[str, Any]) -> None:
    """Print a human-readable copy of the paper report to stdout."""
    conditions = list(report.get("conditions") or [])
    tables = dict(report.get("tables") or {})

    def _f(v: Any, decimals: int = 4) -> str:
        if v is None:
            return "---"
        try:
            if decimals == 0:
                return str(int(round(float(v))))
            return f"{float(v):.{decimals}f}"
        except (TypeError, ValueError):
            return str(v)

    sep = "=" * 64
    print(f"\n{sep}")
    print("AGENTIC EVALUATION PAPER REPORT")
    print(
        f"Scenario: {report.get('scenario')}  "
        f"Tasks: {report.get('task_count')}  "
        f"Runs: {report.get('run_count')}"
    )
    print(sep)

    # tab:agent_outcomes
    print("\n--- tab:agent_outcomes ---")
    col_w = 10
    header = f"{'Outcome':<14}" + "".join(f"  {c:>{col_w}}" for c in conditions)
    print(header)
    outcomes = {r["condition"]: r for r in tables.get("tab_agent_outcomes", [])}
    int_metrics = {"stopped_recursion_limit", "stopped_parse_error", "stopped_runtime_error"}
    for metric, label in [
        ("success_rate", "Success"),
        ("miss_rate", "Wrong"),
        ("stopped_rate", "Stopped"),
        ("stopped_recursion_limit", "  Recursion limit"),
        ("stopped_parse_error", "  Parse error"),
        ("stopped_runtime_error", "  Runtime error"),
    ]:
        decimals = 0 if metric in int_metrics else 4
        print(
            f"{label:<22}"
            + "".join(f"  {_f(outcomes.get(c, {}).get(metric), decimals=decimals):>{col_w}}" for c in conditions)
        )

    # tab:agent_effort
    print("\n--- tab:agent_effort ---")
    effort = {r["condition"]: r for r in tables.get("tab_agent_effort", [])}
    int_effort_metrics = {"tc_p25", "tc_median", "tc_p75", "tc_p95"}
    for metric, label in [
        ("mean_retrieve_calls", "Mean retrieve calls"),
        ("mean_analysis_tool_calls", "Mean analysis calls"),
        ("mean_tool_calls", "Mean total calls"),
        ("tc_p25", "Q1 total calls"),
        ("tc_median", "Median total calls"),
        ("tc_p75", "Q3 total calls"),
        ("tc_p95", "P95 total calls"),
        ("mean_total_tokens", "Mean total tokens"),
        ("token_median", "Median total tokens"),
        ("token_p25", "Q1 total tokens"),
        ("token_p75", "Q3 total tokens"),
        ("token_p95", "P95 total tokens"),
    ]:
        decimals = 0 if metric in int_effort_metrics else 4
        print(
            f"{label:<24}"
            + "".join(f"  {_f(effort.get(c, {}).get(metric), decimals=decimals):>{col_w}}" for c in conditions)
        )

    # tab:first_call_gold_rank
    print("\n--- tab:first_call_gold_rank ---")
    print(
        f"{'Condition':<12}  {'Hit rate':>10}  {'Mean rank':>10}  "
        f"{'Mean rank (succ)':>16}  {'Mean rank (non)':>16}  "
        f"{'Hit lex':>8}  {'Rank lex':>9}  {'Hit sem':>8}  {'Rank sem':>9}  "
        f"{'Mean total calls':>16}"
    )
    for row in tables.get("tab_first_call_gold_rank", []):
        print(
            f"{row['condition']:<12}  "
            f"{_f(row.get('first_call_gold_hit_rate')):>10}  "
            f"{_f(row.get('first_call_gold_mean_rank')):>10}  "
            f"{_f(row.get('first_call_gold_mean_rank_success')):>16}  "
            f"{_f(row.get('first_call_gold_mean_rank_non_success')):>16}  "
            f"{_f(row.get('first_call_gold_hit_rate_lexical')):>8}  "
            f"{_f(row.get('first_call_gold_mean_rank_lexical')):>9}  "
            f"{_f(row.get('first_call_gold_hit_rate_semantic')):>8}  "
            f"{_f(row.get('first_call_gold_mean_rank_semantic')):>9}  "
            f"{_f(row.get('mean_total_calls')):>16}"
        )

    # tab:agent_delta
    print("\n--- tab:agent_delta ---")
    print(f"{'Condition':<12}  {'Success':>8}  {'E1 P@1':>8}  {'Delta':>8}  {'Mean tokens':>14}")
    for row in tables.get("tab_agent_delta", []):
        print(
            f"{row['condition']:<12}  "
            f"{_f(row['agentic_success_rate']):>8}  "
            f"{_f(row['e1_p1']):>8}  "
            f"{_f(row['delta']):>8}  "
            f"{_f(row['mean_total_tokens'], decimals=0):>14}"
        )

    # tab:rank_bucket_success
    rank_bucket = tables.get("tab_rank_bucket_success", [])
    if rank_bucket:
        print("\n--- tab:rank_bucket_success ---")
        print(f"{'Condition':<12}  {'Bucket':<6}  {'N':>6}  {'Success':>8}")
        for row in rank_bucket:
            print(
                f"{row['condition']:<12}  "
                f"{row['bucket']:<6}  "
                f"{_f(row['n'], decimals=0):>6}  "
                f"{_f(row.get('success_rate')):>8}"
            )

    # tab:per_component_agent
    pc = tables.get("tab_per_component_agent", [])
    if pc:
        print("\n--- tab:per_component_agent (sample) ---")
        print(f"{'Component':<22}  {'Condition':<8}  {'N':>4}  {'Success':>8}  {'Stopped':>8}  {'Calls':>7}")
        for row in pc[:40]:  # first 40 to avoid flood
            print(
                f"{row['component']:<22}  "
                f"{row['condition']:<8}  "
                f"{_f(row['n'], decimals=0):>4}  "
                f"{_f(row.get('success_rate')):>8}  "
                f"{_f(row.get('stopped_rate')):>8}  "
                f"{_f(row.get('mean_total_calls'), decimals=1):>7}"
            )

    print(f"\n{sep}\n")


def _build_agentic_robustness_report(
    summary_payload: Dict[str, Any],
    conditions: List[str],
    *,
    rows: List[Dict[str, Any]],
) -> Dict[str, Any]:
    groups: Dict[Tuple[str, str], List[Dict[str, Any]]] = defaultdict(list)
    for row in rows:
        comp = str(row.get("component") or "").strip()
        cond = str(row.get("condition") or "").strip().lower()
        if cond == "fuse":
            cond = "emb"
        if comp and cond in conditions:
            groups[(comp, cond)].append(row)

    seen_components = {comp for (comp, _cond) in groups}
    ordered_components = [
        comp for comp in ROBUSTNESS_AGENT_COMPONENT_ORDER if comp in seen_components
    ] + sorted(seen_components - set(ROBUSTNESS_AGENT_COMPONENT_ORDER))

    robustness_table: List[Dict[str, Any]] = []
    for component in ordered_components:
        for condition in conditions:
            group = groups.get((component, condition), [])
            n = len(group)
            if n <= 0:
                robustness_table.append({
                    "component": component,
                    "condition": condition,
                    "condition_label": _agent_condition_label(condition),
                    "runs": 0,
                    "success_rate": None,
                    "fail_rate": None,
                    "miss_rate": None,
                    "timeout_rate": None,
                    "stopped_rate": None,
                    "reference_p1": _robustness_agent_p1_reference(component, condition),
                    "delta_vs_p1": None,
                    "tc_p25": None,
                    "tc_median": None,
                    "tc_p75": None,
                    "tc_p95": None,
                    "token_p25": None,
                    "token_median": None,
                    "token_p75": None,
                    "token_p95": None,
                })
                continue

            success_count = sum(1 for row in group if bool(row.get("success")) and _is_agent_run_completed(row))
            stopped_count = sum(1 for row in group if not _is_agent_run_completed(row))
            fail_count = max(0, n - success_count - stopped_count)
            tc_values = [float(row.get("total_tool_calls", 0) or 0) for row in group]
            token_values = [float(row.get("total_tokens", 0) or 0) for row in group]
            success_rate = float(success_count / n)
            reference_p1 = _robustness_agent_p1_reference(component, condition)
            delta_vs_p1 = (
                float(success_rate - float(reference_p1))
                if reference_p1 is not None
                else None
            )

            robustness_table.append({
                "component": component,
                "condition": condition,
                "condition_label": _agent_condition_label(condition),
                "runs": n,
                "success_rate": float(f"{success_rate:.6f}"),
                "fail_rate": float(f"{(fail_count / n):.6f}"),
                "miss_rate": float(f"{(fail_count / n):.6f}"),
                "timeout_rate": float(f"{(stopped_count / n):.6f}"),
                "stopped_rate": float(f"{(stopped_count / n):.6f}"),
                "reference_p1": (
                    float(f"{float(reference_p1):.6f}")
                    if reference_p1 is not None
                    else None
                ),
                "delta_vs_p1": (
                    float(f"{float(delta_vs_p1):.6f}")
                    if delta_vs_p1 is not None
                    else None
                ),
                "tc_p25": float(f"{_quantile(tc_values, 0.25):.6f}"),
                "tc_median": float(f"{_quantile(tc_values, 0.5):.6f}"),
                "tc_p75": float(f"{_quantile(tc_values, 0.75):.6f}"),
                "tc_p95": float(f"{_quantile(tc_values, 0.95):.6f}"),
                "token_p25": float(f"{_quantile(token_values, 0.25):.6f}"),
                "token_median": float(f"{_quantile(token_values, 0.5):.6f}"),
                "token_p75": float(f"{_quantile(token_values, 0.75):.6f}"),
                "token_p95": float(f"{_quantile(token_values, 0.95):.6f}"),
            })

    return {
        "report_type": "agentic_robustness_report",
        "scenario": summary_payload.get("scenario"),
        "conditions": conditions,
        "task_count": summary_payload.get("task_count"),
        "run_count": summary_payload.get("run_count"),
        "tables": {
            "tab_robustness_agent": robustness_table,
            "tab_robustness_condition_summary": list(summary_payload.get("summary") or []),
        },
    }


def agentic_eval_paper_report(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Generate paper-ready numbers for all agentic evaluation tables.

    Loads from an existing output directory if results are present; otherwise
    runs agentic_eval_run_matrix to generate them first.

    Options:
      outdir     -- path to result directory (default base: out/agent_eval;
                    default runs are written to a timestamped subdirectory).
                    If agentic_summary_{scenario}.json is found there, loads it
                    directly.  If only agentic_runs_{scenario}.jsonl is found,
                    re-summarises from the raw rows.  If neither exists, runs
                    agentic_eval_run_matrix and then loads the result.
      scenario   -- scenario name to load (default: topk10)
      conditions -- comma-separated condition names (default: base,bm25,emb,both)
    """
    scenario = str(opts.get("scenario", "topk10") or "topk10").strip()
    cfg = _with_defaults(opts, AGENTIC_RUN_DEFAULTS)
    try:
        conditions = _normalize_conditions(cfg)
    except ValueError as e:
        return {"error": str(e)}

    outdir_opt = str(opts.get("outdir", "") or "").strip()
    outdir: Optional[Path] = Path(outdir_opt).resolve() if outdir_opt else None

    summary_payload: Optional[Dict[str, Any]] = None
    runs_path: Optional[Path] = None
    cached_rows: Optional[List[Dict[str, Any]]] = None  # avoids re-reading JSONL

    # --- Try to load from existing files ---
    if outdir is not None:
        summary_payload, cached_rows, runs_path, load_err = _load_agentic_summary_bundle(
            outdir,
            scenario,
            conditions,
        )
        if load_err:
            return {"error": load_err}
        if summary_payload is not None:
            LOGGER.info(
                "Loaded cached agentic report inputs from %s",
                outdir,
            )

    # --- Fall back to generating new results ---
    if summary_payload is None:
        LOGGER.info("No existing results found; running agentic_eval_run_matrix...")
        run_result = agentic_eval_run_matrix(args, opts)
        if "error" in run_result:
            return run_result
        # Locate the generated summary file
        for artifact_info in (run_result.get("artifacts") or []):
            if not isinstance(artifact_info, dict):
                continue
            sj = artifact_info.get("summary_json")
            if sj and Path(sj).exists():
                try:
                    summary_payload = json.loads(Path(sj).read_text(encoding="utf-8"))
                    outdir = Path(sj).parent
                except Exception as e:
                    return {"error": f"Failed to read generated summary {sj}: {e}"}
                break
        if summary_payload is None:
            return {"error": "agentic_eval_run_matrix completed but no summary file was found."}

    # --- Build and print report ---
    report = _build_agentic_paper_report(summary_payload, conditions, rows=cached_rows)
    _print_agentic_paper_report(report)

    # --- Write paper_report.json ---
    if outdir is None:
        outdir = Path(_resolve_outdir(cfg)).resolve()
    outdir.mkdir(parents=True, exist_ok=True)
    report_path = outdir / "agentic_paper_report.json"
    try:
        report_path.write_text(json.dumps(report, indent=2), encoding="utf-8")
        report["artifact"] = str(report_path)
        LOGGER.info("Paper report written to %s", report_path)
    except Exception as e:
        LOGGER.warning("Could not write paper report: %s", e)

    return report


_TRADEOFF_DATA = [
    {"condition": "base",  "success": 0.3778, "tokens": 469099},
    {"condition": "bm25",  "success": 0.5067, "tokens": 575042},
    {"condition": "emb",   "success": 0.6000, "tokens": 314072},
    {"condition": "both",  "success": 0.6044, "tokens": 453466},
]

_TOOL_USAGE_DATA = [
    {"condition": "base", "retrieve": 5.2711,  "analysis": 30.4622},
    {"condition": "bm25", "retrieve": 31.4756, "analysis": 28.8578},
    {"condition": "emb",  "retrieve": 14.0711, "analysis": 15.7200},
    {"condition": "both", "retrieve": 21.7911, "analysis": 23.7956},
]


_AGENT_FIGURE_CONDITION_ORDER = ("base", "bm25", "emb", "both")
_AGENT_FIGURE_COLORS: Dict[str, str] = {
    "base": "#9a9a9a",
    "bm25": "#4C78A8",
    "emb": "#2A9D8F",
    "both": "#E76F51",
    "oracle": "#6F4E7C",
}
_AGENT_FIGURE_OUTCOME_ORDER = ("success", "wrong", "stopped")
_AGENT_FIGURE_OUTCOME_LABELS: Dict[str, str] = {
    "success": "Success",
    "wrong": "Wrong",
    "stopped": "Stopped",
}
_AGENT_FIGURE_OUTCOME_COLORS: Dict[str, str] = {
    "success": "#54A24B",
    "wrong": "#E45756",
    "stopped": "#F2B134",
}


def _load_live_agent_figure_data(
    jsonl_path: str,
    condition_order: Optional[Sequence[str]] = None,
) -> Optional[Dict[str, Any]]:
    rows = _load_agentic_rows_from_jsonl(Path(jsonl_path))
    if not rows:
        return None
    return _build_agent_figure_data(rows, condition_order or _AGENT_FIGURE_CONDITION_ORDER)


def _plot_agent_tradeoff(
    plt: Any,
    mticker: Any,
    tradeoff_data: List[Dict[str, Any]],
    outpath: Path,
    rc: Dict[str, Any],
    fig_w: float,
    fig_h: float,
) -> None:
    with plt.rc_context(rc):
        fig, ax = plt.subplots(figsize=(fig_w, fig_h))
        for pt in tradeoff_data:
            ax.scatter(pt["tokens"], pt["success"], zorder=3, s=30)
            ax.annotate(
                pt["condition"],
                (pt["tokens"], pt["success"]),
                textcoords="offset points",
                xytext=(4, 3),
                fontsize=7,
            )
        ax.set_xlabel("Mean total tokens per run")
        ax.set_ylabel("Success rate")
        ax.spines["top"].set_visible(False)
        ax.spines["right"].set_visible(False)
        ax.xaxis.set_major_formatter(
            mticker.FuncFormatter(lambda x, _: f"{int(x / 1000)}k" if x >= 1000 else str(int(x)))
        )
        fig.tight_layout()
        fig.savefig(str(outpath))
        plt.close(fig)


def _plot_agent_cost(
    plt: Any,
    mticker: Any,
    figure_data: Dict[str, Any],
    outpath: Path,
    rc: Dict[str, Any],
    fig_w: float,
    fig_h: float,
) -> None:
    def _compact_number_label(value: float) -> str:
        abs_value = abs(value)
        if abs_value >= 1_000_000:
            text = f"{value / 1_000_000:.1f}M"
        elif abs_value >= 1_000:
            text = f"{value / 1_000:.0f}k"
        elif float(value).is_integer():
            text = f"{int(value)}"
        else:
            text = f"{value:.1f}"
        return text.replace(".0M", "M").replace(".0k", "k")

    def _log_display_floor(metric: Dict[str, Any], raw_values: List[float]) -> float:
        positive_values = [value for value in raw_values if value > 0]
        if positive_values:
            smallest_positive = min(positive_values)
            return max(smallest_positive / 2.0, 1e-6)
        if str(metric.get("value_kind") or "") == "tokens":
            return 1.0
        return 0.5

    def _apply_cost_axis_scale(
        ax: Any,
        metric: Dict[str, Any],
        datasets: List[List[float]],
        display_floor: float,
    ) -> None:
        flat_values = [value for values in datasets for value in values]
        if not flat_values:
            return

        max_value = max(flat_values)
        if max_value <= 0:
            ax.set_ylim(bottom=display_floor)
            return

        value_kind = str(metric.get("value_kind") or "")
        if value_kind == "tokens":
            candidate_ticks = [
                10_000.0,
                20_000.0,
                50_000.0,
                100_000.0,
                200_000.0,
                500_000.0,
                1_000_000.0,
                2_000_000.0,
                5_000_000.0,
                10_000_000.0,
            ]
        else:
            candidate_ticks = [
                1.0,
                2.0,
                5.0,
                10.0,
                20.0,
                50.0,
                100.0,
                200.0,
                500.0,
            ]

        tick_max = max_value * 1.05
        ticks = [display_floor]
        ticks.extend(tick for tick in candidate_ticks if display_floor <= tick <= tick_max)
        if ticks[-1] < max_value:
            ticks.append(max_value)
        ticks = sorted(set(ticks))

        ax.set_yscale("log", base=10)
        ax.set_ylim(bottom=display_floor, top=max_value * 1.12)
        ax.yaxis.set_major_locator(mticker.FixedLocator(ticks))
        ax.yaxis.set_major_formatter(
            mticker.FuncFormatter(
                lambda value, _: (
                    "0"
                    if abs(float(value) - display_floor) <= max(display_floor * 1e-6, 1e-9)
                    else _compact_number_label(float(value))
                )
            )
        )

    def _render_outcome_scatter(
        ax: Any,
        metric: Dict[str, Any],
        condition_order: List[str],
        display_floor: float,
    ) -> List[List[float]]:
        key = str(metric.get("key") or "")
        points_by_condition = dict(metric.get("points_by_condition") or {})
        plotted_datasets: List[List[float]] = []

        for idx, cond in enumerate(condition_order, start=1):
            points = list(points_by_condition.get(cond) or [])
            plotted_values: List[float] = []
            by_outcome: Dict[str, Tuple[List[float], List[float]]] = {
                outcome: ([], [])
                for outcome in _AGENT_FIGURE_OUTCOME_ORDER
            }

            for point_idx, point in enumerate(points):
                raw_value = float(point.get("value", 0) or 0)
                plotted_value = raw_value if raw_value > 0 else display_floor
                outcome = str(point.get("outcome") or "wrong").strip().lower()
                if outcome not in by_outcome:
                    outcome = "wrong"
                jitter_rng = random.Random(
                    f"{key}:{cond}:{outcome}:{point_idx}:{raw_value:.6f}"
                )
                jitter = jitter_rng.uniform(-0.18, 0.18)
                by_outcome[outcome][0].append(float(idx) + jitter)
                by_outcome[outcome][1].append(plotted_value)
                plotted_values.append(plotted_value)

            for outcome in _AGENT_FIGURE_OUTCOME_ORDER:
                xs, ys = by_outcome[outcome]
                if not xs:
                    continue
                ax.scatter(
                    xs,
                    ys,
                    s=18,
                    alpha=0.7,
                    color=_AGENT_FIGURE_OUTCOME_COLORS[outcome],
                    label=_AGENT_FIGURE_OUTCOME_LABELS[outcome],
                    zorder=3,
                )

            if plotted_values:
                median_value = _median(plotted_values)
                ax.hlines(
                    median_value,
                    idx - 0.24,
                    idx + 0.24,
                    colors="#111111",
                    linewidth=2.2,
                    zorder=4,
                )
            plotted_datasets.append(plotted_values)

        handles, labels = ax.get_legend_handles_labels()
        if handles:
            deduped: Dict[str, Any] = {}
            for handle, label in zip(handles, labels):
                if label and label not in deduped:
                    deduped[label] = handle
            ax.legend(
                list(deduped.values()),
                list(deduped.keys()),
                loc="upper center",
                bbox_to_anchor=(0.5, 1.12),
                ncol=3,
                frameon=False,
                columnspacing=0.9,
                handletextpad=0.4,
                borderaxespad=0.25,
            )

        return plotted_datasets

    def _apply_ecdf_x_axis_scale(ax: Any, raw_values: List[float]) -> List[float]:
        positive_values = [value for value in raw_values if value > 0]
        if not positive_values:
            display_floor = 1.0
            max_value = 10.0
            has_zero = True
        else:
            has_zero = any(value <= 0 for value in raw_values)
            smallest_positive = min(positive_values)
            display_floor = (
                max(smallest_positive / 2.0, 1e-6)
                if has_zero
                else max(smallest_positive * 0.9, 1e-6)
            )
            max_value = max(positive_values)

        candidate_ticks = [
            10_000.0,
            100_000.0,
            1_000_000.0,
            5_000_000.0,
            10_000_000.0,
        ]
        tick_max = max_value * 1.05
        ticks: List[float] = [display_floor] if has_zero else []
        ticks.extend(tick for tick in candidate_ticks if display_floor <= tick <= tick_max)
        if not ticks:
            ticks.append(display_floor)
        ticks = sorted(set(ticks))

        ax.set_xscale("log", base=10)
        ax.set_xlim(left=display_floor, right=max_value * 1.12)
        ax.xaxis.set_major_locator(mticker.FixedLocator(ticks))
        ax.xaxis.set_minor_locator(mticker.NullLocator())
        ax.xaxis.set_major_formatter(
            mticker.FuncFormatter(
                lambda value, _: (
                    "0"
                    if has_zero and abs(float(value) - display_floor) <= max(display_floor * 1e-6, 1e-9)
                    else _compact_number_label(float(value))
                )
            )
        )
        return ticks

    def _render_ecdf(
        ax: Any,
        metric: Dict[str, Any],
        condition_order: List[str],
        condition_labels: Dict[str, str],
    ) -> None:
        values_by_condition = dict(metric.get("values_by_condition") or {})
        raw_flat_values = [
            float(value)
            for cond in condition_order
            for value in (values_by_condition.get(cond) or [])
        ]
        _apply_ecdf_x_axis_scale(ax, raw_flat_values)

        for cond in condition_order:
            raw_values = [float(v) for v in (values_by_condition.get(cond) or [])]
            if not raw_values:
                continue
            left = ax.get_xlim()[0]
            plotted_values = sorted(value if value > 0 else left for value in raw_values)
            denom = float(len(plotted_values))
            ys = [idx / denom for idx in range(1, len(plotted_values) + 1)]
            ax.step(
                plotted_values,
                ys,
                where="post",
                linewidth=2.0,
                color=_AGENT_FIGURE_COLORS.get(cond, "#444444"),
                label=condition_labels.get(cond, _agent_condition_label(cond)),
            )

        ax.set_xlabel(str(metric.get("label") or "Value"))
        ax.set_ylabel("Fraction of runs <= x")
        ax.set_ylim(0.0, 1.02)
        ax.grid(color="#d8d8d8", linewidth=0.6, alpha=0.7, linestyle=":")
        ax.spines["top"].set_visible(False)
        ax.spines["right"].set_visible(False)

    def _render_cumulative_budget_curve(
        ax: Any,
        condition_order: List[str],
        condition_labels: Dict[str, str],
        run_counts_by_condition: Dict[str, int],
        *,
        value_lists_by_condition: Dict[str, Any],
        budget_values_by_condition: Dict[str, Any],
        denominator_by_condition: Dict[str, Any],
        ylabel: str,
        xlabel: str,
    ) -> None:
        raw_flat_values = [
            float(value)
            for cond in condition_order
            for value in (
                budget_values_by_condition.get(cond)
                or value_lists_by_condition.get(cond)
                or []
            )
        ]
        _apply_ecdf_x_axis_scale(ax, raw_flat_values or [1.0])
        left, right = ax.get_xlim()

        for cond in condition_order:
            values = sorted(float(v) for v in (value_lists_by_condition.get(cond) or []))
            denom = int(
                denominator_by_condition.get(cond)
                or run_counts_by_condition.get(cond)
                or len(budget_values_by_condition.get(cond) or [])
                or 0
            )
            if denom <= 0:
                continue

            plotted_values = [value if value > 0 else left for value in values]
            final_rate = len(plotted_values) / float(denom)
            xs = [left]
            ys = [0.0]
            for idx, value in enumerate(plotted_values, start=1):
                xs.append(value)
                ys.append(idx / float(denom))
            xs.append(right)
            ys.append(final_rate)

            ax.step(
                xs,
                ys,
                where="post",
                linewidth=2.0,
                color=_AGENT_FIGURE_COLORS.get(cond, "#444444"),
                label=condition_labels.get(cond, _agent_condition_label(cond)),
            )

        ax.set_xlabel(xlabel)
        ax.set_ylabel(ylabel)
        ax.set_ylim(0.0, 1.0)
        ax.yaxis.set_major_locator(mticker.FixedLocator([0.0, 0.25, 0.5, 0.75, 1.0]))
        ax.yaxis.set_minor_locator(mticker.NullLocator())
        ax.yaxis.set_major_formatter(mticker.PercentFormatter(xmax=1.0, decimals=0))
        ax.grid(color="#d8d8d8", linewidth=0.6, alpha=0.7, linestyle=":")
        ax.spines["top"].set_visible(False)
        ax.spines["right"].set_visible(False)

    def _render_cumulative_success(
        ax: Any,
        metric: Dict[str, Any],
        condition_order: List[str],
        condition_labels: Dict[str, str],
        run_counts_by_condition: Dict[str, int],
    ) -> None:
        _render_cumulative_budget_curve(
            ax,
            condition_order,
            condition_labels,
            run_counts_by_condition,
            value_lists_by_condition=dict(metric.get("success_values_by_condition") or {}),
            budget_values_by_condition=dict(metric.get("budget_values_by_condition") or {}),
            denominator_by_condition=dict(metric.get("denominator_by_condition") or {}),
            ylabel="Success Rate Within Budget",
            xlabel=str(metric.get("label") or "Token Budget"),
        )

    def _render_cumulative_completion(
        ax: Any,
        metric: Dict[str, Any],
        condition_order: List[str],
        condition_labels: Dict[str, str],
        run_counts_by_condition: Dict[str, int],
    ) -> None:
        _render_cumulative_budget_curve(
            ax,
            condition_order,
            condition_labels,
            run_counts_by_condition,
            value_lists_by_condition=dict(metric.get("completion_values_by_condition") or {}),
            budget_values_by_condition=dict(metric.get("budget_values_by_condition") or {}),
            denominator_by_condition=dict(metric.get("denominator_by_condition") or {}),
            ylabel="Completion Rate Within Budget",
            xlabel=str(metric.get("label") or "Token Budget"),
        )

    def _render_cumulative_failure(
        ax: Any,
        metric: Dict[str, Any],
        condition_order: List[str],
        condition_labels: Dict[str, str],
        run_counts_by_condition: Dict[str, int],
    ) -> None:
        _render_cumulative_budget_curve(
            ax,
            condition_order,
            condition_labels,
            run_counts_by_condition,
            value_lists_by_condition=dict(metric.get("wrong_values_by_condition") or {}),
            budget_values_by_condition=dict(metric.get("budget_values_by_condition") or {}),
            denominator_by_condition=dict(metric.get("denominator_by_condition") or {}),
            ylabel="Failure Rate Within Budget",
            xlabel=str(metric.get("label") or "Token Budget"),
        )

    def _figure_level_legend(fig: Any, handles: List[Any], labels: List[str]) -> None:
        deduped: Dict[str, Any] = {}
        for handle, label in zip(handles, labels):
            if label and label not in deduped:
                deduped[label] = handle
        if not deduped:
            return
        fig.legend(
            list(deduped.values()),
            list(deduped.keys()),
            loc="upper center",
            bbox_to_anchor=(0.5, 0.985),
            ncol=4,
            frameon=False,
            columnspacing=1.0,
            handletextpad=0.5,
            borderaxespad=0.0,
        )

    def _metric_footer_text(metric: Dict[str, Any]) -> str:
        plot_style = str(metric.get("plot_style") or "").strip().lower()
        if plot_style == "outcome_scatter":
            return "All runs; colors denote outcome; log y-axis"
        if plot_style == "ecdf":
            return "All runs; log x-axis"
        if plot_style == "cumulative_success":
            return "Correct runs in numerator; all tasks in denominator; log x-axis"
        if plot_style == "budget_pair":
            return ""
        return "All runs; log y-axis"

    def _render_metric_axis(
        ax: Any,
        metric: Dict[str, Any],
        condition_order: List[str],
        condition_labels: Dict[str, str],
        run_counts_by_condition: Dict[str, int],
    ) -> None:
        key = str(metric.get("key") or "")
        label = str(metric.get("label") or key)
        plot_style = str(metric.get("plot_style") or "").strip().lower()
        if plot_style == "ecdf":
            _render_ecdf(ax, metric, condition_order, condition_labels)
            return
        if plot_style == "cumulative_success":
            _render_cumulative_success(ax, metric, condition_order, condition_labels, run_counts_by_condition)
            return
        if plot_style == "budget_pair":
            _render_cumulative_success(ax, metric, condition_order, condition_labels, run_counts_by_condition)
            return
        values_by_condition = dict(metric.get("values_by_condition") or {})
        positions: List[int] = []
        datasets: List[List[float]] = []
        plotted_conditions: List[str] = []
        raw_datasets: List[List[float]] = []

        for idx, cond in enumerate(condition_order, start=1):
            values = [float(v) for v in (values_by_condition.get(cond) or [])]
            if not values:
                continue
            raw_datasets.append(values)
            positions.append(idx)
            plotted_conditions.append(cond)

        raw_flat_values = [value for values in raw_datasets for value in values]
        display_floor = _log_display_floor(metric, raw_flat_values)
        if plot_style == "outcome_scatter":
            datasets = _render_outcome_scatter(ax, metric, condition_order, display_floor)
            ax.set_ylabel(label)
        else:
            for values in raw_datasets:
                datasets.append([value if value > 0 else display_floor for value in values])

            if datasets:
                bp = ax.boxplot(
                    datasets,
                    positions=positions,
                    widths=0.58,
                    patch_artist=True,
                    showfliers=False,
                    medianprops={"color": "#1f1f1f", "linewidth": 1.2},
                    whiskerprops={"color": "#555555", "linewidth": 0.9},
                    capprops={"color": "#555555", "linewidth": 0.9},
                    boxprops={"edgecolor": "#444444", "linewidth": 0.9},
                )
                for patch, cond in zip(bp["boxes"], plotted_conditions):
                    patch.set_facecolor(_AGENT_FIGURE_COLORS.get(cond, "#bdbdbd"))
                    patch.set_alpha(0.85)
            else:
                ax.text(
                    0.5,
                    0.5,
                    "No runs",
                    transform=ax.transAxes,
                    ha="center",
                    va="center",
                )
            ax.set_title(label)

        ax.set_xticks(list(range(1, len(condition_order) + 1)))
        ax.set_xticklabels(
            [
                f"{condition_labels.get(cond, _agent_condition_label(cond))}\n"
                f"n={run_counts_by_condition.get(cond, 0)}"
                for cond in condition_order
            ]
        )
        ax.set_xlim(0.5, len(condition_order) + 0.5)
        ax.grid(axis="y", color="#d8d8d8", linewidth=0.6, alpha=0.7, linestyle=":")
        ax.spines["top"].set_visible(False)
        ax.spines["right"].set_visible(False)
        _apply_cost_axis_scale(ax, metric, datasets, display_floor)

    condition_order = [
        str(cond or "").strip()
        for cond in (figure_data.get("condition_order") or [])
        if str(cond or "").strip()
    ]
    condition_labels = {
        str(k): str(v)
        for k, v in dict(figure_data.get("condition_labels") or {}).items()
    }
    run_counts_by_condition = {
        str(k): int(v)
        for k, v in dict(
            figure_data.get("run_counts_by_condition")
            or figure_data.get("completed_runs_by_condition")
            or {}
        ).items()
    }
    metrics = list(figure_data.get("metrics") or [])

    with plt.rc_context(rc):
        fig, axes = plt.subplots(2, 2, figsize=(fig_w, fig_h))
        axes_flat = list(axes.flatten())
        for ax, metric in zip(axes_flat, metrics):
            _render_metric_axis(ax, metric, condition_order, condition_labels, run_counts_by_condition)

        for ax in axes_flat[len(metrics):]:
            ax.set_visible(False)

        has_curve_metric = any(
            str(metric.get("plot_style") or "").strip().lower() in {"ecdf", "cumulative_success", "budget_pair"}
            for metric in metrics
        )
        if has_curve_metric:
            for ax, metric in zip(axes_flat, metrics):
                if str(metric.get("plot_style") or "").strip().lower() in {"ecdf", "cumulative_success", "budget_pair"}:
                    handles, labels = ax.get_legend_handles_labels()
                    _figure_level_legend(fig, list(handles), list(labels))
                    break
        fig.text(0.5, 0.02, "All runs", ha="center", va="bottom")
        fig.tight_layout(rect=(0.0, 0.04, 1.0, 0.90 if has_curve_metric else 1.0))
        fig.savefig(str(outpath))
        plt.close(fig)

        for metric in metrics:
            key = str(metric.get("key") or "").strip()
            if not key:
                continue
            metric_slug = key.replace("_", "-")
            metric_path = outpath.parent / f"agent-cost-{metric_slug}.pdf"
            plot_style = str(metric.get("plot_style") or "").strip().lower()
            footer_text = _metric_footer_text(metric)
            if plot_style == "budget_pair":
                fig_single, axes_triple = plt.subplots(1, 3, figsize=(10.2, 2.8))
                _render_cumulative_completion(
                    axes_triple[0],
                    metric,
                    condition_order,
                    condition_labels,
                    run_counts_by_condition,
                )
                axes_triple[0].set_title("Completion")
                _render_cumulative_success(
                    axes_triple[1],
                    metric,
                    condition_order,
                    condition_labels,
                    run_counts_by_condition,
                )
                axes_triple[1].set_title("Success")
                _render_cumulative_failure(
                    axes_triple[2],
                    metric,
                    condition_order,
                    condition_labels,
                    run_counts_by_condition,
                )
                axes_triple[2].set_title("Failure")
                handles, labels = axes_triple[0].get_legend_handles_labels()
                _figure_level_legend(fig_single, list(handles), list(labels))
                if footer_text:
                    fig_single.text(
                        0.5,
                        0.02,
                        footer_text,
                        ha="center",
                        va="bottom",
                    )
                bottom_rect = 0.05 if footer_text else 0.0
                fig_single.tight_layout(rect=(0.0, bottom_rect, 1.0, 0.88))
                fig_single.savefig(str(metric_path))
                plt.close(fig_single)
                continue

            fig_single, ax_single = plt.subplots(figsize=(3.4, 2.8))
            _render_metric_axis(
                ax_single,
                metric,
                condition_order,
                condition_labels,
                run_counts_by_condition,
            )
            if plot_style in {"ecdf", "cumulative_success"}:
                handles, labels = ax_single.get_legend_handles_labels()
                _figure_level_legend(fig_single, list(handles), list(labels))
            if footer_text:
                fig_single.text(
                    0.5,
                    0.02,
                    footer_text,
                    ha="center",
                    va="bottom",
                )
            top_rect = 0.88 if plot_style in {"ecdf", "cumulative_success"} else 1.0
            bottom_rect = 0.05 if footer_text else 0.0
            fig_single.tight_layout(rect=(0.0, bottom_rect, 1.0, top_rect))
            fig_single.savefig(str(metric_path))
            plt.close(fig_single)


def _plot_agent_tool_usage(
    plt: Any,
    tool_usage_data: List[Dict[str, Any]],
    outpath: Path,
    rc: Dict[str, Any],
    fig_w: float,
    fig_h: float,
) -> None:
    with plt.rc_context(rc):
        fig, ax = plt.subplots(figsize=(fig_w, fig_h))
        conditions = [d["condition"] for d in tool_usage_data]
        retrieve_vals = [d["retrieve"] for d in tool_usage_data]
        analysis_vals = [d["analysis"] for d in tool_usage_data]
        total_vals = [d.get("total", d["retrieve"] + d["analysis"]) for d in tool_usage_data]
        x_pos = list(range(len(conditions)))
        bar_width = 0.62
        ax.bar(
            x_pos,
            retrieve_vals,
            width=bar_width,
            label="Retrieve",
            color="#5b8ff9",
            zorder=2,
        )
        ax.bar(
            x_pos,
            analysis_vals,
            width=bar_width,
            bottom=retrieve_vals,
            label="Analysis",
            color="#61b15a",
            zorder=2,
        )
        for idx, total in enumerate(total_vals):
            stacked_height = float(retrieve_vals[idx]) + float(analysis_vals[idx])
            y = max(stacked_height, float(total)) + max(0.35, float(total) * 0.02)
            ax.text(
                idx,
                y,
                f"{float(total):.1f}",
                ha="center",
                va="bottom",
                fontsize=7,
            )
        ax.set_xticks(x_pos)
        ax.set_xticklabels([str(cond).upper() for cond in conditions])
        ax.set_ylabel("Mean calls per run")
        ax.spines["top"].set_visible(False)
        ax.spines["right"].set_visible(False)
        ax.grid(axis="y", color="#d8d8d8", linewidth=0.6, alpha=0.7, linestyle=":")
        ax.legend(loc="upper right")
        fig.tight_layout()
        fig.savefig(str(outpath))
        plt.close(fig)



def generate_agent_figures(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Generate paper figures from agentic evaluation artifacts.

    Options:
      outdir      -- output directory (default: out/agent_eval/figures)
      report_path -- optional path to agentic_paper_report.json
      jsonl_path  -- optional path to agentic_runs_*.jsonl
      conditions  -- optional comma-separated condition order for live JSONL
      which       -- comma-separated figures to generate
                     (default: agent_cost; supported: agent_cost, tradeoff, tool_usage)
                     agent_cost writes one combined PDF plus one PDF per cost metric
    """
    try:
        import matplotlib
        matplotlib.use("pdf")
        import matplotlib.pyplot as plt
        import matplotlib.ticker as mticker
    except ImportError as e:
        return {"error": f"matplotlib not available: {e}"}

    outdir_opt = str(opts.get("outdir", "") or "").strip()
    outdir = Path(outdir_opt) if outdir_opt else Path(DEFAULT_AGENT_FIGURE_OUTDIR)
    outdir = outdir.expanduser().resolve()
    outdir.mkdir(parents=True, exist_ok=True)

    def _parse_csv_list(raw: Any) -> List[str]:
        if raw is None:
            return []
        text = str(raw).strip()
        if not text:
            return []
        return [part.strip() for part in text.split(",") if part.strip()]

    requested = [item.lower() for item in _parse_csv_list(opts.get("which"))]
    if not requested:
        requested = ["agent_cost"]
    requested = list(dict.fromkeys(requested))

    source_conditions = _parse_csv_list(opts.get("conditions"))
    if not source_conditions:
        source_conditions = list(_AGENT_FIGURE_CONDITION_ORDER)

    report_path_opt = str(opts.get("report_path", "") or "").strip()
    report_payload: Dict[str, Any] = {}
    if report_path_opt:
        report_path = Path(report_path_opt).expanduser().resolve()
        try:
            report_payload = json.loads(report_path.read_text(encoding="utf-8"))
            report_conditions = [
                str(cond or "").strip()
                for cond in (report_payload.get("conditions") or [])
                if str(cond or "").strip()
            ]
            if report_conditions:
                source_conditions = report_conditions
        except Exception as e:
            return {"error": f"Failed to read report_path {report_path}: {e}"}

    figure_data_bundle: Optional[Dict[str, Any]] = None
    jsonl_path = str(opts.get("jsonl_path", "") or "").strip()
    if jsonl_path:
        try:
            figure_data_bundle = _load_live_agent_figure_data(jsonl_path, source_conditions)
        except Exception as e:
            LOGGER.warning("Could not load live JSONL data from %s: %s", jsonl_path, e)

    fig_w, fig_h = 3.5, 2.5
    rc = {"font.size": 8, "axes.titlesize": 8, "axes.labelsize": 8,
          "xtick.labelsize": 7, "ytick.labelsize": 7, "legend.fontsize": 7}
    outputs: Dict[str, str] = {}

    if "agent_cost" in requested:
        cost_figure = (
            dict(report_payload.get("figures") or {}).get("fig_agent_cost")
            if report_payload else None
        )
        if cost_figure is None and figure_data_bundle is not None:
            cost_figure = figure_data_bundle.get("agent_cost")
        if cost_figure is None:
            return {
                "error": (
                    "agent_cost figure data not found; provide report_path pointing to "
                    "agentic_paper_report.json or jsonl_path pointing to agentic_runs_*.jsonl"
                )
            }
        cost_path = outdir / "agent-cost.pdf"
        _plot_agent_cost(plt, mticker, cost_figure, cost_path, rc, 6.8, 4.6)
        print(f"agent-cost.pdf       -> {cost_path}")
        outputs["agent_cost"] = str(cost_path)
        for metric in list(cost_figure.get("metrics") or []):
            key = str(metric.get("key") or "").strip()
            if not key:
                continue
            metric_slug = key.replace("_", "-")
            metric_path = outdir / f"agent-cost-{metric_slug}.pdf"
            print(f"{metric_path.name:<20} -> {metric_path}")
            outputs[f"agent_cost_{key}"] = str(metric_path)


    if "tradeoff" in requested:
        tradeoff_data = _TRADEOFF_DATA
        if figure_data_bundle is not None and figure_data_bundle.get("tradeoff") is not None:
            tradeoff_data = list(figure_data_bundle.get("tradeoff") or [])
        tradeoff_path = outdir / "agent-tradeoff.pdf"
        _plot_agent_tradeoff(plt, mticker, tradeoff_data, tradeoff_path, rc, fig_w, fig_h)
        print(f"agent-tradeoff.pdf   -> {tradeoff_path}")
        outputs["agent_tradeoff"] = str(tradeoff_path)

    if "tool_usage" in requested:
        tool_usage_data = _TOOL_USAGE_DATA
        if figure_data_bundle is not None and figure_data_bundle.get("tool_usage") is not None:
            tool_usage_data = list(figure_data_bundle.get("tool_usage") or [])
        tool_path = outdir / "agent-tool-usage.pdf"
        _plot_agent_tool_usage(plt, tool_usage_data, tool_path, rc, fig_w, fig_h)
        print(f"agent-tool-usage.pdf -> {tool_path}")
        outputs["agent_tool_usage"] = str(tool_path)

    if not outputs:
        return {"error": f"No supported figures requested: {requested}"}
    return outputs


def _resolve_figure_outdir(opts: Dict[str, Any], run_outdir: str) -> str:
    raw = str(opts.get("figure_outdir") or opts.get("figures_outdir") or "").strip()
    if raw:
        return str(Path(raw).expanduser().resolve())
    return str((Path(run_outdir).expanduser().resolve() / "figures"))


def _generate_robustness_cost_figures(
    runs_jsonl: Path,
    outdir: Path,
    *,
    fmt: str = "pdf",
) -> Dict[str, str]:
    try:
        from oxide.plugins import fuse as fuse_plugin
    except Exception as e:
        return {"error": f"Could not import oxide.plugins.fuse: {e}"}

    result = fuse_plugin.plot_robustness_cost(
        [],
        {
            "runs_jsonl": str(runs_jsonl),
            "outdir": str(outdir),
            "fmt": str(fmt or "pdf"),
        },
    )
    if "error" in result:
        return result

    outputs: Dict[str, str] = {}
    hyphen_aliases = {
        "robustness_tokens": "robustness-tokens",
        "robustness_tool_calls": "robustness-tool-calls",
    }
    for saved_path in (result.get("saved") or []):
        saved = Path(str(saved_path)).expanduser().resolve()
        outputs[saved.name] = str(saved)
        alias_stem = hyphen_aliases.get(saved.stem)
        if not alias_stem:
            continue
        alias_path = saved.with_name(f"{alias_stem}{saved.suffix}")
        try:
            if alias_path != saved:
                alias_path.write_bytes(saved.read_bytes())
            outputs[alias_path.name] = str(alias_path)
        except Exception:
            outputs[alias_path.name] = str(saved)
    return outputs


def agentic_eval_main(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Run the main agent benchmark experiment and build its paper report."""
    cfg = dict(opts or {})
    outdir = str(cfg.get("outdir") or DEFAULT_MAIN_AGENT_EVAL_OUTDIR).strip()
    scenario = str(cfg.get("scenario") or "topk10").strip() or "topk10"
    figure_outdir = _resolve_figure_outdir(cfg, outdir)
    rerun = _as_bool(cfg.get("rerun"), False)

    run_cfg = dict(cfg)
    run_cfg["outdir"] = outdir
    run_cfg.setdefault("conditions", ",".join(DEFAULT_AGENTIC_CONDITIONS))

    run_result: Optional[Dict[str, Any]] = None
    if rerun:
        run_result = agentic_eval_run_matrix(args, run_cfg)
        if "error" in run_result:
            return run_result

    report = agentic_eval_paper_report(args, run_cfg)
    if "error" in report:
        return report

    outdir_path = Path(outdir).expanduser().resolve()
    runs_path = outdir_path / f"agentic_runs_{scenario}.jsonl"
    summary_path = outdir_path / f"agentic_summary_{scenario}.json"
    manifest_path = outdir_path / "agentic_eval_matrix_manifest.json"
    report_path = Path(str(report.get("artifact") or outdir_path / "agentic_paper_report.json")).expanduser().resolve()

    figures: Dict[str, str] = {}
    warnings: List[str] = []
    if _as_bool(cfg.get("generate_figures"), True):
        figure_opts = {
            "outdir": figure_outdir,
            "report_path": str(report_path),
            "jsonl_path": str(runs_path),
            "conditions": ",".join(report.get("conditions") or DEFAULT_AGENTIC_CONDITIONS),
            "which": str(cfg.get("which") or "agent_cost"),
        }
        figure_result = generate_agent_figures([], figure_opts)
        if "error" in figure_result:
            warnings.append(str(figure_result.get("error")))
        else:
            figures = {str(k): str(v) for k, v in figure_result.items()}

    payload: Dict[str, Any] = {
        "experiment": "agentic_eval_main",
        "scenario": scenario,
        "outdir": str(outdir_path),
        "conditions": list(report.get("conditions") or []),
        "tables": dict(report.get("tables") or {}),
        "artifacts": {
            "manifest_json": str(manifest_path) if manifest_path.exists() else None,
            "summary_json": str(summary_path) if summary_path.exists() else None,
            "runs_jsonl": str(runs_path) if runs_path.exists() else None,
            "report_json": str(report_path) if report_path.exists() else None,
            "figure_outdir": figure_outdir,
            "figures": figures,
        },
    }
    if run_result is not None:
        payload["run_result"] = {
            "artifact": run_result.get("artifact"),
            "run_count": run_result.get("run_count"),
        }
    if warnings:
        payload["warnings"] = warnings
    return payload


def agentic_eval_robustness(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Run the robustness agent benchmark and build its paper-facing table."""
    cfg = dict(opts or {})
    outdir = str(cfg.get("outdir") or DEFAULT_ROBUSTNESS_AGENT_EVAL_OUTDIR).strip()
    scenario = str(cfg.get("scenario") or "topk10").strip() or "topk10"
    figure_outdir = _resolve_figure_outdir(cfg, outdir)
    rerun = _as_bool(cfg.get("rerun"), False)

    run_cfg = dict(cfg)
    run_cfg["outdir"] = outdir
    run_cfg["robustness"] = True
    run_cfg.setdefault("conditions", ",".join(DEFAULT_ROBUSTNESS_AGENT_CONDITIONS))
    try:
        conditions = _normalize_conditions(run_cfg)
    except ValueError as e:
        return {"error": str(e)}

    run_result: Optional[Dict[str, Any]] = None
    outdir_path = Path(outdir).expanduser().resolve()
    if rerun:
        run_result = agentic_eval_run_matrix(args, run_cfg)
        if "error" in run_result:
            return run_result

    summary_payload, rows, runs_path, load_err = _load_agentic_summary_bundle(
        outdir_path,
        scenario,
        conditions,
    )
    if load_err:
        return {"error": load_err}
    if summary_payload is None or rows is None or runs_path is None:
        run_result = agentic_eval_run_matrix(args, run_cfg)
        if "error" in run_result:
            return run_result
        summary_payload, rows, runs_path, load_err = _load_agentic_summary_bundle(
            outdir_path,
            scenario,
            conditions,
        )
        if load_err:
            return {"error": load_err}
    if summary_payload is None or rows is None or runs_path is None:
        return {"error": "Could not load robustness run artifacts after execution."}

    report = _build_agentic_robustness_report(summary_payload, conditions, rows=rows)
    report_path = outdir_path / "agentic_robustness_report.json"
    report_path.write_text(json.dumps(report, indent=2), encoding="utf-8")
    report["artifact"] = str(report_path)

    robustness_csv = _write_csv(
        str(outdir_path / "agentic_robustness_table.csv"),
        list((report.get("tables") or {}).get("tab_robustness_agent") or []),
    )
    summary_path = outdir_path / f"agentic_summary_{scenario}.json"
    manifest_path = outdir_path / "agentic_eval_matrix_manifest.json"

    figures: Dict[str, str] = {}
    warnings: List[str] = []
    if _as_bool(cfg.get("generate_figures"), True):
        figure_result = _generate_robustness_cost_figures(
            runs_path,
            Path(figure_outdir).expanduser().resolve(),
            fmt=str(cfg.get("fmt") or "pdf"),
        )
        if "error" in figure_result:
            warnings.append(str(figure_result.get("error")))
        else:
            figures = {str(k): str(v) for k, v in figure_result.items()}

    payload: Dict[str, Any] = {
        "experiment": "agentic_eval_robustness",
        "scenario": scenario,
        "outdir": str(outdir_path),
        "conditions": conditions,
        "tables": dict(report.get("tables") or {}),
        "artifacts": {
            "manifest_json": str(manifest_path) if manifest_path.exists() else None,
            "summary_json": str(summary_path) if summary_path.exists() else None,
            "runs_jsonl": str(runs_path) if runs_path.exists() else None,
            "report_json": str(report_path),
            "table_csv": robustness_csv,
            "figure_outdir": figure_outdir,
            "figures": figures,
        },
    }
    if run_result is not None:
        payload["run_result"] = {
            "artifact": run_result.get("artifact"),
            "run_count": run_result.get("run_count"),
        }
    if warnings:
        payload["warnings"] = warnings
    return payload


def agentic_eval_all(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Run all agent-evaluation experiments used by the paper."""
    cfg = dict(opts or {})
    root_outdir = str(cfg.get("outdir") or "").strip()
    if root_outdir:
        root_path = Path(root_outdir).expanduser().resolve()
        main_outdir = str(Path(cfg.get("main_outdir") or root_path / "main"))
        robustness_outdir = str(Path(cfg.get("robustness_outdir") or root_path / "robustness"))
    else:
        root_path = None
        main_outdir = str(cfg.get("main_outdir") or DEFAULT_MAIN_AGENT_EVAL_OUTDIR)
        robustness_outdir = str(cfg.get("robustness_outdir") or DEFAULT_ROBUSTNESS_AGENT_EVAL_OUTDIR)

    main_opts = dict(cfg)
    main_opts["outdir"] = main_outdir
    robustness_opts = dict(cfg)
    robustness_opts["outdir"] = robustness_outdir

    main_result = agentic_eval_main(args, main_opts)
    if "error" in main_result:
        return {"error": f"agentic_eval_main failed: {main_result.get('error')}"}

    robustness_result = agentic_eval_robustness(args, robustness_opts)
    if "error" in robustness_result:
        return {"error": f"agentic_eval_robustness failed: {robustness_result.get('error')}"}

    payload: Dict[str, Any] = {
        "experiment": "agentic_eval_all",
        "outdir": str(root_path) if root_path is not None else None,
        "artifacts": {
            "main_outdir": main_result.get("outdir"),
            "robustness_outdir": robustness_result.get("outdir"),
        },
        "main": main_result,
        "robustness": robustness_result,
    }
    return payload


exports = [agentic_eval_all, agentic_eval_main, agentic_eval_robustness]
