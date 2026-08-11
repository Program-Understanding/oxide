from __future__ import annotations

import logging
import time
from collections import defaultdict
from statistics import median
from typing import Any, Dict, List, Optional, Sequence, Tuple

from oxide.core import api
from oxide.plugins.file_loc_common import (
    DEFAULT_COMP_PATH,
    DEFAULT_PROMPT_PATH,
    apply_task_filters,
    build_eval_tasks,
    create_ground_truth,
    filter_executables,
    load_prompt_map,
    parse_csv_set,
    write_json_artifact,
)


NAME = "query_function_eval"
LOGGER = logging.getLogger(NAME)
if not LOGGER.handlers:
    _h = logging.StreamHandler()
    _h.setFormatter(logging.Formatter("[%(asctime)s] %(levelname)s %(name)s: %(message)s", "%H:%M:%S"))
    LOGGER.addHandler(_h)
LOGGER.setLevel(logging.INFO)
LOGGER.propagate = False

METHOD_IDS = ["qf_decomp_global", "qf_clap_global"]
METHOD_DISPLAY = {
    "qf_decomp_global": "QF-Decomp",
    "qf_clap_global": "QF-CLAP",
}
DEFAULT_OUTDIR = "out/file_localization_tps/query_function_eval"


def _as_int(value: Any, default: int, *, min_value: Optional[int] = None) -> int:
    try:
        out = int(value)
    except Exception:
        out = int(default)
    if min_value is not None and out < min_value:
        out = int(min_value)
    return out


def _normalize_methods(opts: Dict[str, Any]) -> Tuple[Optional[List[str]], Optional[str]]:
    raw = str(opts.get("methods", "") or "").strip().lower()
    if not raw:
        return list(METHOD_IDS), None
    items = [x.strip() for x in raw.split(",") if x.strip()]
    out = []
    alias = {
        "decomp": "qf_decomp_global",
        "qf_decomp": "qf_decomp_global",
        "clap": "qf_clap_global",
        "qf_clap": "qf_clap_global",
    }
    for item in items:
        out.append(alias.get(item, item))
    dedup = list(dict.fromkeys(out))
    unknown = [m for m in dedup if m not in METHOD_IDS]
    if unknown:
        return None, f"Unknown methods: {','.join(unknown)}. Allowed: {','.join(METHOD_IDS)}"
    return dedup, None


def _to_int_addr(value: Any) -> Optional[int]:
    if isinstance(value, int):
        return value
    s = str(value or "").strip()
    if not s:
        return None
    try:
        if s.startswith(("0x", "0X")):
            return int(s, 16)
        if s.isdigit():
            return int(s, 10)
        if all(ch in "0123456789abcdefABCDEF" for ch in s):
            return int(s, 16)
        return int(s)
    except Exception:
        return None


def _extract_ranked_function_candidates(raw: Any) -> List[Dict[str, Any]]:
    payload = raw if isinstance(raw, dict) else {}
    if payload and len(payload) == 1:
        only = next(iter(payload.values()))
        if isinstance(only, dict) and "results" in only:
            payload = only
    candidates = ((payload.get("results") or {}).get("candidates") or []) if isinstance(payload, dict) else []
    if not isinstance(candidates, list):
        return []

    out: List[Dict[str, Any]] = []
    for idx, cand in enumerate(candidates, start=1):
        if not isinstance(cand, dict):
            continue
        oid = str(cand.get("oid") or "").strip()
        if not oid:
            continue
        addr = _to_int_addr(cand.get("function_addr") or cand.get("func_addr"))
        out.append(
            {
                "rank": idx,
                "oid": oid,
                "function_addr": addr,
                "function_name": str(cand.get("function_name") or cand.get("func_name") or "").strip(),
                "score": float(cand.get("similarity", cand.get("score", 0.0)) or 0.0),
            }
        )
    return out


def _bodied_function_addrs(oid: str) -> set:
    """Addresses of functions Ghidra recovered a body for.

    ghidra_disasm also lists external import stubs such as `<EXTERNAL>::strcpy`,
    which carry a signature and an empty block list. Restricting to functions
    with a body holds every method to the same candidate pool.
    """
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    out = set()
    for addr, finfo in funcs.items():
        if addr == "meta" or not isinstance(finfo, dict) or not finfo.get("blocks"):
            continue
        parsed = _to_int_addr(addr)
        if parsed is not None:
            out.add(parsed)
    return out


def _restrict_to_bodied(
    candidates: Sequence[Dict[str, Any]],
    bodied_by_oid: Dict[str, set],
) -> List[Dict[str, Any]]:
    """Drop bodiless candidates and renumber, so both methods rank one pool."""
    kept = [c for c in candidates if c["function_addr"] in bodied_by_oid.get(c["oid"], ())]
    for rank, cand in enumerate(kept, start=1):
        cand["rank"] = rank
    return kept


def _first_function_rank(candidates: Sequence[Dict[str, Any]], gold_oid: str) -> Tuple[Optional[int], Optional[int], Optional[str]]:
    for row in candidates:
        if str(row.get("oid") or "") == gold_oid:
            return (
                int(row.get("rank")),
                row.get("function_addr"),
                str(row.get("function_name") or "") or None,
            )
    return None, None, None


def _first_file_rank(candidates: Sequence[Dict[str, Any]], gold_oid: str) -> Optional[int]:
    seen = set()
    rank = 0
    for row in candidates:
        oid = str(row.get("oid") or "")
        if not oid or oid in seen:
            continue
        seen.add(oid)
        rank += 1
        if oid == gold_oid:
            return rank
    return None


def _rank_metrics(ranks: Sequence[Optional[int]], *, hit_cutoffs: Sequence[int]) -> Dict[str, Any]:
    total = len(ranks)
    found = [int(r) for r in ranks if isinstance(r, int) and r > 0]
    out: Dict[str, Any] = {
        "queries": total,
        "found_queries": len(found),
        "missed_queries": total - len(found),
        "hit_rate": float(sum(1 for r in ranks if isinstance(r, int) and r > 0) / total) if total else 0.0,
        "MRR": float(sum((1.0 / int(r)) for r in ranks if isinstance(r, int) and r > 0) / total) if total else 0.0,
        "mean_rank": (float(sum(found) / len(found)) if found else None),
        "median_rank": (float(median(found)) if found else None),
    }
    for cutoff in hit_cutoffs:
        out[f"Hit@{cutoff}"] = float(sum(1 for r in ranks if isinstance(r, int) and r <= cutoff) / total) if total else 0.0
    out["P@1"] = float(sum(1 for r in ranks if isinstance(r, int) and r == 1) / total) if total else 0.0
    return out


def _per_component_metrics(
    per_query: Sequence[Dict[str, Any]],
    *,
    rank_field: str,
    hit_cutoffs: Sequence[int],
) -> List[Dict[str, Any]]:
    by_component: Dict[str, List[Optional[int]]] = defaultdict(list)
    for row in per_query:
        comp = str(row.get("component") or "").strip()
        if not comp:
            continue
        rank = row.get(rank_field)
        by_component[comp].append(int(rank) if isinstance(rank, int) and rank > 0 else None)

    out = []
    for component in sorted(by_component):
        out.append(
            {
                "component": component,
                "metrics": _rank_metrics(by_component[component], hit_cutoffs=hit_cutoffs),
            }
        )
    return out


def _run_method(method_id: str, tasks: List[Dict[str, Any]], opts: Dict[str, Any]) -> Dict[str, Any]:
    backend = "search_functions" if method_id == "qf_decomp_global" else "clap"
    search_mode = str(opts.get("search_mode", "semantic") or "semantic").strip().lower()
    if search_mode != "semantic":
        return {"method": method_id, "error": "query_function_eval currently supports semantic mode only."}

    per_query: List[Dict[str, Any]] = []
    function_ranks: List[Optional[int]] = []
    file_ranks: List[Optional[int]] = []
    exes_by_cid: Dict[str, List[str]] = {}
    bodied_by_oid: Dict[str, set] = {}

    for task in tasks:
        cid = str(task.get("cid") or "")
        if not cid:
            continue
        exes = exes_by_cid.get(cid)
        if exes is None:
            exes = filter_executables(list(api.expand_oids(cid) or []))
            exes_by_cid[cid] = exes
        if not exes:
            continue
        for oid in exes:
            if oid not in bodied_by_oid:
                bodied_by_oid[oid] = _bodied_function_addrs(oid)

        prompt = str(task.get("prompt") or "").strip()
        if not prompt:
            continue

        retrieve_opts = {
            "query": prompt,
            "backend": backend,
            "search_mode": "semantic",
            "top_k": 0,
            "limit": 0,
            "offset": 0,
            "similarity_threshold": float("-inf"),
            "include_full_code": False,
            "preview_length": 0,
            "timing": False,
            "progress": False,
        }
        t0 = time.perf_counter_ns()
        out = api.retrieve("query_function", exes, retrieve_opts) or {}
        runtime_ms = (time.perf_counter_ns() - t0) / 1_000_000.0

        candidates = _restrict_to_bodied(_extract_ranked_function_candidates(out), bodied_by_oid)
        gold_oid = str(task.get("gold_oid") or "")
        function_rank, function_addr, function_name = _first_function_rank(candidates, gold_oid)
        file_rank = _first_file_rank(candidates, gold_oid)
        unique_files = len({str(row.get("oid") or "") for row in candidates if str(row.get("oid") or "")})

        function_ranks.append(function_rank)
        file_ranks.append(file_rank)
        per_query.append(
            {
                "task_id": task.get("task_id"),
                "cid": cid,
                "collection": task.get("collection"),
                "component": task.get("component"),
                "query": prompt,
                "gold_oid": gold_oid,
                "first_correct_function_rank": function_rank,
                "first_correct_function_addr": (f"0x{function_addr:x}" if isinstance(function_addr, int) else None),
                "first_correct_function_name": function_name,
                "first_correct_file_rank": file_rank,
                "total_ranked_functions": len(candidates),
                "total_ranked_files": unique_files,
                "runtime_ms": float(f"{runtime_ms:.3f}"),
            }
        )

    return {
        "method": method_id,
        "backend": backend,
        "attempted_queries": len(per_query),
        "global_function_metrics": _rank_metrics(function_ranks, hit_cutoffs=[10, 100, 1000]),
        "global_file_metrics": _rank_metrics(file_ranks, hit_cutoffs=[2, 5]),
        "per_component_function_metrics": _per_component_metrics(
            per_query, rank_field="first_correct_function_rank", hit_cutoffs=[10, 100, 1000]
        ),
        "per_component_file_metrics": _per_component_metrics(
            per_query, rank_field="first_correct_file_rank", hit_cutoffs=[2, 5]
        ),
        "per_query": per_query,
    }


def query_function_eval_main(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Evaluate query_function as a global function-ranking task.

    For each FUSE-style query q, rank all functions in the firmware image and
    measure the first function rank belonging to the known gold executable.

    Options:
      comp_path   -- ground-truth JSON (default: fuse_data/openwrt-dataset/fuse_ground_truth.json)
      prompt_path -- prompt JSON (default: fuse_data/descriptions/component_descriptions.json)
      methods     -- qf_decomp_global,qf_clap_global (default: both)
      components  -- optional comma list filter
      collections -- optional comma list filter
      outdir      -- write artifact directory (default: out/query_function_eval)
    """
    comp_path = str(opts.get("comp_path", DEFAULT_COMP_PATH) or DEFAULT_COMP_PATH).strip()
    prompt_path = str(opts.get("prompt_path", DEFAULT_PROMPT_PATH) or DEFAULT_PROMPT_PATH).strip()
    outdir = str(opts.get("outdir", DEFAULT_OUTDIR) or DEFAULT_OUTDIR).strip()

    try:
        ground_truth = create_ground_truth(comp_path)
    except Exception as err:
        return {"error": f"failed to load comp_path '{comp_path}': {err}"}
    try:
        prompt_map = load_prompt_map(prompt_path)
    except Exception as err:
        return {"error": f"failed to load prompt_path '{prompt_path}': {err}"}

    methods, method_err = _normalize_methods(opts)
    if method_err:
        return {"error": method_err}
    if methods is None:
        return {"error": "no methods selected"}

    tasks = build_eval_tasks(ground_truth, prompt_map)
    tasks = apply_task_filters(
        tasks,
        components=parse_csv_set(opts.get("components")),
        collections=parse_csv_set(opts.get("collections")),
    )
    if not tasks:
        return {"error": "no evaluation tasks generated (check filters and prompt coverage)"}

    per_method: Dict[str, Dict[str, Any]] = {}
    for method_id in methods:
        LOGGER.info("query_function_eval_main: running method %s (%d tasks)", method_id, len(tasks))
        per_method[method_id] = _run_method(method_id, tasks, opts)
        if per_method[method_id].get("error"):
            return {
                "error": f"method '{method_id}' failed: {per_method[method_id].get('error')}",
                "partial": per_method,
            }

    function_summary = []
    for method_id in methods:
        result = per_method[method_id]
        function_summary.append(
            {
                "method": METHOD_DISPLAY.get(method_id, method_id),
                **(result.get("global_function_metrics") or {}),
            }
        )

    payload = {
        "experiment": "query_function_eval_main",
        "task_count": len(tasks),
        "methods": methods,
        "sources": {
            "comp_path": comp_path,
            "prompt_path": prompt_path,
        },
        "tables": {
            "tab_function_rank_summary": function_summary,
        },
        "per_method": per_method,
    }
    artifact = write_json_artifact(outdir, "query_function_eval_main.json", payload)
    if artifact:
        payload["artifact"] = artifact
    return payload


exports = [query_function_eval_main]
