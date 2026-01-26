import json
import time
import logging
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from oxide.core import api

NAME = "fuse_test"
logger = logging.getLogger(NAME)

# ---------------------------------------------------------------------------
# Exposed plugin functions
# ---------------------------------------------------------------------------

def agent_search(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Execute the "agent" retrieval workflow for one query on one collection.

    args: [<cid>]   (collection id)
    opts:
      - query / query_path
      - toolset: "fuse" | "function" | "both"
      - use_tags: bool (passed to FUSE; function tool ignores unless you add tags there)
      - top_k_files: int (how many file candidates to return)
      - top_k_funcs: int (function candidates used for aggregation / rerank)
    """
    cid = _get_cid(args)
    query = _load_text_opt(opts, "query", "query_path")
    if not query:
        return {"error": "Provide query or query_path."}

    toolset = (opts.get("toolset") or "fuse").strip().lower()
    use_tags = bool(opts.get("use_tags", True))

    top_k_files = int(opts.get("top_k_files", 50) or 50)
    top_k_funcs = int(opts.get("top_k_funcs", 50) or 50)

    t0 = time.perf_counter_ns()
    tool_calls = 0
    trace: List[Dict[str, Any]] = []

    if toolset == "fuse":
        tool_calls += 1
        fuse_out = _call_fuse(cid, query, use_tags=use_tags, top_k=top_k_files)
        trace.append({"tool": "fuse", "top_k": top_k_files})

        ranked_files = _extract_file_candidates_from_fuse(fuse_out, top_k=top_k_files)

    elif toolset == "function":
        tool_calls += 1
        qf_out = _call_query_function(cid, query, top_k=top_k_funcs)
        trace.append({"tool": "query_function", "top_k": top_k_funcs})

        ranked_files = _aggregate_functions_to_files(qf_out, top_k_files=top_k_files)

    elif toolset == "both":
        # 1) shortlist files with FUSE
        tool_calls += 1
        fuse_out = _call_fuse(cid, query, use_tags=use_tags, top_k=max(top_k_files, 10))
        trace.append({"tool": "fuse", "top_k": max(top_k_files, 10)})

        fuse_files = _extract_file_candidates_from_fuse(fuse_out, top_k=max(top_k_files, 10))
        shortlist_oids = [c["oid"] for c in fuse_files if "oid" in c]
        shortlist_oids = shortlist_oids[:max(top_k_files, 10)]

        # 2) rerank with function search on shortlist
        tool_calls += 1
        qf_out = _call_query_function_over_oids(shortlist_oids, query, top_k=top_k_funcs)
        trace.append({"tool": "query_function", "top_k": top_k_funcs, "scope": "fuse_shortlist"})

        reranked = _aggregate_functions_to_files(qf_out, top_k_files=top_k_files)

        # merge: keep FUSE-only candidates (for transparency), but prefer function rerank ordering
        ranked_files = reranked

    else:
        return {"error": f"Unknown toolset='{toolset}'. Use: fuse | function | both."}

    elapsed_ms = (time.perf_counter_ns() - t0) / 1_000_000.0

    best = ranked_files[0] if ranked_files else None
    return {
        "cid": cid,
        "collection": api.get_colname_from_oid(cid),
        "query": query,
        "toolset": toolset,
        "use_tags": use_tags,
        "tool_calls": tool_calls,
        "elapsed_ms": float(f"{elapsed_ms:.3f}"),
        "results": {
            "best_match": best,
            "candidates": ranked_files
        },
        "trace": trace
    }


def agent_batch(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Batch evaluation of the agent workflow over collections/components.

    opts:
      - comp_path: json mapping collection_name -> { component -> path(s) }
      - prompt_path: json mapping component -> prompt string (or {component:[prompts]} if you extend)
      - toolset: fuse | function | both
      - use_tags: bool
      - top_k_files, top_k_funcs
    """
    comp_path = opts.get("comp_path")
    prompt_path = opts.get("prompt_path")
    if not comp_path or not prompt_path:
        return {"error": "Provide comp_path and prompt_path."}

    ground_truth = create_ground_truth(comp_path)

    try:
        prompt_map = json.loads(Path(prompt_path).read_text())
    except Exception as e:
        return {"error": f"Failed to load prompt_path JSON: {e}"}

    toolset = (opts.get("toolset") or "fuse").strip().lower()
    use_tags = bool(opts.get("use_tags", True))
    top_k_files = int(opts.get("top_k_files", 50) or 50)
    top_k_funcs = int(opts.get("top_k_funcs", 50) or 50)

    per_collection: Dict[str, Any] = {}
    total = 0
    sum_p1 = 0
    sum_h2 = 0
    sum_h5 = 0
    sum_mrr = 0.0
    sum_rank = 0.0
    total_ms = 0.0
    total_tool_calls = 0

    for cid, golds in ground_truth.items():
        colname = api.get_colname_from_oid(cid)
        ranks_by_component: Dict[str, Optional[int]] = {}
        rows: List[int] = []

        for comp, gold_oid in golds.items():
            prompt = prompt_map.get(comp)
            if not prompt:
                ranks_by_component[comp] = None
                continue

            out = agent_search(
                [cid],
                {
                    "query": prompt,
                    "toolset": toolset,
                    "use_tags": use_tags,
                    "top_k_files": top_k_files,
                    "top_k_funcs": top_k_funcs,
                },
            )

            total_ms += float(out.get("elapsed_ms", 0.0))
            total_tool_calls += int(out.get("tool_calls", 0))

            cands = (out.get("results") or {}).get("candidates") or []
            oid_list = [c.get("oid") for c in cands]

            try:
                rank = oid_list.index(gold_oid) + 1
            except ValueError:
                # not retrieved in returned list
                rank = None

            ranks_by_component[comp] = rank
            if rank is None:
                continue

            rows.append(rank)
            total += 1
            sum_p1 += int(rank == 1)
            sum_h2 += int(rank <= 2)
            sum_h5 += int(rank <= 5)
            sum_mrr += (1.0 / rank)
            sum_rank += rank

        n = len([r for r in ranks_by_component.values() if r is not None])
        if n > 0:
            per_collection[colname] = {
                "metrics": {
                    "P@1": sum(1 for r in ranks_by_component.values() if r == 1) / n,
                    "Hit@2": sum(1 for r in ranks_by_component.values() if r is not None and r <= 2) / n,
                    "Hit@5": sum(1 for r in ranks_by_component.values() if r is not None and r <= 5) / n,
                    "MRR": sum((1.0 / r) for r in ranks_by_component.values() if r) / n,
                    "mean_rank": sum(r for r in ranks_by_component.values() if r) / n,
                },
                "ranks_by_prompt": ranks_by_component,
            }
        else:
            per_collection[colname] = {"metrics": {}, "ranks_by_prompt": ranks_by_component}

    if total == 0:
        return {"error": "No prompts evaluated (check comp_path/prompt_path alignment)."}

    global_metrics = {
        "P@1": sum_p1 / total,
        "Hit@2": sum_h2 / total,
        "Hit@5": sum_h5 / total,
        "MRR": sum_mrr / total,
        "Mean": sum_rank / total,
    }

    return {
        "toolset": toolset,
        "use_tags": use_tags,
        "top_k_files": top_k_files,
        "top_k_funcs": top_k_funcs,
        "per_collection": per_collection,
        "global_metrics": global_metrics,
        "avg_retrieval_time_ms": float(f"{(total_ms / max(total, 1)):.3f}"),
        "avg_tool_calls": float(f"{(total_tool_calls / max(total, 1)):.3f}"),
    }


def agent_compare(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Convenience wrapper: runs fuse vs function vs both under same inputs.
    """
    out = {}
    base = dict(opts)

    for toolset in ("fuse", "function", "both"):
        base["toolset"] = toolset
        out[toolset] = agent_batch(args, base)

    return out


exports = [agent_search, agent_batch, agent_compare]

# ---------------------------------------------------------------------------
# Tool calls + result normalization
# ---------------------------------------------------------------------------

def _call_fuse(cid: str, query: str, use_tags: bool, top_k: int) -> Dict[str, Any]:
    """
    Try to call FUSE in either "cid-driven" or "candidate-driven" mode.
    """
    # Try cid-driven first (many modules do this)
    try:
        out = api.retrieve("fuse", [cid], {"prompt": query, "use_tags": use_tags, "top_k": top_k})
        if isinstance(out, dict):
            return out
    except Exception:
        pass

    # Fallback: candidate-driven (pass expanded executable oids)
    exes = filter_executables(api.expand_oids(cid))
    return api.retrieve("fuse", exes, {"prompt": query, "use_tags": use_tags, "top_k": top_k})


def _extract_file_candidates_from_fuse(fuse_out: Dict[str, Any], top_k: int) -> List[Dict[str, Any]]:
    """
    Normalizes expected FUSE output into: [{oid, score, names}, ...]
    Accepts either:
      - {'results': {'candidates': [...]}}
      - { ... other nesting ... }
    """
    # If your fuse analyzer returns { 'results': { 'candidates': [...] } }
    cands = None
    if isinstance(fuse_out, dict):
        if "results" in fuse_out and isinstance(fuse_out["results"], dict):
            cands = fuse_out["results"].get("candidates")
        elif "results" in fuse_out and isinstance(fuse_out["results"], list):
            cands = fuse_out["results"]
        elif "candidates" in fuse_out:
            cands = fuse_out.get("candidates")

    if not cands:
        return []

    # Ensure it’s list[dict], sort desc by score if not already.
    items = [c for c in cands if isinstance(c, dict) and "oid" in c]
    items.sort(key=lambda x: x.get("score", 0.0), reverse=True)
    return items[:top_k] if top_k > 0 else items


def _call_query_function(cid: str, query: str, top_k: int) -> Dict[str, Any]:
    exes = filter_executables(api.expand_oids(cid))
    return api.retrieve("query_function", exes, {"query": query, "top_k": top_k})


def _call_query_function_over_oids(oids: List[str], query: str, top_k: int) -> Dict[str, Any]:
    # Pass OIDs directly; query_function will index only those.
    return api.retrieve("query_function", oids, {"query": query, "top_k": top_k})


def _aggregate_functions_to_files(qf_out: Dict[str, Any], top_k_files: int) -> List[Dict[str, Any]]:
    """
    Take function matches and produce file candidates.

    Aggregation: file_score = max(function_score) across returned functions
    (simple, stable, and matches "best evidence function" explanation).
    """
    # Expected from your query_function analyzer:
    # { "results": { "candidates": [ {oid,function_addr,function_name,score,preview}, ... ] } }
    funcs = []
    if isinstance(qf_out, dict):
        res = qf_out.get("results", {})
        if isinstance(res, dict):
            funcs = res.get("candidates") or []
        else:
            funcs = qf_out.get("matches") or []

    if not funcs:
        return []

    best_by_oid: Dict[str, Dict[str, Any]] = {}

    for f in funcs:
        if not isinstance(f, dict):
            continue
        oid = f.get("oid")
        score = f.get("score")
        if not oid or score is None:
            continue

        prev = best_by_oid.get(oid)
        if (prev is None) or (float(score) > float(prev.get("score", -1e9))):
            # Keep the single strongest evidence function for this file.
            best_by_oid[oid] = {
                "oid": oid,
                "score": float(score),
                "names": list(api.get_names_from_oid(oid)),
                "evidence": {
                    "function_addr": f.get("function_addr"),
                    "function_name": f.get("function_name"),
                    "preview": f.get("preview"),
                },
            }

    ranked = sorted(best_by_oid.values(), key=lambda x: x["score"], reverse=True)
    return ranked[:top_k_files] if top_k_files > 0 else ranked


# ---------------------------------------------------------------------------
# Ground truth + utilities (lifted from your FUSE plugin patterns)
# ---------------------------------------------------------------------------

def create_ground_truth(data_path: str) -> Dict[str, Dict[str, str]]:
    """
    Build mapping {cid: {component: oid}} by matching basenames from JSON to oid names.
    JSON expected shape: { collection_name: { component: [paths...] or path } }
    """
    data = json.loads(Path(data_path).read_text())

    ground_truth: Dict[str, Dict[str, str]] = {}
    for cid in api.collection_cids():
        c_name = api.get_colname_from_oid(cid)
        if c_name not in data:
            continue

        collection_data = data[c_name]
        basename_map: Dict[str, str] = {}

        for component, paths in collection_data.items():
            candidates = paths if isinstance(paths, list) else [paths]
            for p in candidates:
                basename_map[component] = Path(p).name

        exes = filter_executables(api.expand_oids(cid))
        ground_truth[cid] = build_col_gt(exes, basename_map)

    return ground_truth


def build_col_gt(exes: List[str], basename_map: Dict[str, str]) -> Dict[str, str]:
    col_gt: Dict[str, str] = {}
    for oid in exes:
        for name in api.get_names_from_oid(oid):
            match = next((c for c, f in basename_map.items() if f == name), None)
            if match is not None:
                col_gt[match] = oid
                break
    return col_gt


def filter_executables(oids: List[str]) -> List[str]:
    exes = []
    for oid in oids:
        cat = api.get_field("categorize", oid, oid)
        if cat != "executable":
            continue
        names = list(api.get_names_from_oid(oid))
        if any(ext in n for n in names for ext in (".so", ".ko")):
            continue
        exes.append(oid)
    return exes


def _get_cid(args: List[str]) -> str:
    # Match your existing plugin idioms
    cids, _ = api.valid_oids(args)
    if not cids:
        # allow direct cid in args[0]
        return args[0]
    return cids[0]


def _load_text_opt(opts: Dict[str, Any], key: str, key_path: str) -> str:
    s = (opts.get(key) or "").strip()
    p = (opts.get(key_path) or "").strip()
    if not s and p:
        try:
            s = Path(p).read_text(encoding="utf-8", errors="replace").strip()
        except Exception:
            return ""
    return s
