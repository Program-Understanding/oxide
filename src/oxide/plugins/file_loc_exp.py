from __future__ import annotations

"""
Primary retrieval-side experiment plugin for the PACK paper.

Covers the non-agent artifact path referenced in evaluation.tex:
- §5.1 Standalone retrieval: BM25 / Dense / PACK via tool_eval_main()
- §5.3 Per-component retrieval MRR via component_analysis()
- Paper artifact assembly via eval_paper_report()
"""

import json
import logging
import time
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

from oxide.core import api
from oxide.plugins.file_loc_common import (
    DEFAULT_COMP_PATH,
    DEFAULT_PROMPT_PATH,
    apply_task_filters,
    build_eval_tasks,
    create_ground_truth,
    filter_executables,
    load_json_object,
    load_prompt_map,
    parse_csv_set,
    write_json_artifact,
)

try:
    import numpy as np
except Exception:
    np = None  # type: ignore

try:
    from sentence_transformers import SentenceTransformer
except Exception:
    SentenceTransformer = None  # type: ignore


NAME = "file_localization_eval"
LOGGER = logging.getLogger(NAME)
if not LOGGER.handlers:
    _h = logging.StreamHandler()
    _h.setFormatter(logging.Formatter("[%(asctime)s] %(levelname)s %(name)s: %(message)s", "%H:%M:%S"))
    LOGGER.addHandler(_h)
LOGGER.setLevel(logging.INFO)
LOGGER.propagate = False

DEFAULT_OUTDIR = "out/file_localization_tps"
DEFAULT_TOP_K_FILES = 1_000_000
DEFAULT_METHODS = ["bm25_tool", "dense_tool", "pack_tool"]
DEFAULT_AGENT_REPORT_PATH = "out/agent_eval/agentic_paper_report.json"
DEFAULT_DENSE_MODEL_ID = "sentence-transformers/all-MiniLM-L6-v2"
DEFAULT_DENSE_MODEL_REVISION = "c9745ed1d9f207416be6d2e6f8de32d1f16199bf"
DEFAULT_PACK_BUDGET_TOKENS = 512
DEFAULT_LOCAL_FILES_ONLY = True

# dense_tool = same encoder as the packed semantic condition but on raw string
# concatenation without evidence packing — §5.1 ablation.
METHOD_IDS = ["bm25_tool", "dense_tool", "pack_tool"]
METHOD_ALIASES = {
    "bm25": "bm25_tool",
    "dense": "dense_tool",
    "pack": "pack_tool",
}
METHOD_DISPLAY_MAIN = {
    "bm25_tool": "BM25",
    "dense_tool": "Dense",
    "pack_tool": "PACK",
}
METHOD_DISPLAY_ABLATION = {
    "dense_tool": "Dense",
    "pack_tool": "PACK",
}
_FIGURE_RC: Dict[str, Any] = {
    "font.size": 8,
    "axes.titlesize": 8,
    "axes.labelsize": 8,
    "xtick.labelsize": 7,
    "ytick.labelsize": 7,
    "legend.fontsize": 7,
}
# In-memory caches.
_SENTENCE_MODEL_CACHE: Dict[Tuple[str, bool, Optional[str]], Any] = {}
_PACK_HANDLE_CACHE: Dict[Tuple[str, int, str, Optional[str], bool], Dict[str, Any]] = {}
_DENSE_HANDLE_CACHE: Dict[Tuple[str, str, Optional[str], bool], Dict[str, Any]] = {}


# ---------------------------------------------------------------------------
# Generic helpers
# ---------------------------------------------------------------------------

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


def _as_int(value: Any, default: int, *, min_value: Optional[int] = None) -> int:
    try:
        out = int(value)
    except Exception:
        out = int(default)
    if min_value is not None and out < min_value:
        out = int(min_value)
    return out


def _display_method(method_id: str, *, context: str = "main") -> str:
    if context == "ablation":
        return METHOD_DISPLAY_ABLATION.get(method_id, METHOD_DISPLAY_MAIN.get(method_id, method_id))
    return METHOD_DISPLAY_MAIN.get(method_id, method_id)


def _normalize_methods(opts: Dict[str, Any]) -> Tuple[Optional[List[str]], Optional[str]]:
    raw = str(opts.get("methods", "") or "").strip().lower()
    if not raw:
        return list(DEFAULT_METHODS), None
    out: List[str] = []
    for tok in [x.strip() for x in raw.split(",") if x.strip()]:
        mid = METHOD_ALIASES.get(tok, tok)
        if mid == "all":
            out.extend(METHOD_IDS)
            continue
        out.append(mid)
    dedup = list(dict.fromkeys(out))
    unknown = [m for m in dedup if m not in METHOD_IDS]
    if unknown:
        return None, f"Unknown methods: {','.join(unknown)}. Allowed: {','.join(METHOD_IDS)}"
    return dedup, None


# ---------------------------------------------------------------------------
# Retrieval methods
# ---------------------------------------------------------------------------

def _rank_from_list(oid_list: Sequence[str], gold_oid: str) -> Optional[int]:
    try:
        return list(oid_list).index(gold_oid) + 1
    except ValueError:
        return None


def _metrics_from_ranks(ranks: Sequence[int]) -> Dict[str, float]:
    n = len(ranks)
    if n <= 0:
        return {"MRR": 0.0, "P@1": 0.0, "Hit@5": 0.0, "Hit@10": 0.0}
    return {
        "MRR": float(sum((1.0 / r) for r in ranks) / n),
        "P@1": float(sum(1 for r in ranks if r == 1) / n),
        "Hit@5": float(sum(1 for r in ranks if r <= 5) / n),
        "Hit@10": float(sum(1 for r in ranks if r <= 10) / n),
    }


def _run_bm25_method(tasks: List[Dict[str, Any]], opts: Dict[str, Any]) -> Dict[str, Any]:
    top_k_files = _as_int(opts.get("top_k_files"), DEFAULT_TOP_K_FILES, min_value=1)
    per_query: List[Dict[str, Any]] = []
    ranks: List[int] = []
    exes_by_cid: Dict[str, List[str]] = {}

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

        prompt = str(task.get("prompt") or "").strip()
        if not prompt:
            continue

        t0 = time.perf_counter_ns()
        out = api.retrieve(
            "file_search",
            exes,
            {
                "prompt": prompt,
                "top_k": int(top_k_files),
                "backend": "bm25",
                "include_string_rankings": False,
            },
        ) or {}
        q_ms = (time.perf_counter_ns() - t0) / 1_000_000.0

        cands = ((out.get("results") or {}).get("candidates") or []) if isinstance(out, dict) else []
        ranked = [str(c.get("oid") or "") for c in cands if isinstance(c, dict) and str(c.get("oid") or "")]
        ranked = ranked[:top_k_files]

        rank = _rank_from_list(ranked, str(task.get("gold_oid") or ""))
        if rank is None:
            rank = top_k_files + 1
        ranks.append(rank)

        per_query.append(
            {
                "task_id": task.get("task_id"),
                "cid": cid,
                "collection": task.get("collection"),
                "component": task.get("component"),
                "gold_oid": task.get("gold_oid"),
                "rank": int(rank),
                "runtime_ms": float(f"{q_ms:.3f}"),
            }
        )

    return {
        "method": "bm25_tool",
        "attempted_queries": len(per_query),
        "global_metrics": _metrics_from_ranks(ranks),
        "per_query": per_query,
    }


def _strings_for_oid(oid: str) -> str:
    """Return all embedded strings for an OID as a single concatenated text."""
    raw = api.get_field("strings", oid, oid) or {}
    parts: List[str] = []
    for s in raw.values():
        if isinstance(s, str):
            t = s.strip()
            if t:
                parts.append(t)
    return " ".join(parts)


def _get_sentence_model(model_id: str, local_files_only: bool, revision: Optional[str] = None) -> Any:
    key = (model_id, bool(local_files_only), revision)
    if key in _SENTENCE_MODEL_CACHE:
        return _SENTENCE_MODEL_CACHE[key]
    if SentenceTransformer is None:
        raise RuntimeError("sentence_transformers is not available")
    try:
        model = SentenceTransformer(model_id, local_files_only=bool(local_files_only), revision=revision)
    except TypeError:
        model = SentenceTransformer(model_id)
    _SENTENCE_MODEL_CACHE[key] = model
    return model


def _prepare_pack_handle(cid: str, exes: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    if np is None:
        return {"error": "numpy is not available"}

    pack_budget_tokens = _as_int(
        opts.get("pack_budget_tokens"), DEFAULT_PACK_BUDGET_TOKENS, min_value=32
    )
    model_id = str(opts.get("dense_model_id", DEFAULT_DENSE_MODEL_ID) or DEFAULT_DENSE_MODEL_ID).strip()
    model_revision: Optional[str] = str(opts.get("dense_model_revision", DEFAULT_DENSE_MODEL_REVISION) or DEFAULT_DENSE_MODEL_REVISION).strip() or None

    try:
        from oxide.modules.analyzers.file_search import module_interface as file_search_module
    except Exception as e:
        return {"error": f"failed to import file_search analyzer module_interface: {e}"}
    local_files_only = _as_bool(opts.get("local_files_only"), DEFAULT_LOCAL_FILES_ONLY)

    key = (str(cid), int(pack_budget_tokens), model_id, model_revision, bool(local_files_only))
    cached = _PACK_HANDLE_CACHE.get(key)
    if cached is not None:
        return cached

    try:
        packed_docs = file_search_module.build_packed_docs_for_oids(
            exes,
            pack_budget_tokens=int(pack_budget_tokens),
        )
    except Exception as e:
        return {"error": f"failed to build packed docs: {e}"}

    docs = [str((packed_docs or {}).get(oid, "") or "") for oid in exes]
    nonempty = [bool(d.strip()) for d in docs]
    if not any(nonempty):
        return {"error": "packed docs are all empty"}

    try:
        model = _get_sentence_model(model_id, local_files_only, revision=model_revision)
    except Exception as e:
        return {"error": f"failed loading sentence model: {e}"}

    try:
        emb = model.encode(
            docs,
            batch_size=32,
            show_progress_bar=False,
            normalize_embeddings=True,
        )
    except Exception as e:
        return {"error": f"failed encoding packed docs: {e}"}

    emb_mat = np.asarray(emb, dtype=np.float32)
    if emb_mat.ndim != 2 or emb_mat.shape[0] != len(exes):
        return {"error": "invalid packed embedding matrix shape"}

    handle = {
        "oids": list(exes),
        "emb": emb_mat,
        "nonempty": np.asarray(nonempty, dtype=bool),
        "model": model,
    }
    _PACK_HANDLE_CACHE[key] = handle
    return handle


def _run_pack_method(tasks: List[Dict[str, Any]], opts: Dict[str, Any]) -> Dict[str, Any]:
    if np is None:
        return {"method": "pack_tool", "error": "numpy is not available"}

    top_k_files = _as_int(opts.get("top_k_files"), DEFAULT_TOP_K_FILES, min_value=1)
    per_query: List[Dict[str, Any]] = []
    ranks: List[int] = []

    tasks_by_cid: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    for t in tasks:
        cid = str(t.get("cid") or "")
        if cid:
            tasks_by_cid[cid].append(t)

    for cid, cid_tasks in tasks_by_cid.items():
        exes = filter_executables(list(api.expand_oids(cid) or []))
        if not exes:
            continue

        handle = _prepare_pack_handle(cid, exes, opts)
        if handle.get("error"):
            return {"method": "pack_tool", "error": str(handle.get("error"))}

        oids = list(handle.get("oids") or [])
        emb_mat = np.asarray(handle.get("emb"), dtype=np.float32)
        nonempty = np.asarray(handle.get("nonempty"), dtype=bool)
        model = handle.get("model")

        if emb_mat.ndim != 2 or emb_mat.shape[0] != len(oids):
            return {"method": "pack_tool", "error": "invalid packed embedding matrix shape"}
        if nonempty.ndim != 1 or nonempty.shape[0] != len(oids):
            return {"method": "pack_tool", "error": "invalid packed nonempty mask shape"}
        if model is None:
            return {"method": "pack_tool", "error": "missing packed model handle"}

        for task in cid_tasks:
            prompt = str(task.get("prompt") or "").strip()
            if not prompt:
                continue

            t0 = time.perf_counter_ns()
            try:
                q_emb = model.encode(
                    prompt,
                    show_progress_bar=False,
                    normalize_embeddings=True,
                )
            except Exception as e:
                return {"method": "pack_tool", "error": f"pack query failed: {e}"}

            q_vec = np.asarray(q_emb, dtype=np.float32)
            if q_vec.ndim == 2:
                if q_vec.shape[0] != 1:
                    return {"method": "pack_tool", "error": "invalid query embedding shape"}
                q_vec = q_vec[0]
            if q_vec.ndim != 1 or q_vec.shape[0] != emb_mat.shape[1]:
                return {"method": "pack_tool", "error": "invalid query embedding shape"}

            scores = emb_mat @ q_vec
            if scores.ndim != 1 or scores.shape[0] != len(oids):
                return {"method": "pack_tool", "error": "invalid PACK score vector shape"}

            order = np.argsort(scores)[::-1]
            ranked = [str(oids[i]) for i in order if bool(nonempty[i])]
            ranked = ranked[:top_k_files]
            q_ms = (time.perf_counter_ns() - t0) / 1_000_000.0

            rank = _rank_from_list(ranked, str(task.get("gold_oid") or ""))
            if rank is None:
                rank = top_k_files + 1
            ranks.append(rank)

            per_query.append(
                {
                    "task_id": task.get("task_id"),
                    "cid": cid,
                    "collection": task.get("collection"),
                    "component": task.get("component"),
                    "gold_oid": task.get("gold_oid"),
                    "rank": int(rank),
                    "runtime_ms": float(f"{q_ms:.3f}"),
                }
            )

    return {
        "method": "pack_tool",
        "attempted_queries": len(per_query),
        "global_metrics": _metrics_from_ranks(ranks),
        "per_query": per_query,
    }


def _prepare_dense_handle(cid: str, exes: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Build a dense-file index over raw string concatenations (no IDF packing)."""
    if np is None:
        return {"error": "numpy is not available"}

    model_id = str(opts.get("dense_model_id", DEFAULT_DENSE_MODEL_ID) or DEFAULT_DENSE_MODEL_ID).strip()
    model_revision: Optional[str] = str(opts.get("dense_model_revision", DEFAULT_DENSE_MODEL_REVISION) or DEFAULT_DENSE_MODEL_REVISION).strip() or None
    local_files_only = _as_bool(opts.get("local_files_only"), DEFAULT_LOCAL_FILES_ONLY)

    key = (str(cid), model_id, model_revision, bool(local_files_only))
    cached = _DENSE_HANDLE_CACHE.get(key)
    if cached is not None:
        return cached

    try:
        model = _get_sentence_model(model_id, local_files_only, revision=model_revision)
    except Exception as e:
        return {"error": f"failed loading sentence model: {e}"}

    docs = [_strings_for_oid(oid) for oid in exes]
    nonempty = [bool(d.strip()) for d in docs]

    try:
        emb = model.encode(
            docs,
            batch_size=32,
            show_progress_bar=False,
            normalize_embeddings=True,
        )
    except Exception as e:
        return {"error": f"failed encoding raw docs: {e}"}

    emb_mat = np.asarray(emb, dtype=np.float32)
    if emb_mat.ndim != 2 or emb_mat.shape[0] != len(exes):
        return {"error": "invalid dense embedding matrix shape"}

    handle = {
        "oids": list(exes),
        "emb": emb_mat,
        "nonempty": np.asarray(nonempty, dtype=bool),
        "model": model,
    }
    _DENSE_HANDLE_CACHE[key] = handle
    return handle


def _run_dense_method(tasks: List[Dict[str, Any]], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Dense retrieval over raw string concatenations for the packing ablation."""
    if np is None:
        return {"method": "dense_tool", "error": "numpy is not available"}

    top_k_files = _as_int(opts.get("top_k_files"), DEFAULT_TOP_K_FILES, min_value=1)
    per_query: List[Dict[str, Any]] = []
    ranks: List[int] = []

    tasks_by_cid: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    for t in tasks:
        cid = str(t.get("cid") or "")
        if cid:
            tasks_by_cid[cid].append(t)

    for cid, cid_tasks in tasks_by_cid.items():
        exes = filter_executables(list(api.expand_oids(cid) or []))
        if not exes:
            continue

        handle = _prepare_dense_handle(cid, exes, opts)
        if handle.get("error"):
            return {"method": "dense_tool", "error": str(handle.get("error"))}

        oids = list(handle.get("oids") or [])
        emb_mat = np.asarray(handle.get("emb"), dtype=np.float32)
        nonempty = np.asarray(handle.get("nonempty"), dtype=bool)
        model = handle.get("model")

        if emb_mat.ndim != 2 or emb_mat.shape[0] != len(oids):
            return {"method": "dense_tool", "error": "invalid dense embedding matrix shape"}
        if model is None:
            return {"method": "dense_tool", "error": "missing dense model handle"}

        for task in cid_tasks:
            prompt = str(task.get("prompt") or "").strip()
            if not prompt:
                continue

            t0 = time.perf_counter_ns()
            try:
                q_emb = model.encode(prompt, show_progress_bar=False, normalize_embeddings=True)
            except Exception as e:
                return {"method": "dense_tool", "error": f"dense query failed: {e}"}

            q_vec = np.asarray(q_emb, dtype=np.float32)
            if q_vec.ndim == 2:
                q_vec = q_vec[0]
            if q_vec.ndim != 1 or q_vec.shape[0] != emb_mat.shape[1]:
                return {"method": "dense_tool", "error": "invalid query embedding shape"}

            scores = emb_mat @ q_vec
            order = np.argsort(scores)[::-1]
            ranked = [str(oids[i]) for i in order if bool(nonempty[i])]
            ranked = ranked[:top_k_files]
            q_ms = (time.perf_counter_ns() - t0) / 1_000_000.0

            rank = _rank_from_list(ranked, str(task.get("gold_oid") or ""))
            if rank is None:
                rank = top_k_files + 1
            ranks.append(rank)

            per_query.append(
                {
                    "task_id": task.get("task_id"),
                    "cid": cid,
                    "collection": task.get("collection"),
                    "component": task.get("component"),
                    "gold_oid": task.get("gold_oid"),
                    "rank": int(rank),
                    "runtime_ms": float(f"{q_ms:.3f}"),
                }
            )

    return {
        "method": "dense_tool",
        "attempted_queries": len(per_query),
        "global_metrics": _metrics_from_ranks(ranks),
        "per_query": per_query,
    }


def _run_method(method_id: str, tasks: List[Dict[str, Any]], opts: Dict[str, Any]) -> Dict[str, Any]:
    if method_id == "bm25_tool":
        return _run_bm25_method(tasks, opts)
    if method_id == "dense_tool":
        return _run_dense_method(tasks, opts)
    if method_id == "pack_tool":
        return _run_pack_method(tasks, opts)
    return {"method": method_id, "error": f"unknown method: {method_id}"}


# ---------------------------------------------------------------------------
# Public: E1 tool experiment
# ---------------------------------------------------------------------------

def _per_component_from_per_method(
    per_method: Dict[str, Dict[str, Any]],
    top_k_files: int,
) -> List[Dict[str, Any]]:
    """
    Aggregate per-query ranks into per-component MRR/P@1/Hit@5/Hit@10 for each method.
    Returns rows sorted alphabetically by component name.
    """
    # Collect all component names across all methods.
    components: List[str] = []
    seen_comp = set()
    for mid, result in per_method.items():
        for q in (result.get("per_query") or []):
            comp = str(q.get("component") or "").strip()
            if comp and comp not in seen_comp:
                seen_comp.add(comp)
                components.append(comp)
    components.sort()

    rows: List[Dict[str, Any]] = []
    for comp in components:
        row: Dict[str, Any] = {"component": comp}
        for mid, result in per_method.items():
            ranks: List[int] = []
            for q in (result.get("per_query") or []):
                if str(q.get("component") or "").strip() != comp:
                    continue
                try:
                    ranks.append(int(q.get("rank", top_k_files + 1)))
                except Exception:
                    ranks.append(top_k_files + 1)
            if ranks:
                row[mid] = _metrics_from_ranks(ranks)
            else:
                row[mid] = None
        rows.append(row)
    return rows


def tool_eval_main(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Run the §5.1 retrieval benchmark (BM25 / Dense / PACK).

    Options:
      comp_path   -- ground-truth JSON (default: fuse_data/openwrt-dataset/fuse_ground_truth.json)
      prompt_path -- prompt JSON (default: fuse_data/descriptions/component_descriptions.json)
      methods     -- comma list; default runs all three file-level methods.
                     Pass methods=bm25_tool,pack_tool for §5.1 main table only.
                     Pass methods=dense_tool,pack_tool for §5.1 packing ablation only.
      top_k_files -- ranking depth (default: 1_000_000)
      components  -- optional comma list filter
      collections -- optional comma list filter
      outdir      -- write artifact directory (optional)
    """
    comp_path = str(opts.get("comp_path", DEFAULT_COMP_PATH) or DEFAULT_COMP_PATH).strip()
    prompt_path = str(opts.get("prompt_path", DEFAULT_PROMPT_PATH) or DEFAULT_PROMPT_PATH).strip()
    top_k_files = _as_int(opts.get("top_k_files"), DEFAULT_TOP_K_FILES, min_value=1)

    try:
        gt = create_ground_truth(comp_path)
    except Exception as e:
        return {"error": f"failed to load comp_path '{comp_path}': {e}"}
    try:
        prompt_map = load_prompt_map(prompt_path)
    except Exception as e:
        return {"error": f"failed to load prompt_path '{prompt_path}': {e}"}

    methods, m_err = _normalize_methods(opts)
    if m_err:
        return {"error": m_err}
    if methods is None:
        return {"error": "no methods selected"}

    tasks = build_eval_tasks(gt, prompt_map)
    tasks = apply_task_filters(
        tasks,
        components=parse_csv_set(opts.get("components")),
        collections=parse_csv_set(opts.get("collections")),
    )
    if not tasks:
        return {"error": "no evaluation tasks generated (check filters and prompt coverage)"}

    per_method: Dict[str, Dict[str, Any]] = {}
    for mid in methods:
        LOGGER.info("tool_eval_main: running method %s (%d tasks)", mid, len(tasks))
        per_method[mid] = _run_method(mid, tasks, opts)
        if per_method[mid].get("error"):
            return {
                "error": f"method '{mid}' failed: {per_method[mid].get('error')}",
                "partial": per_method,
            }

    # §5.1 main table: BM25 / PACK
    main_order = ["bm25_tool", "pack_tool"]
    tab_e1_main: List[Dict[str, Any]] = []
    for mid in [m for m in main_order if m in per_method]:
        gm = (per_method[mid] or {}).get("global_metrics") or {}
        tab_e1_main.append(
            {
                "method": _display_method(mid, context="main"),
                "MRR": gm.get("MRR"),
                "P@1": gm.get("P@1"),
                "Hit@5": gm.get("Hit@5"),
                "Hit@10": gm.get("Hit@10"),
            }
        )

    # §5.1 packing ablation table: Dense / PACK
    ablation_order = ["dense_tool", "pack_tool"]
    tab_ablation: List[Dict[str, Any]] = []
    for mid in [m for m in ablation_order if m in per_method]:
        gm = (per_method[mid] or {}).get("global_metrics") or {}
        tab_ablation.append(
            {
                "method": _display_method(mid, context="ablation"),
                "MRR": gm.get("MRR"),
                "P@1": gm.get("P@1"),
                "Hit@5": gm.get("Hit@5"),
                "Hit@10": gm.get("Hit@10"),
            }
        )

    # §5.3 per-component retrieval breakdown
    tab_per_component = _per_component_from_per_method(per_method, top_k_files)

    payload = {
        "experiment": "tool_eval_main",
        "task_count": len(tasks),
        "methods": methods,
        "sources": {
            "comp_path": comp_path,
            "prompt_path": prompt_path,
            "components": parse_csv_set(opts.get("components")),
            "collections": parse_csv_set(opts.get("collections")),
        },
        "tables": {
            "tab_e1_main": tab_e1_main,
            "tab_ablation_packing": tab_ablation,
            "tab_per_component_retrieval": tab_per_component,
        },
        "per_method": per_method,
    }

    artifact = write_json_artifact(str(opts.get("outdir", "") or "").strip(), "tool_eval_main.json", payload)
    if artifact:
        payload["artifact"] = artifact
    return payload


# ---------------------------------------------------------------------------
# §5.3 Per-component retrieval analysis
# ---------------------------------------------------------------------------

def _project_per_component_rows(
    rows: Sequence[Dict[str, Any]],
    methods: Sequence[str],
) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    for row in rows:
        projected: Dict[str, Any] = {"component": row.get("component")}
        for method_id in methods:
            projected[method_id] = row.get(method_id)
        out.append(projected)

    if "pack_tool" in methods:
        out.sort(
            key=lambda row: float(((row.get("pack_tool") or {}).get("MRR")) or 0.0),
            reverse=True,
        )
    return out

def component_analysis(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Per-component retrieval MRR/P@1/Hit@5/Hit@10 for the raw-tool columns.

    By default, this reuses the retrieval artifact emitted by tool_eval_main.
    If that artifact is unavailable, it runs tool_eval_main once and projects
    the per-component table from that result.

    Options:
      retrieval_path -- existing tool_eval_main.json artifact to reuse
      methods     -- default: bm25_tool,pack_tool
      outdir      -- write artifact directory (optional)
    """
    methods, m_err = _normalize_methods(opts)
    if m_err:
        return {"error": m_err}
    if not methods:
        return {"error": "no methods selected"}

    retrieval_path = str(
        opts.get("retrieval_path")
        or Path(DEFAULT_OUTDIR) / "retrieval" / "tool_eval_main.json"
    ).strip()

    retrieval_payload: Optional[Dict[str, Any]] = None
    retrieval_src = Path(retrieval_path).expanduser()
    if retrieval_src.exists():
        try:
            retrieval_payload = load_json_object(retrieval_src)
        except Exception as err:
            return {"error": f"failed to load retrieval_path '{retrieval_src}': {err}"}
    else:
        rerun_opts = dict(opts)
        rerun_opts["methods"] = ",".join(methods)
        LOGGER.info("component_analysis: retrieval artifact missing, running tool_eval_main once")
        retrieval_payload = tool_eval_main(args, rerun_opts)
        if retrieval_payload.get("error"):
            return {"error": f"tool_eval_main failed: {retrieval_payload.get('error')}"}

    tables = (retrieval_payload.get("tables") or {}) if isinstance(retrieval_payload, dict) else {}
    raw_rows = tables.get("tab_per_component_retrieval") or []
    if not isinstance(raw_rows, list) or not raw_rows:
        return {"error": "tab_per_component_retrieval missing from retrieval artifact"}

    tab_per_component = _project_per_component_rows(raw_rows, methods)
    per_method = {
        method_id: {"global_metrics": ((retrieval_payload.get("per_method") or {}).get(method_id) or {}).get("global_metrics")}
        for method_id in methods
    }

    payload = {
        "analysis": "component_analysis",
        "task_count": retrieval_payload.get("task_count"),
        "methods": methods,
        "tables": {
            "tab_per_component_retrieval": tab_per_component,
        },
        "per_method": per_method,
        "sources": {
            "retrieval_path": str(retrieval_src) if retrieval_src.exists() else retrieval_payload.get("artifact"),
        },
    }
    artifact = write_json_artifact(str(opts.get("outdir", "") or "").strip(), "component_analysis.json", payload)
    if artifact:
        payload["artifact"] = artifact
    return payload


# ---------------------------------------------------------------------------
# Paper report bundle
# ---------------------------------------------------------------------------

def eval_paper_report(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Assemble a paper-ready report from existing experiment artifacts.

    Options:
      outdir               -- write directory (default: out/file_localization_tps)
      retrieval_path       -- tool_eval_main.json path
      component_path       -- component_analysis.json path
      function_eval_path   -- query_function_eval_main.json path
      agent_report_path    -- agentic_paper_report.json path
    """
    outdir = str(opts.get("outdir", DEFAULT_OUTDIR) or DEFAULT_OUTDIR).strip()
    tables: Dict[str, Any] = {}
    sources: Dict[str, Any] = {}

    def _maybe_load(path_value: str, label: str) -> Optional[Dict[str, Any]]:
        if not path_value:
            return None
        path = Path(path_value).expanduser()
        if not path.exists():
            LOGGER.warning("eval_paper_report: %s not found at %s", label, path)
            return None
        try:
            payload = load_json_object(path)
        except Exception as err:
            LOGGER.warning("eval_paper_report: failed loading %s: %s", label, err)
            return None
        sources[f"{label}_path"] = str(path)
        return payload

    retrieval_path = str(
        opts.get("retrieval_path")
        or (Path(DEFAULT_OUTDIR) / "retrieval" / "tool_eval_main.json")
    ).strip()
    retrieval_payload = _maybe_load(retrieval_path, "retrieval")
    if retrieval_payload is not None:
        retrieval_tables = retrieval_payload.get("tables") or {}
        tables["tab_e1_main"] = retrieval_tables.get("tab_e1_main")
        tables["tab_ablation_packing"] = retrieval_tables.get("tab_ablation_packing")
        tables["tab_per_component_retrieval"] = retrieval_tables.get("tab_per_component_retrieval")

    function_eval_path = str(
        opts.get("function_eval_path")
        or (Path(DEFAULT_OUTDIR) / "query_function_eval" / "query_function_eval_main.json")
    ).strip()
    function_payload = _maybe_load(function_eval_path, "function_eval")
    if function_payload is not None:
        function_tables = function_payload.get("tables") or {}
        tables["tab_function_rank_summary"] = function_tables.get("tab_function_rank_summary")

    component_path = str(
        opts.get("component_path")
        or (Path(DEFAULT_OUTDIR) / "per_component" / "component_analysis.json")
    ).strip()
    component_payload = _maybe_load(component_path, "component")
    if component_payload is not None:
        component_tables = component_payload.get("tables") or {}
        tables["tab_per_component_retrieval"] = component_tables.get("tab_per_component_retrieval")

    agent_report_path = str(opts.get("agent_report_path", DEFAULT_AGENT_REPORT_PATH) or DEFAULT_AGENT_REPORT_PATH).strip()
    agent_payload = _maybe_load(agent_report_path, "agent_report")
    if agent_payload is not None:
        agent_tables = agent_payload.get("tables") or {}
        tables["tab_agent_outcomes"] = agent_tables.get("tab_agent_outcomes")
        tables["tab_agent_effort"] = agent_tables.get("tab_agent_effort")
        tables["tab_per_component_agent"] = agent_tables.get("tab_per_component_agent")
        tables["tab_robustness_agent"] = agent_tables.get("tab_robustness_agent")

    report = {
        "report_type": "eval_paper_report",
        "tables": tables,
        "sources": sources,
    }

    artifact = write_json_artifact(outdir, "eval_paper_report.json", report)
    if artifact:
        report["artifact"] = artifact
    return report


exports = [
    tool_eval_main,
    component_analysis,
    eval_paper_report,
]
