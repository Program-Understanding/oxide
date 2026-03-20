from __future__ import annotations

"""
Primary experiment plugin for the FUSE paper.

Covers all retrieval and agent experiments referenced in evaluation.tex:
- §5.1 Standalone retrieval: BM25 / Dense (no packing) / Func-Emb / FUSE via tool_eval_main()
- §5.3 Per-component retrieval MRR: component_analysis()
- §5.4 Robustness: eval_robustness() with prompt variant JSON
- §5.2 Agent benchmark tables: agent_eval_main() reading agentic_paper_report.json
- Full paper report bundle: eval_paper_report()

This module does not import other experiment plugins.
"""

import json
import logging
import time
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

from oxide.core import api

try:
    import numpy as np
except Exception:
    np = None  # type: ignore

try:
    from sentence_transformers import SentenceTransformer
except Exception:
    SentenceTransformer = None  # type: ignore


NAME = "fuse"
LOGGER = logging.getLogger(NAME)
if not LOGGER.handlers:
    _h = logging.StreamHandler()
    _h.setFormatter(logging.Formatter("[%(asctime)s] %(levelname)s %(name)s: %(message)s", "%H:%M:%S"))
    LOGGER.addHandler(_h)
LOGGER.setLevel(logging.INFO)
LOGGER.propagate = False

DEFAULT_COMP_PATH = "fuse_data/openwrt-dataset/fuse_ground_truth.json"
DEFAULT_PROMPT_PATH = "fuse_data/descriptions/component_descriptions.json"
DEFAULT_OUTDIR = "out/fuse"
DEFAULT_TOP_K_FILES = 1_000_000
DEFAULT_METHODS = ["bm25_tool", "dense_tool", "func_emb_tool", "fuse_tool"]
DEFAULT_CONDITIONS = ["base", "bm25", "fuse", "both"]
DEFAULT_AGENT_REPORT_PATH = "out/agent_eval/20260317_131650/agentic_paper_report.json"
DEFAULT_AGENT_FIRST_JSONL = "out/agent_eval/20260311_183155/agentic_runs_topk10.jsonl"
DEFAULT_DENSE_MODEL_ID = "sentence-transformers/all-MiniLM-L6-v2"
DEFAULT_PACK_BUDGET_TOKENS = 512
DEFAULT_LOCAL_FILES_ONLY = True

# dense_tool = same encoder as FUSE but on raw string concat (no packing) — §5.1 ablation.
METHOD_IDS = ["bm25_tool", "dense_tool", "func_emb_tool", "fuse_tool"]
METHOD_ALIASES = {
    "bm25": "bm25_tool",
    "dense": "dense_tool",
    "func": "func_emb_tool",
    "func_emb": "func_emb_tool",
    "function": "func_emb_tool",
    "fuse": "fuse_tool",
}
METHOD_DISPLAY = {
    "bm25_tool": "BM25",
    "dense_tool": "Dense (no packing)",
    "func_emb_tool": "Func-Emb",
    "fuse_tool": "FUSE",
}
_FIGURE_RC: Dict[str, Any] = {
    "font.size": 8,
    "axes.titlesize": 8,
    "axes.labelsize": 8,
    "xtick.labelsize": 7,
    "ytick.labelsize": 7,
    "legend.fontsize": 7,
}
# Default method sets for each experiment
E1_MAIN_METHODS = ["bm25_tool", "func_emb_tool", "fuse_tool"]   # §5.1 main table
E1_ABLATION_METHODS = ["dense_tool", "fuse_tool"]                # §5.1 packing ablation
E1_ALL_METHODS = ["bm25_tool", "dense_tool", "func_emb_tool", "fuse_tool"]  # full run
COMPONENT_DEFAULT_METHODS = ["bm25_tool", "fuse_tool"]           # §5.3 retrieval columns

# In-memory caches.
_SENTENCE_MODEL_CACHE: Dict[Tuple[str, bool], Any] = {}
_FUSE_HANDLE_CACHE: Dict[Tuple[str, int, str, bool], Dict[str, Any]] = {}
_DENSE_HANDLE_CACHE: Dict[Tuple[str, str, bool], Dict[str, Any]] = {}


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


def _as_float(value: Any, default: float) -> float:
    try:
        return float(value)
    except Exception:
        return float(default)


def _mean(values: Sequence[float]) -> float:
    if not values:
        return 0.0
    return float(sum(values) / max(len(values), 1))


def _write_json_artifact(outdir: str, filename: str, payload: Dict[str, Any]) -> Optional[str]:
    outdir = str(outdir or "").strip()
    if not outdir:
        return None
    p = Path(outdir).expanduser()
    p.mkdir(parents=True, exist_ok=True)
    target = p / filename
    target.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    return str(target)


def _parse_csv_set(value: Any) -> List[str]:
    if value is None:
        return []
    if isinstance(value, (list, tuple, set)):
        items = [str(x).strip() for x in value if str(x).strip()]
    else:
        items = [x.strip() for x in str(value).split(",") if x.strip()]
    return list(dict.fromkeys(items))


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


def _normalize_conditions(opts: Dict[str, Any]) -> Tuple[Optional[List[str]], Optional[str]]:
    raw = opts.get("conditions")
    if raw is None:
        return list(DEFAULT_CONDITIONS), None
    if isinstance(raw, str):
        items = [x.strip().lower() for x in raw.split(",") if x.strip()]
    else:
        items = [str(x).strip().lower() for x in (raw or []) if str(x).strip()]
    if not items:
        return list(DEFAULT_CONDITIONS), None
    alias = {"baseline": "bm25"}
    items = [alias.get(x, x) for x in items]
    allowed = set(DEFAULT_CONDITIONS)
    bad = [x for x in items if x not in allowed]
    if bad:
        return None, f"Invalid conditions: {','.join(sorted(set(bad)))}"
    return list(dict.fromkeys(items)), None


# ---------------------------------------------------------------------------
# Dataset/task loading
# ---------------------------------------------------------------------------

def _filter_executables(oids: Sequence[str]) -> List[str]:
    out: List[str] = []
    for oid in oids:
        cat = api.get_field("categorize", oid, oid)
        if cat != "executable":
            continue
        names = list(api.get_names_from_oid(oid))
        if any((".so" in n) or (".ko" in n) for n in names):
            continue
        out.append(str(oid))
    return out


def _build_ground_truth_for_collection(exes: Sequence[str], basename_map: Dict[str, List[str]]) -> Dict[str, str]:
    base_to_oid: Dict[str, str] = {}
    for oid in exes:
        for name in api.get_names_from_oid(oid):
            base = Path(str(name)).name.strip()
            if base and base not in base_to_oid:
                base_to_oid[base] = str(oid)

    col_gt: Dict[str, str] = {}
    for component, basenames in basename_map.items():
        for base in basenames:
            oid = base_to_oid.get(base)
            if oid:
                col_gt[component] = oid
                break
    return col_gt


def create_ground_truth(comp_path: str) -> Dict[str, Dict[str, str]]:
    data = json.loads(Path(comp_path).read_text(encoding="utf-8"))
    out: Dict[str, Dict[str, str]] = {}

    for cid in api.collection_cids() or []:
        colname = api.get_colname_from_oid(cid)
        if colname not in data:
            continue
        raw = data[colname]
        if not isinstance(raw, dict):
            continue

        basename_map: Dict[str, List[str]] = {}
        for component, paths in raw.items():
            if not isinstance(component, str):
                continue
            vals = paths if isinstance(paths, list) else [paths]
            ordered: List[str] = []
            seen = set()
            for p in vals:
                base = Path(str(p)).name.strip()
                if not base or base in seen:
                    continue
                seen.add(base)
                ordered.append(base)
            if ordered:
                basename_map[component] = ordered

        exes = _filter_executables(list(api.expand_oids(cid) or []))
        gt_col = _build_ground_truth_for_collection(exes, basename_map)
        if gt_col:
            out[str(cid)] = gt_col

    return out


def load_prompt_map(prompt_path: str) -> Dict[str, str]:
    raw = json.loads(Path(prompt_path).read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        return {}
    out: Dict[str, str] = {}
    for k, v in raw.items():
        if isinstance(k, str) and isinstance(v, str) and v.strip():
            out[k] = v.strip()
    return out


def build_eval_tasks(ground_truth: Dict[str, Dict[str, str]], prompt_map: Dict[str, str]) -> List[Dict[str, Any]]:
    tasks: List[Dict[str, Any]] = []
    for cid in sorted(ground_truth.keys(), key=lambda c: str(api.get_colname_from_oid(c) or c)):
        colname = api.get_colname_from_oid(cid)
        for component, gold_oid in sorted(ground_truth[cid].items(), key=lambda kv: kv[0]):
            prompt = str(prompt_map.get(component, "") or "").strip()
            if not prompt:
                continue
            tasks.append(
                {
                    "task_id": f"{cid}:{component}",
                    "cid": str(cid),
                    "collection": str(colname or cid),
                    "component": component,
                    "prompt": prompt,
                    "gold_oid": str(gold_oid),
                }
            )
    return tasks


def _apply_task_filters(
    tasks: Sequence[Dict[str, Any]],
    *,
    components: Sequence[str],
    collections: Sequence[str],
) -> List[Dict[str, Any]]:
    comp_set = {str(x).strip().lower() for x in components if str(x).strip()}
    col_set = {str(x).strip().lower() for x in collections if str(x).strip()}
    if not comp_set and not col_set:
        return list(tasks)

    out: List[Dict[str, Any]] = []
    for task in tasks:
        comp = str(task.get("component") or "").strip().lower()
        col = str(task.get("collection") or "").strip().lower()
        if comp_set and comp not in comp_set:
            continue
        if col_set and col not in col_set:
            continue
        out.append(task)
    return out


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
        return {"P@1": 0.0, "Hit@2": 0.0, "Hit@5": 0.0, "MRR": 0.0}
    return {
        "P@1": float(sum(1 for r in ranks if r == 1) / n),
        "Hit@2": float(sum(1 for r in ranks if r <= 2) / n),
        "Hit@5": float(sum(1 for r in ranks if r <= 5) / n),
        "MRR": float(sum((1.0 / r) for r in ranks) / n),
    }


def _aggregate_function_candidates(qf_out: Dict[str, Any], top_k_files: int) -> List[str]:
    # Preferred path: file_scores emitted by query_function.
    file_scores = qf_out.get("file_scores") if isinstance(qf_out, dict) else None
    if isinstance(file_scores, dict) and file_scores:
        ranked = sorted(
            ((str(oid), float(score)) for oid, score in file_scores.items() if score is not None),
            key=lambda x: x[1],
            reverse=True,
        )
        return [oid for oid, _ in ranked[:top_k_files]]

    # Fallback: aggregate top function score per file.
    best_by_oid: Dict[str, float] = {}
    cands = ((qf_out.get("results") or {}).get("candidates") or []) if isinstance(qf_out, dict) else []
    if isinstance(cands, list):
        for c in cands:
            if not isinstance(c, dict):
                continue
            oid = str(c.get("oid") or "").strip()
            score = c.get("score")
            if not oid or score is None:
                continue
            sc = float(score)
            prev = best_by_oid.get(oid)
            if prev is None or sc > prev:
                best_by_oid[oid] = sc

    ranked2 = sorted(best_by_oid.items(), key=lambda x: x[1], reverse=True)
    return [oid for oid, _ in ranked2[:top_k_files]]


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
            exes = _filter_executables(list(api.expand_oids(cid) or []))
            exes_by_cid[cid] = exes
        if not exes:
            continue

        prompt = str(task.get("prompt") or "").strip()
        if not prompt:
            continue

        t0 = time.perf_counter_ns()
        out = api.retrieve(
            "bm25",
            exes,
            {
                "prompt": prompt,
                "top_k": int(top_k_files),
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


def _run_func_emb_method(tasks: List[Dict[str, Any]], opts: Dict[str, Any]) -> Dict[str, Any]:
    top_k_files = _as_int(opts.get("top_k_files"), DEFAULT_TOP_K_FILES, min_value=1)
    top_k_funcs = _as_int(opts.get("top_k_funcs"), 1, min_value=1)
    file_agg = str(opts.get("func_file_agg", "top1") or "top1").strip().lower()
    if file_agg not in {"top1", "mean", "attn"}:
        file_agg = "top1"
    attn_tau = _as_float(opts.get("func_attn_tau"), 0.07)

    per_query: List[Dict[str, Any]] = []
    ranks: List[int] = []
    exes_by_cid: Dict[str, List[str]] = {}

    for task in tasks:
        cid = str(task.get("cid") or "")
        if not cid:
            continue
        exes = exes_by_cid.get(cid)
        if exes is None:
            exes = _filter_executables(list(api.expand_oids(cid) or []))
            exes_by_cid[cid] = exes
        if not exes:
            continue

        prompt = str(task.get("prompt") or "").strip()
        if not prompt:
            continue

        t0 = time.perf_counter_ns()
        qf_out = api.retrieve(
            "query_function",
            exes,
            {
                "query": prompt,
                "top_k": int(top_k_funcs),
                "return_file_embeddings": True,
                "file_agg": file_agg,
                "attn_tau": float(attn_tau),
                "timing": False,
                "progress": False,
            },
        ) or {}
        q_ms = (time.perf_counter_ns() - t0) / 1_000_000.0

        ranked = _aggregate_function_candidates(qf_out, top_k_files)

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
        "method": "func_emb_tool",
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


def _get_sentence_model(model_id: str, local_files_only: bool) -> Any:
    key = (model_id, bool(local_files_only))
    if key in _SENTENCE_MODEL_CACHE:
        return _SENTENCE_MODEL_CACHE[key]
    if SentenceTransformer is None:
        raise RuntimeError("sentence_transformers is not available")
    try:
        model = SentenceTransformer(model_id, local_files_only=bool(local_files_only))
    except TypeError:
        model = SentenceTransformer(model_id)
    _SENTENCE_MODEL_CACHE[key] = model
    return model


def _prepare_fuse_handle(cid: str, exes: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    if np is None:
        return {"error": "numpy is not available"}

    pack_budget_tokens = _as_int(
        opts.get("pack_budget_tokens"), DEFAULT_PACK_BUDGET_TOKENS, min_value=32
    )
    model_id = str(opts.get("dense_model_id", DEFAULT_DENSE_MODEL_ID) or DEFAULT_DENSE_MODEL_ID).strip()
    local_files_only = _as_bool(opts.get("local_files_only"), DEFAULT_LOCAL_FILES_ONLY)

    key = (str(cid), int(pack_budget_tokens), model_id, bool(local_files_only))
    cached = _FUSE_HANDLE_CACHE.get(key)
    if cached is not None:
        return cached

    try:
        from oxide.modules.analyzers.fuse import module_interface as fuse_module
    except Exception as e:
        return {"error": f"failed to import fuse analyzer module_interface: {e}"}

    try:
        packed_docs = fuse_module.build_packed_docs_for_oids(
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
        model = _get_sentence_model(model_id, local_files_only)
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
    _FUSE_HANDLE_CACHE[key] = handle
    return handle


def _run_fuse_method(tasks: List[Dict[str, Any]], opts: Dict[str, Any]) -> Dict[str, Any]:
    if np is None:
        return {"method": "fuse_tool", "error": "numpy is not available"}

    top_k_files = _as_int(opts.get("top_k_files"), DEFAULT_TOP_K_FILES, min_value=1)
    per_query: List[Dict[str, Any]] = []
    ranks: List[int] = []

    tasks_by_cid: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    for t in tasks:
        cid = str(t.get("cid") or "")
        if cid:
            tasks_by_cid[cid].append(t)

    for cid, cid_tasks in tasks_by_cid.items():
        exes = _filter_executables(list(api.expand_oids(cid) or []))
        if not exes:
            continue

        handle = _prepare_fuse_handle(cid, exes, opts)
        if handle.get("error"):
            return {"method": "fuse_tool", "error": str(handle.get("error"))}

        oids = list(handle.get("oids") or [])
        emb_mat = np.asarray(handle.get("emb"), dtype=np.float32)
        nonempty = np.asarray(handle.get("nonempty"), dtype=bool)
        model = handle.get("model")

        if emb_mat.ndim != 2 or emb_mat.shape[0] != len(oids):
            return {"method": "fuse_tool", "error": "invalid packed embedding matrix shape"}
        if nonempty.ndim != 1 or nonempty.shape[0] != len(oids):
            return {"method": "fuse_tool", "error": "invalid packed nonempty mask shape"}
        if model is None:
            return {"method": "fuse_tool", "error": "missing packed model handle"}

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
                return {"method": "fuse_tool", "error": f"fuse analyzer query failed: {e}"}

            q_vec = np.asarray(q_emb, dtype=np.float32)
            if q_vec.ndim == 2:
                if q_vec.shape[0] != 1:
                    return {"method": "fuse_tool", "error": "invalid query embedding shape"}
                q_vec = q_vec[0]
            if q_vec.ndim != 1 or q_vec.shape[0] != emb_mat.shape[1]:
                return {"method": "fuse_tool", "error": "invalid query embedding shape"}

            scores = emb_mat @ q_vec
            if scores.ndim != 1 or scores.shape[0] != len(oids):
                return {"method": "fuse_tool", "error": "invalid FUSE score vector shape"}

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
        "method": "fuse_tool",
        "attempted_queries": len(per_query),
        "global_metrics": _metrics_from_ranks(ranks),
        "per_query": per_query,
    }


def _prepare_dense_handle(cid: str, exes: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Build a dense-file index over raw string concatenations (no IDF packing)."""
    if np is None:
        return {"error": "numpy is not available"}

    model_id = str(opts.get("dense_model_id", DEFAULT_DENSE_MODEL_ID) or DEFAULT_DENSE_MODEL_ID).strip()
    local_files_only = _as_bool(opts.get("local_files_only"), DEFAULT_LOCAL_FILES_ONLY)

    key = (str(cid), model_id, bool(local_files_only))
    cached = _DENSE_HANDLE_CACHE.get(key)
    if cached is not None:
        return cached

    try:
        model = _get_sentence_model(model_id, local_files_only)
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
    """Dense file retrieval over raw string concatenations — the no-packing ablation baseline."""
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
        exes = _filter_executables(list(api.expand_oids(cid) or []))
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
    if method_id == "func_emb_tool":
        return _run_func_emb_method(tasks, opts)
    if method_id == "fuse_tool":
        return _run_fuse_method(tasks, opts)
    return {"method": method_id, "error": f"unknown method: {method_id}"}


# ---------------------------------------------------------------------------
# Public: E1 tool experiment
# ---------------------------------------------------------------------------

def _per_component_from_per_method(
    per_method: Dict[str, Dict[str, Any]],
    top_k_files: int,
) -> List[Dict[str, Any]]:
    """
    Aggregate per-query ranks into per-component MRR/P@1/Hit@5 for each method.
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
    Run the §5.1 retrieval benchmark (BM25 / Dense / Func-Emb / FUSE).

    Options:
      comp_path   -- ground-truth JSON (default: fuse_data/openwrt-dataset/fuse_ground_truth.json)
      prompt_path -- prompt JSON (default: fuse_data/descriptions/component_descriptions.json)
      methods     -- comma list; default runs all four methods.
                     Pass methods=bm25_tool,func_emb_tool,fuse_tool for §5.1 main table only.
                     Pass methods=dense_tool,fuse_tool for §5.1 packing ablation only.
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
    tasks = _apply_task_filters(
        tasks,
        components=_parse_csv_set(opts.get("components")),
        collections=_parse_csv_set(opts.get("collections")),
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

    # §5.1 main table: BM25 / Func-Emb / FUSE
    main_order = ["bm25_tool", "func_emb_tool", "fuse_tool"]
    tab_e1_main: List[Dict[str, Any]] = []
    for mid in [m for m in main_order if m in per_method]:
        gm = (per_method[mid] or {}).get("global_metrics") or {}
        tab_e1_main.append(
            {
                "method": METHOD_DISPLAY.get(mid, mid),
                "MRR": gm.get("MRR"),
                "Hit@2": gm.get("Hit@2"),
                "Hit@5": gm.get("Hit@5"),
                "P@1": gm.get("P@1"),
            }
        )

    # §5.1 packing ablation table: Dense / FUSE
    ablation_order = ["dense_tool", "fuse_tool"]
    tab_ablation: List[Dict[str, Any]] = []
    for mid in [m for m in ablation_order if m in per_method]:
        gm = (per_method[mid] or {}).get("global_metrics") or {}
        tab_ablation.append(
            {
                "method": METHOD_DISPLAY.get(mid, mid),
                "MRR": gm.get("MRR"),
                "Hit@2": gm.get("Hit@2"),
                "Hit@5": gm.get("Hit@5"),
                "P@1": gm.get("P@1"),
            }
        )

    # §5.3 per-component retrieval breakdown
    tab_per_component = _per_component_from_per_method(per_method, top_k_files)

    payload = {
        "experiment": "tool_eval_main",
        "task_count": len(tasks),
        "methods": methods,
        "tables": {
            "tab_e1_main": tab_e1_main,
            "tab_ablation_packing": tab_ablation,
            "tab_per_component_retrieval": tab_per_component,
        },
        "per_method": per_method,
    }

    artifact = _write_json_artifact(str(opts.get("outdir", "") or "").strip(), "tool_eval_main.json", payload)
    if artifact:
        payload["artifact"] = artifact
    return payload


# ---------------------------------------------------------------------------
# Agent summary from JSONL (first agent benchmark)
# ---------------------------------------------------------------------------

def _load_rows_jsonl(path: Path) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    if not path.exists():
        return rows
    for line in path.read_text(encoding="utf-8").splitlines():
        s = line.strip()
        if not s:
            continue
        try:
            obj = json.loads(s)
        except Exception:
            continue
        if isinstance(obj, dict):
            rows.append(obj)
    return rows


def _load_json_object(path: Path) -> Dict[str, Any]:
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except Exception as e:
        raise ValueError(f"failed to parse JSON '{path}': {e}") from e
    if not isinstance(obj, dict):
        raise ValueError(f"JSON root is not an object: {path}")
    return obj


def _select_condition_rows(rows: Sequence[Dict[str, Any]], conditions: Sequence[str]) -> List[Dict[str, Any]]:
    by_cond = {str(row.get("condition") or "").strip().lower(): row for row in rows if isinstance(row, dict)}
    out: List[Dict[str, Any]] = []
    for cond in conditions:
        row = by_cond.get(str(cond).strip().lower())
        if row is not None:
            out.append(row)
    return out


def _stop_reason(row: Dict[str, Any]) -> str:
    explicit = str(row.get("stop_reason") or "").strip().lower()
    if explicit:
        return explicit
    if bool(row.get("parse_error")):
        return "finalizer_parse_error"
    if bool(row.get("answered_unknown")):
        return "answered_unknown"
    return ""


def _is_stopped(row: Dict[str, Any]) -> bool:
    return bool(_stop_reason(row))


def _summarize_agent_rows(rows: List[Dict[str, Any]], conditions: Sequence[str]) -> List[Dict[str, Any]]:
    by_cond: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    for r in rows:
        by_cond[str(r.get("condition") or "")].append(r)

    out: List[Dict[str, Any]] = []
    for cond in conditions:
        cond_rows = by_cond.get(cond, [])
        n = len(cond_rows)
        if n <= 0:
            out.append(
                {
                    "condition": cond,
                    "runs": 0,
                    "success_rate": 0.0,
                    "miss_rate": 0.0,
                    "stopped_rate": 0.0,
                    "mean_retrieve_calls": 0.0,
                    "mean_analysis_tool_calls": 0.0,
                    "mean_tool_calls": 0.0,
                    "mean_total_tokens_completed_only": 0.0,
                }
            )
            continue

        stopped_rows = [r for r in cond_rows if _is_stopped(r)]
        completed_rows = [r for r in cond_rows if not _is_stopped(r)]

        success_count = sum(1 for r in completed_rows if bool(r.get("success")))
        stopped_count = len(stopped_rows)
        miss_count = n - success_count - stopped_count

        mean_retrieve = _mean([float(r.get("retrieve_calls", 0) or 0) for r in cond_rows])
        mean_tool_calls = _mean([float(r.get("total_tool_calls", 0) or 0) for r in cond_rows])
        mean_analysis = _mean(
            [
                float(
                    int(r.get("grep_strings_calls", 0) or 0)
                    + int(r.get("get_function_list_calls", 0) or 0)
                    + int(r.get("get_call_graph_calls", 0) or 0)
                    + int(r.get("get_func_decomp_calls", 0) or 0)
                )
                for r in cond_rows
            ]
        )
        mean_tokens_completed = _mean([float(r.get("total_tokens", 0) or 0) for r in completed_rows])

        out.append(
            {
                "condition": cond,
                "runs": int(n),
                "success_rate": float(f"{(success_count / n):.6f}"),
                "miss_rate": float(f"{(miss_count / n):.6f}"),
                "stopped_rate": float(f"{(stopped_count / n):.6f}"),
                "mean_retrieve_calls": float(f"{mean_retrieve:.6f}"),
                "mean_analysis_tool_calls": float(f"{mean_analysis:.6f}"),
                "mean_tool_calls": float(f"{mean_tool_calls:.6f}"),
                "mean_total_tokens_completed_only": float(f"{mean_tokens_completed:.6f}"),
            }
        )
    return out


def agent_eval_first(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Build first-agent benchmark tables from run-level JSONL.

    Options:
      jsonl_path   -- default: out/agent_eval/20260311_183155/agentic_runs_topk10.jsonl
      conditions   -- comma list (default: base,bm25,fuse,both)
      collections  -- optional collection filter (comma list)
      outdir       -- write artifact directory (optional)
    """
    jsonl_path = str(opts.get("jsonl_path", DEFAULT_AGENT_FIRST_JSONL) or DEFAULT_AGENT_FIRST_JSONL).strip()
    path = Path(jsonl_path).expanduser()
    if not path.exists():
        return {"error": f"jsonl_path not found: {path}"}

    conditions, c_err = _normalize_conditions(opts)
    if c_err:
        return {"error": c_err}
    if conditions is None:
        return {"error": "no conditions selected"}

    rows = _load_rows_jsonl(path)
    if not rows:
        return {"error": f"no rows loaded from {path}"}

    collections_filter = {x.lower() for x in _parse_csv_set(opts.get("collections"))}
    if collections_filter:
        rows = [r for r in rows if str(r.get("collection") or "").strip().lower() in collections_filter]
        if not rows:
            return {"error": "collection filter matched zero rows"}

    summary = _summarize_agent_rows(rows, conditions)
    by_cond = {str(r.get("condition") or ""): r for r in summary}

    outcomes = []
    effort = []
    for cond in conditions:
        r = by_cond.get(cond, {})
        outcomes.append(
            {
                "condition": cond,
                "success_rate": r.get("success_rate"),
                "miss_rate": r.get("miss_rate"),
                "stopped_rate": r.get("stopped_rate"),
                "runs": r.get("runs"),
            }
        )
        effort.append(
            {
                "condition": cond,
                "mean_retrieve_calls": r.get("mean_retrieve_calls"),
                "mean_analysis_tool_calls": r.get("mean_analysis_tool_calls"),
                "mean_tool_calls": r.get("mean_tool_calls"),
                "mean_total_tokens": r.get("mean_total_tokens_completed_only"),
            }
        )

    payload = {
        "experiment": "agent_eval_first",
        "jsonl_path": str(path),
        "run_count": len(rows),
        "task_count": len({str(r.get("task_id") or "") for r in rows if str(r.get("task_id") or "").strip()}),
        "conditions": conditions,
        "tables": {
            "tab_agent_outcomes": outcomes,
            "tab_agent_effort": effort,
        },
        "summary": summary,
    }

    artifact = _write_json_artifact(str(opts.get("outdir", "") or "").strip(), "agent_eval_first.json", payload)
    if artifact:
        payload["artifact"] = artifact
    return payload


def agent_eval_main(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Build agent benchmark tables aligned with evaluation.txt.

    Options:
      agent_report_path -- preferred source: fuse_agent_eval paper report JSON
                           (default: out/agent_eval/main_9col/agentic_paper_report.json)
      jsonl_path        -- legacy fallback source: run-level JSONL
      conditions        -- comma list (default: base,bm25,fuse,both)
      outdir            -- write artifact directory (optional)
    """
    conditions, c_err = _normalize_conditions(opts)
    if c_err:
        return {"error": c_err}
    if conditions is None:
        return {"error": "no conditions selected"}

    if "agent_report_path" in opts:
        report_path_raw = str(opts.get("agent_report_path") or "").strip()
    else:
        report_path_raw = DEFAULT_AGENT_REPORT_PATH

    if report_path_raw:
        report_path = Path(report_path_raw).expanduser()
        if not report_path.exists():
            return {"error": f"agent_report_path not found: {report_path}"}
        try:
            report = _load_json_object(report_path)
        except Exception as e:
            return {"error": str(e)}

        tables = dict(report.get("tables") or {})
        outcomes = _select_condition_rows(tables.get("tab_agent_outcomes") or [], conditions)
        effort = _select_condition_rows(tables.get("tab_agent_effort") or [], conditions)
        if not outcomes or not effort:
            return {
                "error": (
                    f"agent_report_path missing tab_agent_outcomes/tab_agent_effort rows "
                    f"for requested conditions: {','.join(conditions)}"
                )
            }

        payload = {
            "experiment": "agent_eval_main",
            "agent_report_path": str(report_path),
            "conditions": conditions,
            "tables": {
                "tab_agent_outcomes": outcomes,
                "tab_agent_effort": effort,
            },
            "sources": {
                "report_type": report.get("report_type"),
                "scenario": report.get("scenario"),
                "task_count": report.get("task_count"),
                "run_count": report.get("run_count"),
            },
        }
        artifact = _write_json_artifact(str(opts.get("outdir", "") or "").strip(), "agent_eval_main.json", payload)
        if artifact:
            payload["artifact"] = artifact
        return payload

    return agent_eval_first(args, opts)


# ---------------------------------------------------------------------------
# §5.3 Per-component retrieval analysis
# ---------------------------------------------------------------------------

def component_analysis(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Per-component retrieval MRR/P@1/Hit@5 for §5.3 tab_per_component retrieval columns.

    Runs BM25 and FUSE by default (the two columns in tab_per_component).

    Options:
      comp_path   -- ground-truth JSON
      prompt_path -- prompt JSON
      methods     -- default: bm25_tool,fuse_tool
      outdir      -- write artifact directory (optional)
    """
    comp_path = str(opts.get("comp_path", DEFAULT_COMP_PATH) or DEFAULT_COMP_PATH).strip()
    prompt_path = str(opts.get("prompt_path", DEFAULT_PROMPT_PATH) or DEFAULT_PROMPT_PATH).strip()
    top_k_files = _as_int(opts.get("top_k_files"), DEFAULT_TOP_K_FILES, min_value=1)

    # Default to the two methods that populate the paper table.
    raw_methods = str(opts.get("methods", "") or "").strip()
    if not raw_methods:
        opts = dict(opts)
        opts["methods"] = "bm25_tool,fuse_tool"

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
    if not methods:
        return {"error": "no methods selected"}

    tasks = build_eval_tasks(gt, prompt_map)
    tasks = _apply_task_filters(
        tasks,
        components=_parse_csv_set(opts.get("components")),
        collections=_parse_csv_set(opts.get("collections")),
    )
    if not tasks:
        return {"error": "no evaluation tasks generated"}

    per_method: Dict[str, Dict[str, Any]] = {}
    for mid in methods:
        LOGGER.info("component_analysis: running method %s (%d tasks)", mid, len(tasks))
        per_method[mid] = _run_method(mid, tasks, opts)
        if per_method[mid].get("error"):
            return {
                "error": f"method '{mid}' failed: {per_method[mid].get('error')}",
                "partial": per_method,
            }

    tab_per_component = _per_component_from_per_method(per_method, top_k_files)

    # Sort by FUSE MRR descending for the paper table.
    fuse_key = next((m for m in methods if "fuse" in m), None)
    if fuse_key:
        tab_per_component.sort(
            key=lambda r: float((r.get(fuse_key) or {}).get("MRR") or 0.0),
            reverse=True,
        )

    payload = {
        "analysis": "component_analysis",
        "task_count": len(tasks),
        "methods": methods,
        "tables": {
            "tab_per_component_retrieval": tab_per_component,
        },
        "per_method": {mid: {"global_metrics": res.get("global_metrics")} for mid, res in per_method.items()},
    }
    artifact = _write_json_artifact(str(opts.get("outdir", "") or "").strip(), "component_analysis.json", payload)
    if artifact:
        payload["artifact"] = artifact
    return payload


# ---------------------------------------------------------------------------
# §5.4 Robustness retrieval evaluation
# ---------------------------------------------------------------------------

def eval_robustness(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    §5.4 retrieval robustness: run all prompt variants for selected components and
    compute pair-level stability metrics (mean median rank, mean worst rank,
    ≥80%-variants@5, ≥50%-variants@5).

    Options:
      prompt_variants_path -- JSON mapping component -> [variant_prompt, ...]  (required)
      comp_path            -- ground-truth JSON
      prompt_path          -- canonical prompt JSON (unused for ranking, used for GT lookup)
      methods              -- default: bm25_tool,func_emb_tool,fuse_tool
      stable_k             -- hit threshold (default: 5)
      outdir               -- write artifact directory (optional)
    """
    import statistics as _stats

    comp_path = str(opts.get("comp_path", DEFAULT_COMP_PATH) or DEFAULT_COMP_PATH).strip()
    prompt_path = str(opts.get("prompt_path", DEFAULT_PROMPT_PATH) or DEFAULT_PROMPT_PATH).strip()
    top_k_files = _as_int(opts.get("top_k_files"), DEFAULT_TOP_K_FILES, min_value=1)
    stable_k = _as_int(opts.get("stable_k"), 5, min_value=1)

    variants_path = str((opts.get("prompt_variants_path") or opts.get("variants_path") or "").strip())
    if not variants_path:
        return {"error": "provide prompt_variants_path (JSON: component -> [variant, ...])"}
    try:
        raw_variants = json.loads(Path(variants_path).read_text(encoding="utf-8"))
    except Exception as e:
        return {"error": f"failed to load prompt_variants_path '{variants_path}': {e}"}
    if not isinstance(raw_variants, dict):
        return {"error": "prompt_variants_path must be a JSON object"}
    variants_map: Dict[str, List[str]] = {}
    for comp, vals in raw_variants.items():
        if isinstance(vals, str):
            vals = [vals]
        if isinstance(vals, list):
            norm = [str(v).strip() for v in vals if isinstance(v, str) and str(v).strip()]
            if norm:
                variants_map[comp] = norm
    if not variants_map:
        return {"error": "no usable variants found in prompt_variants_path"}

    # Default methods for robustness table
    raw_methods = str(opts.get("methods", "") or "").strip()
    if not raw_methods:
        opts = dict(opts)
        opts["methods"] = "bm25_tool,func_emb_tool,fuse_tool"

    try:
        gt = create_ground_truth(comp_path)
    except Exception as e:
        return {"error": f"failed to load comp_path '{comp_path}': {e}"}
    try:
        load_prompt_map(prompt_path)  # validate file exists; not used for task prompts
    except Exception as e:
        return {"error": f"failed to load prompt_path '{prompt_path}': {e}"}

    methods, m_err = _normalize_methods(opts)
    if m_err:
        return {"error": m_err}
    if not methods:
        return {"error": "no methods selected"}

    # Build tasks — one per (cid, component, variant_index)
    tasks: List[Dict[str, Any]] = []
    for cid in sorted(gt.keys(), key=lambda c: str(api.get_colname_from_oid(c) or c)):
        colname = api.get_colname_from_oid(cid)
        for component, gold_oid in sorted(gt[cid].items()):
            variants = variants_map.get(component) or []
            for idx, variant_prompt in enumerate(variants):
                tasks.append(
                    {
                        "task_id": f"{cid}:{component}:v{idx}",
                        "pair_id": f"{cid}:{component}",
                        "cid": str(cid),
                        "collection": str(colname or cid),
                        "component": component,
                        "prompt": variant_prompt,
                        "gold_oid": str(gold_oid),
                    }
                )
    if not tasks:
        return {"error": "no variant tasks built — check prompt_variants_path components match ground truth"}

    per_method_out: Dict[str, Any] = {}
    for mid in methods:
        LOGGER.info("eval_robustness: running method %s (%d tasks)", mid, len(tasks))
        result = _run_method(mid, tasks, opts)
        if result.get("error"):
            per_method_out[mid] = result
            continue

        pq = result.get("per_query") or []
        pair_ranks: Dict[str, List[int]] = defaultdict(list)
        for q in pq:
            if not isinstance(q, dict):
                continue
            pair_id = str(q.get("pair_id") or q.get("task_id", "").rsplit(":v", 1)[0])
            try:
                rank = int(q.get("rank", top_k_files + 1))
            except Exception:
                rank = top_k_files + 1
            if pair_id:
                pair_ranks[pair_id].append(rank)

        pair_count = len(pair_ranks)
        pair_hit_rates: List[float] = []
        pair_medians: List[float] = []
        pair_worsts: List[float] = []
        # Per-component stats: component -> all raw ranks and per-collection worsts
        comp_all_ranks: Dict[str, List[int]] = defaultdict(list)
        comp_medians: Dict[str, List[float]] = defaultdict(list)
        comp_worsts: Dict[str, List[float]] = defaultdict(list)
        for pid, rs in pair_ranks.items():
            if not rs:
                continue
            pair_hit_rates.append(float(sum(1 for r in rs if r <= stable_k) / len(rs)))
            pair_medians.append(float(_stats.median(rs)))
            pair_worsts.append(float(max(rs)))
            # Extract component name: pair_id is "{cid}:{component}"
            comp = pid.split(":", 1)[1] if ":" in pid else pid
            comp_all_ranks[comp].extend(rs)
            comp_medians[comp].append(float(_stats.median(rs)))
            comp_worsts[comp].append(float(max(rs)))

        ge80 = sum(1 for x in pair_hit_rates if x >= 0.80)
        ge50 = sum(1 for x in pair_hit_rates if x >= 0.50)
        mean_median = float(sum(pair_medians) / max(len(pair_medians), 1))
        mean_worst = float(sum(pair_worsts) / max(len(pair_worsts), 1))

        def _quartiles(vals: List[float]) -> Dict[str, float]:
            if not vals:
                return {"q1": 0.0, "median": 0.0, "q3": 0.0, "worst": 0.0}
            s = sorted(vals)
            n = len(s)
            q1_idx = (n - 1) * 0.25
            q3_idx = (n - 1) * 0.75
            lo, hi = int(q1_idx), min(int(q1_idx) + 1, n - 1)
            q1 = s[lo] + (q1_idx - lo) * (s[hi] - s[lo])
            lo, hi = int(q3_idx), min(int(q3_idx) + 1, n - 1)
            q3 = s[lo] + (q3_idx - lo) * (s[hi] - s[lo])
            mid_idx = (n - 1) * 0.5
            lo, hi = int(mid_idx), min(int(mid_idx) + 1, n - 1)
            med = s[lo] + (mid_idx - lo) * (s[hi] - s[lo])
            return {"q1": round(q1, 2), "median": round(med, 2), "q3": round(q3, 2), "worst": round(max(s), 2)}

        per_component_stats = {
            comp: {
                "mean_median_rank": round(sum(comp_medians[comp]) / len(comp_medians[comp]), 3),
                "mean_worst_rank": round(sum(comp_worsts[comp]) / len(comp_worsts[comp]), 3),
                "rank_distribution": _quartiles([float(r) for r in comp_all_ranks[comp]]),
                "ranks": sorted(comp_all_ranks[comp]),
            }
            for comp in sorted(comp_medians)
        }

        per_method_out[mid] = {
            "global_metrics": result.get("global_metrics"),
            "pair_level": {
                "stable_k": stable_k,
                "pairs": pair_count,
                f"ge_80pct_variants_at_{stable_k}": (ge80 / pair_count) if pair_count else 0.0,
                f"ge_50pct_variants_at_{stable_k}": (ge50 / pair_count) if pair_count else 0.0,
                "mean_median_rank_per_pair": round(mean_median, 6),
                "mean_worst_rank_per_pair": round(mean_worst, 6),
            },
            "per_component": per_component_stats,
        }

    # Build tab_robustness_retrieval in paper order: BM25, Func-Emb, FUSE
    paper_order = ["bm25_tool", "func_emb_tool", "dense_tool", "fuse_tool"]
    tab_robustness: List[Dict[str, Any]] = []
    for mid in [m for m in paper_order if m in per_method_out]:
        pl = (per_method_out[mid] or {}).get("pair_level") or {}
        tab_robustness.append(
            {
                "method": METHOD_DISPLAY.get(mid, mid),
                f"ge_80pct_variants@{stable_k}": pl.get(f"ge_80pct_variants_at_{stable_k}"),
                f"ge_50pct_variants@{stable_k}": pl.get(f"ge_50pct_variants_at_{stable_k}"),
                "mean_median_rank_per_pair": pl.get("mean_median_rank_per_pair"),
                "mean_worst_rank_per_pair": pl.get("mean_worst_rank_per_pair"),
            }
        )

    # Build tab_robustness_per_component: rows are components, columns are BM25/FUSE median+worst
    bm25_pc = (per_method_out.get("bm25_tool") or {}).get("per_component") or {}
    fuse_pc = (per_method_out.get("fuse_tool") or {}).get("per_component") or {}
    all_comps = sorted(set(bm25_pc) | set(fuse_pc))
    tab_robustness_per_component: List[Dict[str, Any]] = []
    for comp in all_comps:
        b = bm25_pc.get(comp) or {}
        f = fuse_pc.get(comp) or {}
        tab_robustness_per_component.append({
            "component": comp,
            "bm25_median_rank": b.get("mean_median_rank"),
            "bm25_worst_rank": b.get("mean_worst_rank"),
            "fuse_median_rank": f.get("mean_median_rank"),
            "fuse_worst_rank": f.get("mean_worst_rank"),
        })

    payload = {
        "experiment": "eval_robustness",
        "prompt_variants_path": variants_path,
        "stable_k": stable_k,
        "task_count": len(tasks),
        "methods": methods,
        "tables": {
            "tab_robustness_retrieval": tab_robustness,
            "tab_robustness_per_component": tab_robustness_per_component,
        },
        "per_method": per_method_out,
    }
    artifact = _write_json_artifact(str(opts.get("outdir", "") or "").strip(), "eval_robustness.json", payload)
    if artifact:
        payload["artifact"] = artifact
    return payload


# ---------------------------------------------------------------------------
# Paper report bundle
# ---------------------------------------------------------------------------

def eval_paper_report(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Produce all evaluation tables needed by the current evaluation.tex structure:

      §5.1  tab_e1_main, tab_ablation_packing
      §5.2  tab_agent_summary, tab_first_call_gold_rank, tab_rank_bucket_success
      §5.3  tab_per_component_retrieval (from tool_eval_main with bm25+fuse)
            tab_per_component_agent     (from agentic_paper_report.json)
      §5.4  tab_robustness_retrieval    (from eval_robustness if variants path given)

    Options:
      outdir               -- write directory (default: out/fuse)
      agent_report_path    -- agentic_paper_report.json path
      prompt_variants_path -- variant JSON for §5.4 robustness (optional; skipped if absent)
      skip_retrieval       -- if true, skip tool_eval_main (use cached tables) (default: false)
    """
    outdir = str(opts.get("outdir", DEFAULT_OUTDIR) or DEFAULT_OUTDIR).strip()
    tables: Dict[str, Any] = {}

    # --- §5.1 + §5.3 retrieval ---
    if not _as_bool(opts.get("skip_retrieval"), False):
        # Run all four methods so we get both main table and ablation table in one pass.
        retrieval_opts = dict(opts)
        retrieval_opts.setdefault("methods", "bm25_tool,dense_tool,func_emb_tool,fuse_tool")
        LOGGER.info("eval_paper_report: running tool_eval_main (all four methods)")
        tool_out = tool_eval_main(args, retrieval_opts)
        if tool_out.get("error"):
            return {"error": f"tool_eval_main failed: {tool_out.get('error')}"}
        t = tool_out.get("tables") or {}
        tables["tab_e1_main"] = t.get("tab_e1_main")
        tables["tab_ablation_packing"] = t.get("tab_ablation_packing")
        tables["tab_per_component_retrieval"] = t.get("tab_per_component_retrieval")
    else:
        LOGGER.info("eval_paper_report: skip_retrieval=true — omitting §5.1/§5.3 retrieval tables")

    # --- §5.2 + §5.3 agent tables from agentic_paper_report.json ---
    agent_opts = dict(opts)
    agent_out = agent_eval_main(args, agent_opts)
    if agent_out.get("error"):
        return {"error": f"agent_eval_main failed: {agent_out.get('error')}"}
    agent_report_tables = (agent_out.get("tables") or {})
    tables["tab_agent_outcomes"] = agent_report_tables.get("tab_agent_outcomes")
    tables["tab_agent_effort"] = agent_report_tables.get("tab_agent_effort")

    # Pull the richer tables directly from the raw report JSON (agent_eval_main only
    # surfaces outcomes + effort via its current interface).
    agent_report_path = str(
        opts.get("agent_report_path", DEFAULT_AGENT_REPORT_PATH) or DEFAULT_AGENT_REPORT_PATH
    ).strip()
    try:
        raw_report = _load_json_object(Path(agent_report_path).expanduser())
        raw_tables = raw_report.get("tables") or {}
        tables["tab_first_call_gold_rank"] = raw_tables.get("tab_first_call_gold_rank")
        tables["tab_rank_bucket_success"] = raw_tables.get("tab_rank_bucket_success")
        tables["tab_per_component_agent"] = raw_tables.get("tab_per_component_agent")
    except Exception as e:
        LOGGER.warning("eval_paper_report: could not load agent report for extra tables: %s", e)

    # --- §5.4 retrieval robustness (optional) ---
    variants_path = str((opts.get("prompt_variants_path") or opts.get("variants_path") or "").strip())
    if variants_path:
        LOGGER.info("eval_paper_report: running eval_robustness for §5.4")
        rob_opts = dict(opts)
        rob_out = eval_robustness(args, rob_opts)
        if rob_out.get("error"):
            LOGGER.warning("eval_paper_report: eval_robustness failed: %s", rob_out.get("error"))
        else:
            tables["tab_robustness_retrieval"] = (rob_out.get("tables") or {}).get("tab_robustness_retrieval")
    else:
        LOGGER.info("eval_paper_report: no prompt_variants_path — skipping §5.4 robustness retrieval")

    report = {
        "report_type": "eval_paper_report",
        "tables": tables,
        "sources": {
            "agent_report_path": agent_report_path,
        },
    }

    artifact = _write_json_artifact(outdir, "eval_paper_report.json", report)
    if artifact:
        report["artifact"] = artifact
    return report


def plot_robustness(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Generate a box plot figure showing per-component rank distributions for FUSE vs BM25
    across all query variants, for inclusion in §5.4 of the paper.

    Options:
      robustness_path -- path to eval_robustness.json (default: out/fuse/robustness/eval_robustness.json)
      outdir          -- directory to write figure files (default: out/fuse/robustness)
      fmt             -- comma-separated output formats, e.g. "pdf,png" (default: "pdf,png")
    """
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from matplotlib.lines import Line2D
    except ImportError:
        return {"error": "matplotlib is required: pip install matplotlib"}

    import statistics as _stats

    rob_path = str(opts.get("robustness_path") or "out/fuse/robustness/eval_robustness.json").strip()
    outdir = str(opts.get("outdir") or "out/fuse/robustness").strip()
    formats = [f.strip() for f in str(opts.get("fmt") or "pdf,png").split(",") if f.strip()]

    try:
        data = _load_json_object(Path(rob_path))
    except Exception as e:
        return {"error": f"failed to load robustness_path '{rob_path}': {e}"}

    pm = data.get("per_method") or {}
    fuse_pc = (pm.get("fuse_tool") or {}).get("per_component") or {}
    bm25_pc = (pm.get("bm25_tool") or {}).get("per_component") or {}
    if not fuse_pc or not bm25_pc:
        return {"error": "per_component rank data missing — re-run eval_robustness first"}

    # Component display order: ascending FUSE difficulty (matches §5.3 sort order)
    component_order = ["dnsmasq", "px5g-mbedtls", "usign", "dropbear", "mtd"]
    component_labels = ["dnsmasq", "px5g-\nmbedtls", "usign", "dropbear", "mtd"]
    missing = [c for c in component_order if c not in fuse_pc or c not in bm25_pc]
    if missing:
        return {"error": f"components missing from data: {missing}"}

    fuse_color = "#2A9D8F"
    bm25_color = "#4C78A8"

    n = len(component_order)
    group_width = 0.7
    gap = 0.35
    box_w = group_width / 2

    positions_fuse = [i * (group_width + gap) - box_w / 2 for i in range(n)]
    positions_bm25 = [i * (group_width + gap) + box_w / 2 for i in range(n)]
    fuse_data = [fuse_pc[comp]["ranks"] for comp in component_order]
    bm25_data = [bm25_pc[comp]["ranks"] for comp in component_order]

    from matplotlib.patches import Patch as _Patch

    def _draw_boxes(ax: Any, data: List, positions: List, color: str) -> None:
        bp = ax.boxplot(
            data,
            positions=positions,
            widths=box_w * 0.75,
            patch_artist=True,
            showfliers=True,
            flierprops=dict(marker="o", markersize=3, alpha=0.35,
                            markeredgewidth=0, markerfacecolor=color,
                            markeredgecolor="none"),
            medianprops=dict(color="white", linewidth=1.5),
            whiskerprops=dict(color=color, linewidth=0.9, alpha=0.7),
            capprops=dict(color=color, linewidth=0.9, alpha=0.7),
            boxprops=dict(edgecolor=color, linewidth=0.9),
        )
        for patch in bp["boxes"]:
            patch.set_facecolor(color)
            patch.set_alpha(0.85)

    with plt.rc_context(_FIGURE_RC):
        fig, ax = plt.subplots(figsize=(7, 3.6))

        _draw_boxes(ax, fuse_data, positions_fuse, fuse_color)
        _draw_boxes(ax, bm25_data, positions_bm25, bm25_color)

        ax.axhline(y=5, color="gray", linestyle="--", linewidth=0.9, alpha=0.7, zorder=0)
        ax.text(
            positions_bm25[-1] + box_w, 5.3, "top-5",
            color="gray", fontsize=7, va="bottom", ha="right",
        )

        group_centers = [i * (group_width + gap) for i in range(n)]
        ax.set_xticks(group_centers)
        ax.set_xticklabels(component_labels)
        ax.set_ylabel("Rank (lower is better)")
        ax.set_ylim(0, 50)
        ax.set_yticks([1, 5, 10, 20, 30, 40, 50])
        ax.yaxis.grid(True, color="#d8d8d8", linewidth=0.6, alpha=0.7, linestyle=":")
        ax.set_axisbelow(True)
        ax.set_xlim(positions_fuse[0] - box_w, positions_bm25[-1] + box_w)
        ax.legend(
            handles=[
                _Patch(facecolor=fuse_color, edgecolor=fuse_color, alpha=0.85, label="FUSE"),
                _Patch(facecolor=bm25_color, edgecolor=bm25_color, alpha=0.85, label="BM25"),
            ],
            fontsize=7, loc="upper left", framealpha=0.9,
        )
        ax.spines["top"].set_visible(False)
        ax.spines["right"].set_visible(False)
        fig.tight_layout()

        Path(outdir).mkdir(parents=True, exist_ok=True)
        saved = []
        for fmt in formats:
            out_path = str(Path(outdir) / f"robustness_boxplot.{fmt}")
            fig.savefig(out_path, dpi=200, bbox_inches="tight")
            saved.append(out_path)
            LOGGER.info("plot_robustness: saved %s", out_path)
        plt.close(fig)

    return {"saved": saved}


def plot_robustness_cost(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Generate boxplot figures showing per-component token usage and tool call
    distributions for FUSE vs BM25 across robustness query variants.

    Options:
      runs_jsonl -- path to agentic runs JSONL
                   (default: out/agent_eval/robustness_agent/agentic_runs_topk10.jsonl)
      outdir     -- directory to write figure files (default: out/fuse/robustness)
      fmt        -- comma-separated output formats, e.g. "pdf,png" (default: "pdf,png")
    """
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from matplotlib.lines import Line2D
    except ImportError:
        return {"error": "matplotlib is required: pip install matplotlib"}

    import statistics as _stats

    default_jsonl = "out/agent_eval/robustness_agent/agentic_runs_topk10.jsonl"
    runs_jsonl = str(opts.get("runs_jsonl") or default_jsonl).strip()
    outdir = str(opts.get("outdir") or "out/fuse/robustness").strip()
    formats = [f.strip() for f in str(opts.get("fmt") or "pdf,png").split(",") if f.strip()]

    component_order = ["dnsmasq", "px5g-mbedtls", "usign", "dropbear", "mtd"]
    component_labels = ["dnsmasq", "px5g-\nmbedtls", "usign", "dropbear", "mtd"]
    conditions = ["fuse", "bm25"]

    per: Dict[str, Dict[str, Dict[str, List]]] = {
        c: {comp: {"tokens": [], "tool_calls": []} for comp in component_order}
        for c in conditions
    }

    try:
        with open(runs_jsonl, encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                run = json.loads(line)
                cond = str(run.get("condition", "")).strip().lower()
                comp = str(run.get("component", "")).strip()
                if cond not in conditions or comp not in component_order:
                    continue
                per[cond][comp]["tokens"].append(run.get("total_tokens") or 0)
                per[cond][comp]["tool_calls"].append(run.get("total_tool_calls") or 0)
    except Exception as e:
        return {"error": f"failed to load runs_jsonl '{runs_jsonl}': {e}"}

    fuse_color = "#2A9D8F"
    bm25_color = "#4C78A8"

    n = len(component_order)
    group_width = 0.7
    gap = 0.35
    box_w = group_width / 2
    TOKEN_FLOOR = 1e3  # clip zero-token runs for log display

    from matplotlib.patches import Patch as _Patch

    positions_fuse = [i * (group_width + gap) - box_w / 2 for i in range(n)]
    positions_bm25 = [i * (group_width + gap) + box_w / 2 for i in range(n)]

    Path(outdir).mkdir(parents=True, exist_ok=True)
    saved = []

    def _make_plot(metric: str, ylabel: str, logscale: bool, filename: str,
                   floor: float = 0.0) -> None:
        fuse_vals = [
            [max(v, floor) if floor > 0 else v for v in per["fuse"][comp][metric]]
            for comp in component_order
        ]
        bm25_vals = [
            [max(v, floor) if floor > 0 else v for v in per["bm25"][comp][metric]]
            for comp in component_order
        ]

        with plt.rc_context(_FIGURE_RC):
            fig, ax = plt.subplots(figsize=(7, 3.6))

            def _draw(data: List, positions: List, color: str) -> None:
                bp = ax.boxplot(
                    data,
                    positions=positions,
                    widths=box_w * 0.75,
                    patch_artist=True,
                    showfliers=True,
                    flierprops=dict(marker="o", markersize=3, alpha=0.35,
                                    markeredgewidth=0, markerfacecolor=color,
                                    markeredgecolor="none"),
                    medianprops=dict(color="white", linewidth=1.5),
                    whiskerprops=dict(color=color, linewidth=0.9, alpha=0.7),
                    capprops=dict(color=color, linewidth=0.9, alpha=0.7),
                    boxprops=dict(edgecolor=color, linewidth=0.9),
                )
                for patch in bp["boxes"]:
                    patch.set_facecolor(color)
                    patch.set_alpha(0.85)

            _draw(fuse_vals, positions_fuse, fuse_color)
            _draw(bm25_vals, positions_bm25, bm25_color)

            group_centers = [i * (group_width + gap) for i in range(n)]
            ax.set_xticks(group_centers)
            ax.set_xticklabels(component_labels)
            ax.set_ylabel(ylabel)
            ax.set_xlim(positions_fuse[0] - box_w, positions_bm25[-1] + box_w)
            if logscale:
                ax.set_yscale("log")
            ax.yaxis.grid(True, color="#d8d8d8", linewidth=0.6, alpha=0.7, linestyle=":")
            ax.set_axisbelow(True)
            ax.legend(
                handles=[
                    _Patch(facecolor=fuse_color, edgecolor=fuse_color, alpha=0.85, label="FUSE"),
                    _Patch(facecolor=bm25_color, edgecolor=bm25_color, alpha=0.85, label="BM25"),
                ],
                fontsize=7, loc="upper left", framealpha=0.9,
            )
            ax.spines["top"].set_visible(False)
            ax.spines["right"].set_visible(False)
            fig.tight_layout()

            for fmt in formats:
                out_path = str(Path(outdir) / f"{filename}.{fmt}")
                fig.savefig(out_path, dpi=200, bbox_inches="tight")
                saved.append(out_path)
                LOGGER.info("plot_robustness_cost: saved %s", out_path)
            plt.close(fig)

    _make_plot("tokens", "Total tokens (log scale)", logscale=True,
               filename="robustness_tokens", floor=TOKEN_FLOOR)
    _make_plot("tool_calls", "Total tool calls", logscale=False,
               filename="robustness_tool_calls")

    return {"saved": saved}


exports = [
    tool_eval_main,
    component_analysis,
    eval_robustness,
    agent_eval_first,
    agent_eval_main,
    eval_paper_report,
    plot_robustness,
    plot_robustness_cost,
]
