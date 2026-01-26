DESC = "Semantic search over decompiled functions using local embeddings (MiniLM)."
NAME = "query_function"

import logging
import re
from typing import Any, Dict, List, Tuple, Optional

import numpy as np
from sentence_transformers import SentenceTransformer

from oxide.core import api

logger = logging.getLogger(NAME)

# -----------------------------------------------------------------------------
# Options (Oxide schema format)
# -----------------------------------------------------------------------------
opts_doc = {
    "query": {"type": str, "mangle": True, "default": ""},
    "query_path": {"type": str, "mangle": True, "default": ""},

    # list-length only; do not fork caching
    "top_k": {"type": int, "mangle": False, "default": 10},

    # affects indexed text (truncation) => must fork caching
    "max_chars": {"type": int, "mangle": True, "default": 20000},

    # perf knobs; should not fork caching
    "batch_size": {"type": int, "mangle": False, "default": 64},
    "use_cache": {"type": bool, "mangle": False, "default": True},
    "rebuild": {"type": bool, "mangle": False, "default": False},

    # embedding space changes => must fork caching
    "model_id": {"type": str, "mangle": True, "default": "sentence-transformers/all-MiniLM-L6-v2"},
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
    try:
        oids = api.expand_oids(oid_list)
    except Exception:
        oids = oid_list

    query = _load_query(opts)
    if not query:
        return {"error": "Please provide a query via 'query' or 'query_path'."}

    top_k = int(opts.get("top_k", 10) or 10)
    max_chars = int(opts.get("max_chars", 20000) or 20000)
    batch_size = int(opts.get("batch_size", 64) or 64)
    model_id = (opts.get("model_id") or "sentence-transformers/all-MiniLM-L6-v2").strip()

    use_cache = bool(opts.get("use_cache", True))
    rebuild = bool(opts.get("rebuild", False))

    model = _get_model(model_id)
    qvec = model.encode(query, normalize_embeddings=True).astype(np.float32)

    counts: Dict[str, Dict[str, Any]] = {}
    global_candidates: List[Dict[str, Any]] = []

    for oid in oids:
        idx = _load_or_build_index(
            oid=oid,
            model_id=model_id,
            max_chars=max_chars,
            batch_size=batch_size,
            use_cache=use_cache,
            rebuild=rebuild,
            model=model,
            counts=counts,
        )
        if not idx:
            continue

        emb = idx["emb"]
        if emb.size == 0:
            continue

        sims = emb.dot(qvec)

        k_local = top_k if top_k > 0 else sims.shape[0]
        k_local = min(k_local, sims.shape[0])
        if k_local <= 0:
            continue

        loc = np.argpartition(-sims, k_local - 1)[:k_local]
        loc = loc[np.argsort(-sims[loc])]

        addrs = idx["addrs"]
        names = idx["names"]
        previews = idx["previews"]

        for i in loc:
            global_candidates.append({
                "oid": oid,
                "function_addr": addrs[i],
                "function_name": names[i],
                "score": float(sims[i]),
                "preview": previews[i],
            })

    if not global_candidates:
        return {
            "query": query,
            "counts": counts,
            "results": {"best_match": None, "candidates": []},
            "warning": "No indexed functions available (no decomp output or no functions found).",
        }

    global_candidates.sort(key=lambda x: x["score"], reverse=True)
    if top_k > 0:
        global_candidates = global_candidates[:top_k]

    return {
        "query": query,
        "counts": counts,
        "results": {"best_match": global_candidates[0], "candidates": global_candidates},
        "notes": {
            "model_id": model_id,
            "similarity": "cosine (normalized dot product)",
        },
    }

# -----------------------------------------------------------------------------
# Index build + cache
# -----------------------------------------------------------------------------
def _load_or_build_index(
    *,
    oid: str,
    model_id: str,
    max_chars: int,
    batch_size: int,
    use_cache: bool,
    rebuild: bool,
    model: SentenceTransformer,
    counts: Dict[str, Dict[str, Any]],
) -> Optional[Dict[str, Any]]:
    key = _cache_key(oid, model_id, max_chars)

    if use_cache and (not rebuild) and api.local_exists(NAME, key):
        try:
            blob = api.local_retrieve(NAME, key) or {}
            idx = blob.get(oid)
            if idx:
                counts[oid] = {
                    "cache": "hit",
                    "num_functions": idx.get("num_functions", 0),
                    "num_indexed": idx.get("num_indexed", 0),
                }
                return idx
        except Exception:
            logger.exception("Failed to load cached index for oid=%s", oid)

    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    f_list = list(_iter_functions(funcs))
    num_functions = len(f_list)

    addrs: List[str] = []
    names: List[str] = []
    texts: List[str] = []
    previews: List[str] = []

    num_indexed = 0

    for addr, finfo in f_list:
        decomp = _safe_decompile(oid, addr)
        text = _normalize_decomp_blob(decomp, max_chars=max_chars)
        if not text:
            continue

        addrs.append(str(addr))
        names.append(_extract_func_name(finfo, addr))
        previews.append(_first_preview_line(text))
        texts.append(text)
        num_indexed += 1

    counts[oid] = {"cache": "miss", "num_functions": num_functions, "num_indexed": num_indexed}

    if not texts:
        return None

    emb = model.encode(
        texts,
        batch_size=max(1, batch_size),
        normalize_embeddings=True,
        show_progress_bar=False,
    ).astype(np.float32)

    idx = {
        "num_functions": num_functions,
        "num_indexed": num_indexed,
        "addrs": addrs,
        "names": names,
        "previews": previews,
        "emb": emb,
    }

    if use_cache:
        try:
            api.local_store(NAME, key, {oid: idx})
        except Exception:
            logger.exception("Failed to cache index for oid=%s", oid)

    return idx

def _cache_key(oid: str, model_id: str, max_chars: int) -> str:
    safe = re.sub(r"[^A-Za-z0-9_.-]+", "_", f"{oid}_{model_id}_{max_chars}")
    return safe

def _iter_functions(funcs: Any):
    if isinstance(funcs, dict):
        for addr, finfo in funcs.items():
            yield addr, finfo
    elif isinstance(funcs, (list, tuple)):
        for addr in funcs:
            yield addr, None

def _safe_decompile(oid: str, addr: Any) -> Any:
    try:
        res = api.retrieve("function_decomp", [oid], {"function_addr": str(addr)})
        return res.get(oid, res) if isinstance(res, dict) else res
    except Exception:
        logger.debug("Decompile failed oid=%s addr=%s", oid, addr, exc_info=True)
        return None

def _extract_func_name(finfo: Any, addr: Any) -> str:
    if isinstance(finfo, dict):
        for k in ("name", "function_name", "symbol", "label"):
            v = finfo.get(k)
            if isinstance(v, str) and v.strip():
                return v.strip()
    if isinstance(finfo, str) and finfo.strip():
        return finfo.strip()
    return f"sub_{str(addr)}"

def _first_preview_line(text: str) -> str:
    for line in text.splitlines():
        s = line.strip()
        if s:
            return s[:200]
    return ""

def _load_query(opts: dict) -> str:
    q = (opts.get("query") or "").strip()
    qp = (opts.get("query_path") or "").strip()
    if (not q) and qp:
        try:
            with open(qp, "r", encoding="utf-8", errors="replace") as f:
                q = f.read().strip()
        except OSError:
            return ""
    return q

def _normalize_decomp_blob(f_decomp: Any, max_chars: int) -> str:
    if not f_decomp:
        return ""
    if isinstance(f_decomp, list):
        s = "\n".join([x for x in f_decomp if isinstance(x, str)]).strip()
    elif isinstance(f_decomp, str):
        s = f_decomp.strip()
    else:
        s = str(f_decomp).strip()
    return s[:max_chars] if (max_chars and len(s) > max_chars) else s

_MODEL: Optional[SentenceTransformer] = None
_MODEL_ID: Optional[str] = None

def _get_model(model_id: str) -> SentenceTransformer:
    global _MODEL, _MODEL_ID
    if _MODEL is None or _MODEL_ID != model_id:
        _MODEL = SentenceTransformer(model_id)
        _MODEL_ID = model_id
    return _MODEL
