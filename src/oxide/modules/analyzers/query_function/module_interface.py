DESC = "Semantic search over decompiled functions using local embeddings (MiniLM)."
NAME = "query_function"

import logging
import re
import time
from typing import Any, Dict, List, Optional, Tuple

import numpy as np

from oxide.core import api

logger = logging.getLogger(NAME)

# -----------------------------------------------------------------------------
# Options
# -----------------------------------------------------------------------------
opts_doc = {
    "query": {"type": str, "mangle": True, "default": ""},
    "query_path": {"type": str, "mangle": True, "default": ""},
    "top_k": {"type": int, "mangle": False, "default": 10},
    # affects indexed text, must fork caching
    "max_chars": {"type": int, "mangle": True, "default": 20000},
    # perf knobs, do not fork caching
    "batch_size": {"type": int, "mangle": False, "default": 64},
    "use_cache": {"type": bool, "mangle": False, "default": True},
    "rebuild": {"type": bool, "mangle": False, "default": False},
    # embedding space changes, must fork caching
    "model_id": {
        "type": str,
        "mangle": True,
        "default": "sentence-transformers/all-MiniLM-L6-v2",
    },
    # timing + live progress, do not fork caching
    "timing": {"type": bool, "mangle": False, "default": True},
    "timing_topn": {"type": int, "mangle": False, "default": 5},
    "progress": {"type": bool, "mangle": False, "default": True},
    "progress_every": {"type": int, "mangle": False, "default": 50},
    # optional: file-level embedding aggregation
    "return_file_embeddings": {"type": bool, "mangle": False, "default": False},
    "file_agg": {"type": str, "mangle": False, "default": "attn"},
    "attn_tau": {"type": float, "mangle": False, "default": 0.07},
}


def documentation() -> Dict[str, Any]:
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }


# -----------------------------------------------------------------------------
# Main
# -----------------------------------------------------------------------------
def results(oid_list: List[str], opts: dict) -> Dict[str, Any]:
    t_total0 = time.perf_counter()

    timing = _as_bool(opts.get("timing", True))
    topn = _as_int(opts.get("timing_topn", 5), 5)

    progress = _as_bool(opts.get("progress", True))
    progress_every = _as_int(opts.get("progress_every", 50), 50)

    oids = _expand_oids_best_effort(oid_list)

    query = _load_query(opts)
    if not query:
        return {"error": "Please provide a query via 'query' or 'query_path'."}

    top_k = _as_int(opts.get("top_k", 10), 10)
    max_chars = _as_int(opts.get("max_chars", 20000), 20000)
    batch_size = _as_int(opts.get("batch_size", 64), 64)
    use_cache = _as_bool(opts.get("use_cache", True))
    rebuild = _as_bool(opts.get("rebuild", False))
    model_id = (
        opts.get("model_id") or "sentence-transformers/all-MiniLM-L6-v2"
    ).strip()
    return_file_embeddings = _as_bool(opts.get("return_file_embeddings", False))
    file_agg = (opts.get("file_agg") or "attn").strip().lower()
    if file_agg not in ("top1", "mean", "attn"):
        file_agg = "attn"
    attn_tau = _as_float(opts.get("attn_tau", 0.07), 0.07)
    if attn_tau <= 0:
        attn_tau = 0.07

    t0 = time.perf_counter()
    model = _get_model(model_id)
    t_model = time.perf_counter() - t0

    t0 = time.perf_counter()
    q_text = _truncate_text_for_model(query, model)
    qvec = model.encode(q_text, normalize_embeddings=True).astype(np.float32)
    t_qemb = time.perf_counter() - t0

    if timing and progress:
        logger.info(
            "query_function start oids=%d model_load_s=%.3f query_embed_s=%.3f model_id=%s",
            len(oids),
            t_model,
            t_qemb,
            model_id,
        )

    counts: Dict[str, Dict[str, Any]] = {}
    candidates: List[Dict[str, Any]] = []
    oid_times: List[Dict[str, Any]] = []
    file_embeddings: Dict[str, List[float]] = {}
    file_scores: Dict[str, float] = {}

    for idx_oid, oid in enumerate(oids, start=1):
        t_oid0 = time.perf_counter()

        if timing and progress:
            logger.info("oid %d/%d start oid=%s", idx_oid, len(oids), oid)

        idx, tinfo = _load_or_build_index(
            oid=oid,
            model_id=model_id,
            max_chars=max_chars,
            batch_size=batch_size,
            use_cache=use_cache,
            rebuild=rebuild,
            model=model,
            counts=counts,
            timing=timing,
            progress=progress,
            progress_every=progress_every,
        )

        t_search0 = time.perf_counter()
        if idx and idx.get("emb") is not None and idx["emb"].size > 0:
            loc, loc_sims = _topk_indices_and_sims(idx["emb"], qvec, top_k)
            _append_topk_candidates(
                candidates=candidates,
                oid=oid,
                idx=idx,
                qvec=qvec,
                top_k=top_k,
                loc=loc,
                loc_sims=loc_sims,
            )
            if return_file_embeddings:
                file_emb = _aggregate_file_embedding(
                    idx["emb"], loc, loc_sims, file_agg, attn_tau
                )
                if file_emb is not None:
                    file_embeddings[oid] = file_emb.astype(np.float32).tolist()
                    file_scores[oid] = float(file_emb.dot(qvec))
        t_search = time.perf_counter() - t_search0

        t_oid_total = time.perf_counter() - t_oid0

        if timing:
            entry = {
                "oid": oid,
                "total_s": t_oid_total,
                "search_s": t_search,
            }
            if tinfo:
                entry.update(tinfo)
            oid_times.append(entry)

        if timing and progress:
            cache_state = (tinfo or {}).get("cache_hit")
            logger.info(
                "oid %d/%d done oid=%s total_s=%.3f search_s=%.3f cache_hit=%s indexed=%s",
                idx_oid,
                len(oids),
                oid,
                t_oid_total,
                t_search,
                cache_state,
                (counts.get(oid) or {}).get("num_indexed"),
            )

    if not candidates:
        out = {
            "query": query,
            "counts": counts,
            "results": {"best_match": None, "candidates": []},
            "warning": "No indexed functions available (no decomp output or no functions found).",
        }
        if return_file_embeddings:
            out["file_embeddings"] = file_embeddings
            out["file_scores"] = file_scores
            out["notes"] = {
                "file_agg": file_agg,
                "attn_tau": attn_tau,
                "file_top_k": top_k,
            }
        if timing:
            out["timing"] = _timing_summary(
                total_s=time.perf_counter() - t_total0,
                model_load_s=t_model,
                query_embed_s=t_qemb,
                oid_times=oid_times,
                topn=topn,
            )
        return out

    candidates.sort(key=lambda x: x["score"], reverse=True)
    if top_k > 0:
        candidates = candidates[:top_k]

    out = {
        "query": query,
        "counts": counts,
        "results": {"best_match": candidates[0], "candidates": candidates},
        "notes": {
            "model_id": model_id,
            "similarity": "cosine (normalized dot product)",
            "file_agg": file_agg,
            "attn_tau": attn_tau,
            "file_top_k": top_k,
        },
    }
    if return_file_embeddings:
        out["file_embeddings"] = file_embeddings
        out["file_scores"] = file_scores

    if timing:
        out["timing"] = _timing_summary(
            total_s=time.perf_counter() - t_total0,
            model_load_s=t_model,
            query_embed_s=t_qemb,
            oid_times=oid_times,
            topn=topn,
        )
        if progress:
            logger.info(
                "query_function done total_s=%.3f oids=%d candidates=%d",
                out["timing"]["total_s"],
                len(oids),
                len(candidates),
            )

    return out


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
    model: "SentenceTransformer",
    counts: Dict[str, Dict[str, Any]],
    timing: bool,
    progress: bool,
    progress_every: int,
) -> Tuple[Optional[Dict[str, Any]], Optional[Dict[str, Any]]]:
    t0 = time.perf_counter()
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
                if timing and progress:
                    logger.info(
                        "oid=%s cache hit num_functions=%d num_indexed=%d",
                        oid,
                        counts[oid]["num_functions"],
                        counts[oid]["num_indexed"],
                    )
                return idx, _tinfo(
                    timing,
                    cache_hit=True,
                    list_funcs_s=0.0,
                    decomp_s=0.0,
                    embed_s=0.0,
                    store_s=0.0,
                    num_decomp_calls=0,
                    build_total_s=time.perf_counter() - t0,
                )
        except Exception:
            logger.exception("Failed to load cached index for oid=%s", oid)

    # list functions
    t_list0 = time.perf_counter()
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    f_list = list(_iter_functions(funcs))
    t_list = time.perf_counter() - t_list0

    if timing and progress:
        logger.info(
            "oid=%s list funcs done num_functions=%d list_funcs_s=%.3f",
            oid,
            len(f_list),
            t_list,
        )

    addrs: List[str] = []
    names: List[str] = []
    previews: List[str] = []
    texts: List[str] = []

    # decompile loop
    num_decomp_calls = 0
    t_decomp0 = time.perf_counter()
    last_report_t = t_decomp0

    for addr, finfo in f_list:
        num_decomp_calls += 1
        decomp_results = _safe_decompile(oid, addr)
        text = _normalize_decomp_blob(decomp_results.get("decomp"), max_chars=max_chars)
        if text:
            addrs.append(str(addr))
            names.append(decomp_results.get("func_name"))
            previews.append(_first_preview_line(text))
            texts.append(text)

        if (
            timing
            and progress
            and progress_every > 0
            and (num_decomp_calls % progress_every == 0)
        ):
            now = time.perf_counter()
            dt = now - last_report_t
            elapsed = now - t_decomp0
            rate = (progress_every / dt) if dt > 0 else 0.0
            logger.info(
                "oid=%s decomp progress calls=%d/%d indexed=%d elapsed_s=%.3f rate_fps=%.2f",
                oid,
                num_decomp_calls,
                len(f_list),
                len(texts),
                elapsed,
                rate,
            )
            last_report_t = now

    t_decomp = time.perf_counter() - t_decomp0

    counts[oid] = {
        "cache": "miss",
        "num_functions": len(f_list),
        "num_indexed": len(texts),
    }

    if timing and progress:
        logger.info(
            "oid=%s decomp done decomp_s=%.3f num_decomp_calls=%d num_indexed=%d",
            oid,
            t_decomp,
            num_decomp_calls,
            len(texts),
        )

    if not texts:
        return None, _tinfo(
            timing,
            cache_hit=False,
            list_funcs_s=t_list,
            decomp_s=t_decomp,
            embed_s=0.0,
            store_s=0.0,
            num_decomp_calls=num_decomp_calls,
            build_total_s=time.perf_counter() - t0,
        )

    # embed
    t_embed0 = time.perf_counter()
    text_batch = _truncate_texts_for_model(texts, model)
    emb = model.encode(
        text_batch,
        batch_size=max(1, batch_size),
        normalize_embeddings=True,
        show_progress_bar=False,
    ).astype(np.float32)
    t_embed = time.perf_counter() - t_embed0

    if timing and progress:
        logger.info(
            "oid=%s embed done embed_s=%.3f vectors=%d dim=%d",
            oid,
            t_embed,
            emb.shape[0],
            emb.shape[1] if emb.ndim == 2 else -1,
        )

    idx = {
        "num_functions": len(f_list),
        "num_indexed": len(texts),
        "addrs": addrs,
        "names": names,
        "previews": previews,
        "emb": emb,
    }

    # store
    t_store = 0.0
    if use_cache:
        t_store0 = time.perf_counter()
        try:
            api.local_store(NAME, key, {oid: idx})
        except Exception:
            logger.exception("Failed to cache index for oid=%s", oid)
        t_store = time.perf_counter() - t_store0

        if timing and progress:
            logger.info(
                "oid=%s cache store done store_s=%.3f key=%s", oid, t_store, key
            )

    return idx, _tinfo(
        timing,
        cache_hit=False,
        list_funcs_s=t_list,
        decomp_s=t_decomp,
        embed_s=t_embed,
        store_s=t_store,
        num_decomp_calls=num_decomp_calls,
        build_total_s=time.perf_counter() - t0,
    )


# -----------------------------------------------------------------------------
# Candidate ranking
# -----------------------------------------------------------------------------
def _append_topk_candidates(
    *,
    candidates: List[Dict[str, Any]],
    oid: str,
    idx: Dict[str, Any],
    qvec: np.ndarray,
    top_k: int,
    loc: Optional[np.ndarray] = None,
    loc_sims: Optional[np.ndarray] = None,
) -> None:
    emb = idx["emb"]
    if loc is None or loc_sims is None:
        loc, loc_sims = _topk_indices_and_sims(emb, qvec, top_k)
    if loc.size == 0:
        return

    addrs = idx["addrs"]
    names = idx["names"]
    previews = idx["previews"]

    for i, score in zip(loc, loc_sims):
        candidates.append(
            {
                "oid": oid,
                "func_addr": addrs[i],
                "func_name": names[i],
                "score": float(score),
                "preview": previews[i],
            }
        )


def _topk_indices_and_sims(
    emb: np.ndarray, qvec: np.ndarray, top_k: int
) -> Tuple[np.ndarray, np.ndarray]:
    sims = emb.dot(qvec)
    if sims.size == 0:
        return np.asarray([], dtype=int), np.asarray([], dtype=np.float32)

    if top_k <= 0 or top_k >= sims.shape[0]:
        loc = np.argsort(-sims)
    else:
        loc = np.argpartition(-sims, top_k - 1)[:top_k]
        loc = loc[np.argsort(-sims[loc])]
    return loc, sims[loc]


def _aggregate_file_embedding(
    emb: np.ndarray,
    loc: np.ndarray,
    sims: np.ndarray,
    mode: str,
    attn_tau: float,
) -> Optional[np.ndarray]:
    if loc is None or loc.size == 0:
        return None

    vecs = emb[loc]
    if vecs.ndim != 2 or vecs.shape[0] == 0:
        return None

    if mode == "top1":
        agg = vecs[0]
    elif mode == "mean":
        agg = np.mean(vecs, axis=0)
    else:
        tau = attn_tau if attn_tau > 0 else 0.07
        logits = sims / tau
        logits = logits - np.max(logits)
        weights = np.exp(logits)
        denom = float(weights.sum())
        if denom <= 0:
            agg = np.mean(vecs, axis=0)
        else:
            weights = weights / denom
            agg = (vecs * weights[:, None]).sum(axis=0)

    norm = float(np.linalg.norm(agg))
    if norm > 0:
        agg = agg / norm
    return agg


# -----------------------------------------------------------------------------
# Timing helpers
# -----------------------------------------------------------------------------
def _tinfo(enabled: bool, **kw) -> Optional[Dict[str, Any]]:
    return kw if enabled else None


def _timing_summary(
    *,
    total_s: float,
    model_load_s: float,
    query_embed_s: float,
    oid_times: List[Dict[str, Any]],
    topn: int,
) -> Dict[str, Any]:
    def _top(key: str) -> List[Dict[str, Any]]:
        return sorted(oid_times, key=lambda x: x.get(key, 0.0), reverse=True)[
            : max(1, topn)
        ]

    return {
        "total_s": float(f"{total_s:.6f}"),
        "model_load_s": float(f"{model_load_s:.6f}"),
        "query_embed_s": float(f"{query_embed_s:.6f}"),
        "oids": len(oid_times),
        "worst_oids_by_total_s": _top("total_s"),
        "worst_oids_by_build_s": [
            x for x in _top("build_total_s") if x.get("build_total_s") is not None
        ],
    }


# -----------------------------------------------------------------------------
# IO + utilities
# -----------------------------------------------------------------------------
def _expand_oids_best_effort(oid_list: List[str]) -> List[str]:
    try:
        return api.expand_oids(oid_list)
    except Exception:
        return oid_list


def _load_query(opts: dict) -> str:
    q = (opts.get("query") or "").strip()
    qp = (opts.get("query_path") or "").strip()
    if q:
        return q
    if not qp:
        return ""
    try:
        with open(qp, "r", encoding="utf-8", errors="replace") as f:
            return f.read().strip()
    except OSError:
        return ""


def _as_int(v: Any, default: int) -> int:
    try:
        return int(v)
    except Exception:
        return default


def _as_float(v: Any, default: float) -> float:
    try:
        return float(v)
    except Exception:
        return default


def _as_bool(v: Any) -> bool:
    return bool(v)


def _cache_key(oid: str, model_id: str, max_chars: int) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", f"{oid}_{model_id}_{max_chars}")


def _iter_functions(funcs: Any):
    if isinstance(funcs, dict):
        for addr, finfo in funcs.items():
            yield addr, finfo
    elif isinstance(funcs, (list, tuple)):
        for addr in funcs:
            yield addr, None


def _safe_decompile(oid: str, addr: Any) -> Dict[str, Any]:
    """
    Oxide style output always dict.
    function_decomp is expected to return a dict that includes decomp.
    This unwraps either {oid: payload} or payload directly.
    """
    # function_decomp expects the option name "function_addr".
    res = api.retrieve("function_decomp", [oid], {"function_addr": addr})

    payload = None
    if isinstance(res, dict):
        payload = res.get(oid, res)
    else:
        payload = res

    if not isinstance(payload, dict):
        return {"func_addr": addr, "func_name": None, "decomp": payload}

    return {
        "func_addr": payload.get("func_addr", addr),
        "func_name": payload.get("func_name"),
        "decomp": payload.get("decomp"),
    }


def _first_preview_line(text: str) -> str:
    for line in text.splitlines():
        s = line.strip()
        if s:
            return s[:200]
    return ""


def _normalize_decomp_blob(f_decomp: Any, max_chars: int) -> str:
    if not f_decomp:
        return ""
    if isinstance(f_decomp, list):
        s = "\n".join([x for x in f_decomp if isinstance(x, str)]).strip()
    elif isinstance(f_decomp, str):
        s = f_decomp.strip()
    else:
        s = str(f_decomp).strip()
    if max_chars and len(s) > max_chars:
        return s[:max_chars]
    return s


def _truncate_text_for_model(text: str, model: "SentenceTransformer") -> str:
    """
    Quietly cap text length to model token budget before embedding.
    """
    s = str(text or "").strip()
    if not s:
        return s
    tokenizer = getattr(model, "tokenizer", None)
    max_tokens = int(getattr(model, "max_seq_length", 0) or 0)
    if tokenizer is None or max_tokens <= 0:
        return s

    try:
        enc = tokenizer(
            s,
            add_special_tokens=False,
            truncation=True,
            max_length=max_tokens,
            return_attention_mask=False,
            return_token_type_ids=False,
            verbose=False,
        )
    except TypeError:
        # Some tokenizers do not support the `verbose` kwarg.
        try:
            enc = tokenizer(
                s,
                add_special_tokens=False,
                truncation=True,
                max_length=max_tokens,
                return_attention_mask=False,
                return_token_type_ids=False,
            )
        except Exception:
            return s
    except Exception:
        return s

    ids = enc.get("input_ids") if isinstance(enc, dict) else None
    if ids is None:
        return s
    if isinstance(ids, list) and ids and isinstance(ids[0], list):
        ids = ids[0]
    if not isinstance(ids, list) or not ids:
        return s

    try:
        out = str(
            tokenizer.decode(
                ids,
                skip_special_tokens=True,
                clean_up_tokenization_spaces=True,
            )
            or ""
        ).strip()
        return out or s
    except Exception:
        return s


def _truncate_texts_for_model(
    texts: List[str], model: "SentenceTransformer"
) -> List[str]:
    return [_truncate_text_for_model(t, model) for t in texts]


# -----------------------------------------------------------------------------
# Model singleton
# -----------------------------------------------------------------------------
_MODEL: Optional["SentenceTransformer"] = None
_MODEL_ID: Optional[str] = None


def _get_model(model_id: str) -> "SentenceTransformer":
    from sentence_transformers import SentenceTransformer

    global _MODEL, _MODEL_ID
    if _MODEL is None or _MODEL_ID != model_id:
        _MODEL = SentenceTransformer(model_id)
        _MODEL_ID = model_id
    return _MODEL
