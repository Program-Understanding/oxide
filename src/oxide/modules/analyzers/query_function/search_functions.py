"""search_functions backend: sentence-embedding search over decompiled C.

Indexes each function's decompiler output with a general-purpose sentence
encoder and ranks functions by cosine similarity to the query. This is the
retrieval surface the agent's search_functions tool calls.
"""

import logging
import re
import time
from typing import Any, Dict, List, Optional, Tuple

import numpy as np

from oxide.core import api
from oxide.modules.analyzers.query_function.config import NAME
from oxide.modules.analyzers.query_function.common import (
    as_bool,
    as_float,
    as_int,
    extract_func_name,
    first_preview_line,
    iter_functions,
    load_text_option,
    result_limit,
)

logger = logging.getLogger(NAME)


FAILED_DECOMP_INDEX_KEYS: set[str] = set()


def results(oids: List[str], opts: dict) -> Dict[str, Any]:
    t_total0 = time.perf_counter()
    query = load_text_option(opts, "query", "query_path")
    if not query:
        return {"error": "Please provide a query via 'query' or 'query_path'."}

    limit = result_limit(opts)
    offset = max(0, as_int(opts.get("offset", 0), 0))
    top_k = limit
    search_mode = (opts.get("search_mode") or "semantic").strip().lower()
    if search_mode not in ("semantic", "literal", "both"):
        return {
            "error": f"Unsupported search_mode: {search_mode}",
            "supported_search_modes": ["semantic", "literal", "both"],
        }

    include_full_code = as_bool(opts.get("include_full_code", True))
    preview_length = max(0, as_int(opts.get("preview_length", 500), 500))
    similarity_threshold = as_float(opts.get("similarity_threshold", 0.0), 0.0)
    max_chars = as_int(opts.get("max_chars", 20000), 20000)
    batch_size = max(1, as_int(opts.get("batch_size", 64), 64))
    use_cache = as_bool(opts.get("use_cache", True))
    rebuild = as_bool(opts.get("rebuild", False))
    timing = as_bool(opts.get("timing", True))
    progress = as_bool(opts.get("progress", True))
    progress_every = as_int(opts.get("progress_every", 50), 50)
    timing_topn = as_int(opts.get("timing_topn", 5), 5)
    model_id = (opts.get("model_id") or "sentence-transformers/all-MiniLM-L6-v2").strip()
    return_file_embeddings = as_bool(opts.get("return_file_embeddings", False))
    file_agg = (opts.get("file_agg") or "attn").strip().lower()
    if file_agg not in ("top1", "mean", "attn"):
        file_agg = "attn"
    attn_tau = as_float(opts.get("attn_tau", 0.07), 0.07)
    if attn_tau <= 0:
        attn_tau = 0.07

    model = None
    qvec = None
    t_model = 0.0
    t_qemb = 0.0
    needs_embeddings = search_mode in ("semantic", "both") or return_file_embeddings
    if needs_embeddings:
        try:
            t0 = time.perf_counter()
            model = _get_sentence_model(model_id)
            t_model = time.perf_counter() - t0
            t0 = time.perf_counter()
            qvec = model.encode(_truncate_text_for_model(query, model), normalize_embeddings=True).astype(np.float32)
            t_qemb = time.perf_counter() - t0
        except ImportError as err:
            return {
                "error": str(err),
                "hint": "Install sentence-transformers to use backend='search_functions' semantic search.",
            }
        except Exception as err:
            logger.exception("Failed to load or run sentence-transformer model")
            return {"error": f"Failed to load model '{model_id}': {err}"}

    if timing and progress:
        logger.info(
            "query_function start backend=search_functions oids=%d mode=%s model_load_s=%.3f query_embed_s=%.3f",
            len(oids), search_mode, t_model, t_qemb,
        )

    counts: Dict[str, Dict[str, Any]] = {}
    semantic_candidates: List[Dict[str, Any]] = []
    literal_candidates: List[Dict[str, Any]] = []
    oid_times: List[Dict[str, Any]] = []
    file_embeddings: Dict[str, List[float]] = {}
    file_scores: Dict[str, float] = {}
    total_functions = 0

    for idx_oid, oid in enumerate(oids, start=1):
        t_oid0 = time.perf_counter()
        if timing and progress:
            logger.info("oid %d/%d start oid=%s", idx_oid, len(oids), oid)

        idx, tinfo = _load_or_build_decomp_index(
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
        if not idx:
            continue

        total_functions += int(idx.get("num_indexed", 0) or 0)
        literal_candidates.extend(_literal_decomp_results(
            idx, oid, query, include_full_code, preview_length,
        ))

        if qvec is not None and idx.get("emb") is not None and idx["emb"].size > 0:
            sims = idx["emb"].dot(qvec)
            semantic_candidates.extend(_semantic_decomp_results(
                idx, oid, sims, similarity_threshold, include_full_code, preview_length,
            ))
            if return_file_embeddings:
                loc, loc_sims = _topk_indices_and_sims(idx["emb"], qvec, top_k)
                file_emb = _aggregate_file_embedding(idx["emb"], loc, loc_sims, file_agg, attn_tau)
                if file_emb is not None:
                    file_embeddings[oid] = file_emb.astype(np.float32).tolist()
                    file_scores[oid] = float(file_emb.dot(qvec))

        if timing:
            entry = {"oid": oid, "total_s": time.perf_counter() - t_oid0}
            if tinfo:
                entry.update(tinfo)
            oid_times.append(entry)
        if timing and progress:
            logger.info(
                "oid %d/%d done oid=%s total_s=%.3f cache=%s indexed=%s",
                idx_oid, len(oids), oid, time.perf_counter() - t_oid0,
                (counts.get(oid) or {}).get("cache"),
                (counts.get(oid) or {}).get("num_indexed"),
            )

    semantic_candidates.sort(key=lambda x: x["similarity"], reverse=True)
    literal_candidates.sort(key=lambda x: (x["oid"], x["function_name"]))
    selected = _select_decomp_candidates(search_mode, semantic_candidates, literal_candidates)
    page = selected[offset:offset + limit] if limit > 0 else selected[offset:]

    out: Dict[str, Any] = {
        "query": query,
        "backend": "search_functions",
        "search_mode": search_mode,
        "returned_count": len(page),
        "offset": offset,
        "limit": limit,
        "literal_total": len(literal_candidates),
        "semantic_total": len(semantic_candidates) if needs_embeddings else total_functions,
        "total_functions": total_functions,
        "counts": counts,
        "results": {"best_match": page[0] if page else None, "candidates": page},
        "notes": {
            "model_id": model_id,
            "similarity": "cosine (normalized dot product)",
            "file_agg": file_agg,
            "attn_tau": attn_tau,
            "mimics": "pyghidra-mcp search_code/search_function style: semantic/literal modes, pagination, full-code toggle, and mode counts.",
        },
    }
    if not page:
        out["warning"] = "No indexed functions available (no decomp output or no functions found)."
    if return_file_embeddings:
        out["file_embeddings"] = file_embeddings
        out["file_scores"] = file_scores
    if timing:
        out["timing"] = _timing_summary(
            total_s=time.perf_counter() - t_total0,
            model_load_s=t_model,
            query_embed_s=t_qemb,
            oid_times=oid_times,
            topn=timing_topn,
        )
    return out


def _load_or_build_decomp_index(
    *,
    oid: str,
    model_id: str,
    max_chars: int,
    batch_size: int,
    use_cache: bool,
    rebuild: bool,
    model: Optional[Any],
    counts: Dict[str, Dict[str, Any]],
    timing: bool,
    progress: bool,
    progress_every: int,
) -> Tuple[Optional[Dict[str, Any]], Optional[Dict[str, Any]]]:
    t0 = time.perf_counter()
    include_embeddings = model is not None
    key = _decomp_cache_key(oid, model_id, max_chars, include_embeddings)
    if use_cache and (not rebuild) and key in FAILED_DECOMP_INDEX_KEYS:
        counts[oid] = {
            "cache": "skip",
            "num_functions": 0,
            "num_indexed": 0,
            "skip_reason": "cached_missing_ghidra_decmap",
        }
        return None, _tinfo(timing, cache_hit=True, build_total_s=time.perf_counter() - t0)

    if use_cache and (not rebuild) and api.local_exists(NAME, key):
        try:
            blob = api.local_retrieve(NAME, key) or {}
            idx = blob.get(oid)
            if isinstance(idx, dict) and idx.get("_skip_reason") == "missing_ghidra_decmap":
                FAILED_DECOMP_INDEX_KEYS.add(key)
                counts[oid] = {
                    "cache": "skip",
                    "num_functions": int(idx.get("num_functions", 0) or 0),
                    "num_indexed": 0,
                    "skip_reason": "cached_missing_ghidra_decmap",
                }
                return None, _tinfo(timing, cache_hit=True, build_total_s=time.perf_counter() - t0)
            if idx and ("codes" in idx) and ((not include_embeddings) or ("emb" in idx)):
                counts[oid] = {
                    "cache": "hit",
                    "num_functions": idx.get("num_functions", 0),
                    "num_indexed": idx.get("num_indexed", 0),
                }
                return idx, _tinfo(timing, cache_hit=True, build_total_s=time.perf_counter() - t0)
        except Exception:
            logger.exception("Failed to load cached index for oid=%s", oid)

    t_list0 = time.perf_counter()
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    f_list = list(iter_functions(funcs))
    t_list = time.perf_counter() - t_list0

    addrs: List[str] = []
    names: List[str] = []
    texts: List[str] = []
    previews: List[str] = []
    codes: List[str] = []
    decompile = _get_decompile_map(oid)
    if not decompile:
        FAILED_DECOMP_INDEX_KEYS.add(key)
        counts[oid] = {
            "cache": "miss",
            "num_functions": len(f_list),
            "num_indexed": 0,
            "skip_reason": "missing_ghidra_decmap",
        }
        if use_cache:
            try:
                api.local_store(
                    NAME,
                    key,
                    {
                        oid: {
                            "_skip_reason": "missing_ghidra_decmap",
                            "num_functions": len(f_list),
                            "num_indexed": 0,
                        }
                    },
                )
            except Exception:
                logger.exception("Failed to cache decomp skip sentinel for oid=%s", oid)
        return None, _tinfo(
            timing,
            cache_hit=False,
            list_funcs_s=t_list,
            decomp_s=0.0,
            embed_s=0.0,
            store_s=0.0,
            build_total_s=time.perf_counter() - t0,
        )

    t_decomp0 = time.perf_counter()
    last_report_t = t_decomp0
    for count, (addr, finfo) in enumerate(f_list, start=1):
        func_name = extract_func_name(finfo, addr)
        key_name = func_name if func_name in decompile else _resolve_decomp_key(decompile, func_name)
        text = _normalize_decomp_blob(_decomp_text_from_blocks(decompile.get(key_name)), max_chars=max_chars) if key_name else ""
        if not text:
            text = _normalize_decomp_blob(_safe_decompile(oid, addr), max_chars=max_chars)
        if text:
            addrs.append(str(addr))
            names.append(func_name)
            texts.append(text)
            codes.append(text)
            previews.append(first_preview_line(text))
        if timing and progress and progress_every > 0 and count % progress_every == 0:
            now = time.perf_counter()
            elapsed = now - t_decomp0
            rate = progress_every / (now - last_report_t) if now > last_report_t else 0.0
            logger.info(
                "oid=%s decomp progress calls=%d/%d indexed=%d elapsed_s=%.3f rate_fps=%.2f",
                oid, count, len(f_list), len(texts), elapsed, rate,
            )
            last_report_t = now
    t_decomp = time.perf_counter() - t_decomp0

    counts[oid] = {"cache": "miss", "num_functions": len(f_list), "num_indexed": len(texts)}
    if not texts:
        return None, _tinfo(
            timing,
            cache_hit=False,
            list_funcs_s=t_list,
            decomp_s=t_decomp,
            embed_s=0.0,
            store_s=0.0,
            build_total_s=time.perf_counter() - t0,
        )

    idx: Dict[str, Any] = {
        "num_functions": len(f_list),
        "num_indexed": len(texts),
        "addrs": addrs,
        "names": names,
        "previews": previews,
        "texts": texts,
        "codes": codes,
    }

    t_embed = 0.0
    if include_embeddings:
        t_embed0 = time.perf_counter()
        idx["emb"] = model.encode(
            _truncate_texts_for_model(texts, model),
            batch_size=batch_size,
            normalize_embeddings=True,
            show_progress_bar=False,
        ).astype(np.float32)
        t_embed = time.perf_counter() - t_embed0

    t_store = 0.0
    if use_cache:
        t_store0 = time.perf_counter()
        try:
            api.local_store(NAME, key, {oid: idx})
        except Exception:
            logger.exception("Failed to cache index for oid=%s", oid)
        t_store = time.perf_counter() - t_store0

    return idx, _tinfo(
        timing,
        cache_hit=False,
        list_funcs_s=t_list,
        decomp_s=t_decomp,
        embed_s=t_embed,
        store_s=t_store,
        build_total_s=time.perf_counter() - t0,
    )


def _select_decomp_candidates(
    search_mode: str,
    semantic_candidates: List[Dict[str, Any]],
    literal_candidates: List[Dict[str, Any]],
) -> List[Dict[str, Any]]:
    if search_mode == "literal":
        return literal_candidates
    if search_mode == "both":
        lit_keys = {(c["oid"], c["function_addr"]) for c in literal_candidates}
        sem_only = [c for c in semantic_candidates if (c["oid"], c["function_addr"]) not in lit_keys]
        return literal_candidates + sem_only
    return semantic_candidates


def _literal_decomp_results(
    idx: Dict[str, Any],
    oid: str,
    query: str,
    include_full_code: bool,
    preview_length: int,
) -> List[Dict[str, Any]]:
    query_lower = query.lower()
    results = []
    for i, code in enumerate(idx.get("codes", [])):
        if query_lower not in str(code).lower():
            continue
        results.append(_decomp_search_candidate(
            idx, oid, i, code, 1.0, "literal", include_full_code, preview_length,
        ))
    return results


def _semantic_decomp_results(
    idx: Dict[str, Any],
    oid: str,
    sims: np.ndarray,
    similarity_threshold: float,
    include_full_code: bool,
    preview_length: int,
) -> List[Dict[str, Any]]:
    results = []
    codes = idx.get("codes", [])
    for i in np.argsort(-sims):
        similarity = float(sims[i])
        if similarity < similarity_threshold:
            continue
        code = codes[int(i)] if int(i) < len(codes) else ""
        results.append(_decomp_search_candidate(
            idx, oid, int(i), code, similarity, "semantic", include_full_code, preview_length,
        ))
    return results


def _decomp_search_candidate(
    idx: Dict[str, Any],
    oid: str,
    i: int,
    code: str,
    similarity: float,
    search_mode: str,
    include_full_code: bool,
    preview_length: int,
) -> Dict[str, Any]:
    preview = _preview(code, preview_length)
    return {
        "oid": oid,
        "function_addr": idx["addrs"][i],
        "function_name": idx["names"][i],
        "func_addr": idx["addrs"][i],
        "func_name": idx["names"][i],
        "code": code if include_full_code else preview,
        "score": similarity,
        "similarity": similarity,
        "search_mode": search_mode,
        "match_type": search_mode,
        "preview": None if include_full_code else preview,
    }


def _topk_indices_and_sims(emb: np.ndarray, qvec: np.ndarray, top_k: int) -> Tuple[np.ndarray, np.ndarray]:
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
        logits = sims / (attn_tau if attn_tau > 0 else 0.07)
        logits = logits - np.max(logits)
        weights = np.exp(logits)
        denom = float(weights.sum())
        agg = np.mean(vecs, axis=0) if denom <= 0 else (vecs * (weights / denom)[:, None]).sum(axis=0)
    norm = float(np.linalg.norm(agg))
    return agg / norm if norm > 0 else agg


def _get_decompile_map(oid: str) -> Dict[str, Any]:
    decmap = api.retrieve("ghidra_decmap", [oid], {"org_by_func": True})
    if not isinstance(decmap, dict) or not decmap:
        return {}
    inner = decmap.get(oid)
    dm = inner if isinstance(inner, dict) else decmap
    decompile = dm.get("decompile") if isinstance(dm, dict) else None
    return decompile if isinstance(decompile, dict) else {}


def _resolve_decomp_key(decompile: Dict[str, Any], want: str) -> Optional[str]:
    if want in decompile:
        return want
    want_short = want.split("::")[-1]
    cands = [k for k in decompile if isinstance(k, str) and k.split("::")[-1] == want_short]
    return cands[0] if len(cands) == 1 else None


def _decomp_text_from_blocks(func_blocks: Any) -> str:
    if not isinstance(func_blocks, dict):
        return ""
    decomp_map: Dict[int, str] = {}
    untagged_fallback: List[str] = []
    for block in func_blocks.values():
        if not isinstance(block, dict):
            continue
        lines = block.get("line") or []
        if not isinstance(lines, list):
            continue
        for raw in lines:
            if not isinstance(raw, str):
                continue
            try:
                left, right = raw.split(":", 1)
                decomp_map.setdefault(int(left.strip()), right.rstrip("\r\n"))
            except Exception:
                untagged_fallback.append(raw.rstrip("\r\n"))
    if decomp_map:
        return "\n".join(decomp_map[ln] for ln in sorted(decomp_map))
    return "\n".join(untagged_fallback)


def _safe_decompile(oid: str, addr: Any) -> Any:
    try:
        res = api.retrieve("function_decomp", [oid], {"function_addr": str(addr)})
        return res.get(oid, res) if isinstance(res, dict) else res
    except Exception:
        logger.debug("Decompile fallback failed oid=%s addr=%s", oid, addr, exc_info=True)
        return None


def _preview(code: str, preview_length: int) -> str:
    if preview_length <= 0:
        return ""
    return code[:preview_length] + "..." if len(code) > preview_length else code


def _normalize_decomp_blob(f_decomp: Any, max_chars: int) -> str:
    if not f_decomp:
        return ""
    if isinstance(f_decomp, list):
        text = "\n".join([x for x in f_decomp if isinstance(x, str)]).strip()
    elif isinstance(f_decomp, str):
        text = f_decomp.strip()
    else:
        text = str(f_decomp).strip()
    return text[:max_chars] if (max_chars and len(text) > max_chars) else text


def _truncate_text_for_model(text: str, model: Any) -> str:
    text = str(text or "").strip()
    tokenizer = getattr(model, "tokenizer", None)
    max_tokens = int(getattr(model, "max_seq_length", 0) or 0)
    if not text or tokenizer is None or max_tokens <= 0:
        return text
    try:
        enc = tokenizer(
            text,
            add_special_tokens=False,
            truncation=True,
            max_length=max_tokens,
            return_attention_mask=False,
            return_token_type_ids=False,
        )
        ids = enc.get("input_ids") if isinstance(enc, dict) else None
        if isinstance(ids, list) and ids and isinstance(ids[0], list):
            ids = ids[0]
        if isinstance(ids, list) and ids:
            return tokenizer.decode(ids, skip_special_tokens=True, clean_up_tokenization_spaces=True).strip() or text
    except Exception:
        return text
    return text


def _truncate_texts_for_model(texts: List[str], model: Any) -> List[str]:
    return [_truncate_text_for_model(t, model) for t in texts]


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
        return sorted(oid_times, key=lambda x: x.get(key, 0.0), reverse=True)[: max(1, topn)]

    return {
        "total_s": float(f"{total_s:.6f}"),
        "model_load_s": float(f"{model_load_s:.6f}"),
        "query_embed_s": float(f"{query_embed_s:.6f}"),
        "oids": len(oid_times),
        "worst_oids_by_total_s": _top("total_s"),
        "worst_oids_by_build_s": [x for x in _top("build_total_s") if x.get("build_total_s") is not None],
    }


def _decomp_cache_key(oid: str, model_id: str, max_chars: int, include_embeddings: bool) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", f"decomp_v2_{oid}_{model_id}_{max_chars}_{include_embeddings}")


SENTENCE_MODEL: Optional[Any] = None


SENTENCE_MODEL_ID: Optional[str] = None


def _get_sentence_model(model_id: str) -> Any:
    global SENTENCE_MODEL, SENTENCE_MODEL_ID
    if SENTENCE_MODEL is None or SENTENCE_MODEL_ID != model_id:
        try:
            from sentence_transformers import SentenceTransformer
        except ImportError as err:
            raise ImportError("query_function backend='search_functions' requires sentence-transformers.") from err
        SENTENCE_MODEL = SentenceTransformer(model_id)
        SENTENCE_MODEL_ID = model_id
    return SENTENCE_MODEL
