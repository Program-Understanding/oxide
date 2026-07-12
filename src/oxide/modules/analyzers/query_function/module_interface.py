DESC = "Semantic search over functions using decompiler text or CLAP assembly embeddings."
NAME = "query_function"

import logging
import re
<<<<<<< Updated upstream
import time
from typing import Any, Dict, List, Optional, Tuple
=======
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple
>>>>>>> Stashed changes

import numpy as np

from oxide.core import api

logger = logging.getLogger(NAME)

<<<<<<< Updated upstream
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
    # search mode: "semantic" (default), "literal" (substring), or "both"
    "search_mode": {"type": str, "mangle": False, "default": "semantic"},
    "similarity_threshold": {"type": float, "mangle": False, "default": 0.0},
=======
opts_doc = {
    "query": {"type": str, "mangle": True, "default": ""},
    "query_path": {"type": str, "mangle": True, "default": ""},
    "prompts": {"type": str, "mangle": True, "default": ""},
    "prompts_path": {"type": str, "mangle": True, "default": ""},
    "backend": {"type": str, "mangle": True, "default": "decomp_minilm"},
    "top_k": {"type": int, "mangle": False, "default": 10},
    "limit": {"type": int, "mangle": False, "default": 0},
    "offset": {"type": int, "mangle": False, "default": 0},
    "search_mode": {"type": str, "mangle": False, "default": "semantic"},
    "include_full_code": {"type": bool, "mangle": False, "default": True},
    "preview_length": {"type": int, "mangle": False, "default": 500},
    "similarity_threshold": {"type": float, "mangle": False, "default": 0.0},
    "max_chars": {"type": int, "mangle": True, "default": 20000},
    "max_instructions": {"type": int, "mangle": True, "default": 512},
    "batch_size": {"type": int, "mangle": False, "default": 64},
    "use_cache": {"type": bool, "mangle": False, "default": True},
    "rebuild": {"type": bool, "mangle": False, "default": False},
    "model_id": {"type": str, "mangle": True, "default": "sentence-transformers/all-MiniLM-L6-v2"},
    "asm_model_id": {"type": str, "mangle": True, "default": "hustcw/clap-asm"},
    "text_model_id": {"type": str, "mangle": True, "default": "hustcw/clap-text"},
    "device": {"type": str, "mangle": False, "default": "auto"},
    "temperature": {"type": float, "mangle": False, "default": 0.07},
    "normalize_embeddings": {"type": bool, "mangle": True, "default": False},
>>>>>>> Stashed changes
}


def documentation() -> Dict[str, Any]:
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }


<<<<<<< Updated upstream
# -----------------------------------------------------------------------------
# Main
# -----------------------------------------------------------------------------
=======
>>>>>>> Stashed changes
def results(oid_list: List[str], opts: dict) -> Dict[str, Any]:
    t_total0 = time.perf_counter()

    timing = _as_bool(opts.get("timing", True))
    topn = _as_int(opts.get("timing_topn", 5), 5)

    progress = _as_bool(opts.get("progress", True))
    progress_every = _as_int(opts.get("progress_every", 50), 50)

    oids = _expand_oids_best_effort(oid_list)

    backend = (opts.get("backend") or "decomp_minilm").strip().lower()
    if backend in ("decomp", "decompiler", "minilm", "decomp_minilm"):
        return _decomp_minilm_results(oids, opts)
    if backend in ("clap", "clap_asm", "asm_clap"):
        return _clap_asm_results(oids, opts)
    return {
        "error": f"Unsupported backend: {backend}",
        "supported_backends": ["decomp_minilm", "clap_asm"],
    }


def _decomp_minilm_results(oids: List[str], opts: dict) -> Dict[str, Any]:
    query = _load_text_option(opts, "query", "query_path")
    if not query:
        return {"error": "Please provide a query via 'query' or 'query_path'."}

<<<<<<< Updated upstream
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
    search_mode = (opts.get("search_mode") or "semantic").strip().lower()
    if search_mode not in ("semantic", "literal", "both"):
        search_mode = "semantic"
    similarity_threshold = _as_float(opts.get("similarity_threshold", 0.0), 0.0)

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
=======
    limit = _result_limit(opts)
    offset = max(0, int(opts.get("offset", 0) or 0))
    search_mode = (opts.get("search_mode") or "semantic").strip().lower()
    include_full_code = bool(opts.get("include_full_code", True))
    preview_length = max(0, int(opts.get("preview_length", 500) or 500))
    similarity_threshold = float(opts.get("similarity_threshold", 0.0) or 0.0)
    max_chars = int(opts.get("max_chars", 20000) or 20000)
    batch_size = max(1, int(opts.get("batch_size", 64) or 64))
    model_id = (opts.get("model_id") or "sentence-transformers/all-MiniLM-L6-v2").strip()
    use_cache = bool(opts.get("use_cache", True))
    rebuild = bool(opts.get("rebuild", False))

    if search_mode not in ("semantic", "literal"):
        return {"error": f"Unsupported search_mode: {search_mode}", "supported_search_modes": ["semantic", "literal"]}
>>>>>>> Stashed changes

    model = None
    qvec = None
    if search_mode == "semantic":
        try:
            model = _get_sentence_model(model_id)
        except ImportError as err:
            return {
                "error": str(err),
                "hint": "Install sentence-transformers to use backend='decomp_minilm' search_mode='semantic'.",
            }
        except Exception as err:
            logger.exception("Failed to load sentence-transformer model")
            return {"error": f"Failed to load model '{model_id}': {err}"}
        qvec = model.encode(query, normalize_embeddings=True).astype(np.float32)
    counts: Dict[str, Dict[str, Any]] = {}
<<<<<<< Updated upstream
    candidates: List[Dict[str, Any]] = []
    literal_candidates: List[Dict[str, Any]] = []
    oid_times: List[Dict[str, Any]] = []
    file_embeddings: Dict[str, List[float]] = {}
    file_scores: Dict[str, float] = {}
    total_semantic: int = 0
    total_literal: int = 0

    for idx_oid, oid in enumerate(oids, start=1):
        t_oid0 = time.perf_counter()

        if timing and progress:
            logger.info("oid %d/%d start oid=%s", idx_oid, len(oids), oid)

        idx, tinfo = _load_or_build_index(
=======
    semantic_candidates: List[Dict[str, Any]] = []
    literal_candidates: List[Dict[str, Any]] = []
    total_functions = 0

    for oid in oids:
        idx = _load_or_build_decomp_index(
>>>>>>> Stashed changes
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

<<<<<<< Updated upstream
        t_search0 = time.perf_counter()
        if idx and idx.get("emb") is not None and idx["emb"].size > 0:
            # Always run semantic search for file embeddings and counts
            loc, loc_sims = _topk_indices_and_sims(idx["emb"], qvec, top_k)
            sem_cands: List[Dict[str, Any]] = []
            _append_topk_candidates(
                candidates=sem_cands,
                oid=oid,
                idx=idx,
                qvec=qvec,
                top_k=top_k,
                loc=loc,
                loc_sims=loc_sims,
            )
            # Apply similarity threshold and tag match type
            for c in sem_cands:
                c["match_type"] = "semantic"
                if c["score"] >= similarity_threshold:
                    candidates.append(c)
                    total_semantic += 1

            if return_file_embeddings:
                file_emb = _aggregate_file_embedding(
                    idx["emb"], loc, loc_sims, file_agg, attn_tau
                )
                if file_emb is not None:
                    file_embeddings[oid] = file_emb.astype(np.float32).tolist()
                    file_scores[oid] = float(file_emb.dot(qvec))

        # Always run literal search for count reporting
        lit_cands = _literal_matches(oid, idx, query, top_k)
        total_literal += len(lit_cands)
        for c in lit_cands:
            literal_candidates.append(c)

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

    # Select final candidates based on search_mode
    if search_mode == "literal":
        final_candidates = sorted(literal_candidates, key=lambda x: x["score"], reverse=True)
    elif search_mode == "both":
        # Merge: literal matches first, then semantic results not already matched literally
        lit_keys = {(c["oid"], c["func_addr"]) for c in literal_candidates}
        sem_only = [c for c in candidates if (c["oid"], c["func_addr"]) not in lit_keys]
        final_candidates = literal_candidates + sorted(sem_only, key=lambda x: x["score"], reverse=True)
    else:
        final_candidates = sorted(candidates, key=lambda x: x["score"], reverse=True)

=======
        total_functions += int(idx.get("num_indexed", 0) or 0)
        literal_candidates.extend(_literal_decomp_results(
            idx,
            oid,
            query=query,
            include_full_code=include_full_code,
            preview_length=preview_length,
        ))
        if search_mode == "semantic" and qvec is not None:
            semantic_candidates.extend(_semantic_decomp_results(
                idx,
                oid,
                sims=idx["emb"].dot(qvec),
                similarity_threshold=similarity_threshold,
                include_full_code=include_full_code,
                preview_length=preview_length,
            ))

    semantic_candidates.sort(key=lambda x: x["similarity"], reverse=True)
    literal_candidates.sort(key=lambda x: (x["oid"], x["function_name"]))
    semantic_total = len(semantic_candidates) if search_mode == "semantic" else total_functions
    selected = literal_candidates if search_mode == "literal" else semantic_candidates
    page = selected[offset:offset + limit] if limit > 0 else selected[offset:]

    if not page:
        return {
            "query": query,
            "backend": "decomp_minilm",
            "search_mode": search_mode,
            "returned_count": 0,
            "offset": offset,
            "limit": limit,
            "literal_total": len(literal_candidates),
            "semantic_total": semantic_total,
            "total_functions": total_functions,
            "counts": counts,
            "results": {"best_match": None, "candidates": []},
            "warning": "No indexed functions available (no decomp output or no functions found).",
        }

    return {
        "query": query,
        "backend": "decomp_minilm",
        "search_mode": search_mode,
        "returned_count": len(page),
        "offset": offset,
        "limit": limit,
        "literal_total": len(literal_candidates),
        "semantic_total": semantic_total,
        "total_functions": total_functions,
        "counts": counts,
        "results": {"best_match": page[0], "candidates": page},
        "notes": {
            "model_id": model_id,
            "similarity": "cosine (normalized dot product)",
            "mimics": "pyghidra-mcp search_code/search_function result shape: semantic/literal modes, pagination, full-code toggle, and dual-mode counts.",
        },
    }


def _clap_asm_results(oids: List[str], opts: dict) -> Dict[str, Any]:
    prompts = _load_prompts(opts)
    if not prompts:
        return {"error": "Please provide 'query', 'query_path', 'prompts', or 'prompts_path'."}

    top_k = int(opts.get("top_k", 10) or 10)
    max_instructions = int(opts.get("max_instructions", 512) or 512)
    batch_size = max(1, int(opts.get("batch_size", 16) or 16))
    use_cache = bool(opts.get("use_cache", True))
    rebuild = bool(opts.get("rebuild", False))
    normalize = bool(opts.get("normalize_embeddings", False))
    temperature = float(opts.get("temperature", 0.07) or 0.07)
    asm_model_id = (opts.get("asm_model_id") or "hustcw/clap-asm").strip()
    text_model_id = (opts.get("text_model_id") or "hustcw/clap-text").strip()

    try:
        encoders = _get_clap_encoders(
            asm_model_id=asm_model_id,
            text_model_id=text_model_id,
            device=(opts.get("device") or "auto").strip(),
        )
    except ImportError as err:
        return {
            "error": str(err),
            "hint": "Install torch and transformers to use backend='clap_asm'.",
        }
    except Exception as err:
        logger.exception("Failed to load CLAP models")
        return {"error": f"Failed to load CLAP models: {err}"}

    text_emb = _encode_clap_texts(encoders, prompts, batch_size=batch_size, normalize=normalize)
    counts: Dict[str, Dict[str, Any]] = {}
    global_candidates: List[Dict[str, Any]] = []
    per_function_labels: List[Dict[str, Any]] = []

    for oid in oids:
        idx = _load_or_build_clap_index(
            oid=oid,
            asm_model_id=asm_model_id,
            max_instructions=max_instructions,
            batch_size=batch_size,
            use_cache=use_cache,
            rebuild=rebuild,
            normalize=normalize,
            encoders=encoders,
            counts=counts,
        )
        if not idx:
            continue

        logits = idx["emb"].dot(text_emb.T)
        scores = _softmax(logits / temperature, axis=1) if len(prompts) > 1 else logits

        if len(prompts) == 1:
            global_candidates.extend(_rank_single_prompt(idx, oid, scores[:, 0], top_k, prompt=prompts[0]))
            continue

        best = np.argmax(scores, axis=1)
        confidence = scores[np.arange(scores.shape[0]), best]
        for i, prompt_index in enumerate(best):
            per_function_labels.append({
                "oid": oid,
                "function_addr": idx["addrs"][i],
                "function_name": idx["names"][i],
                "prompt": prompts[int(prompt_index)],
                "prompt_index": int(prompt_index),
                "score": float(confidence[i]),
                "preview": idx["previews"][i],
            })

        flat = []
        for i in range(scores.shape[0]):
            for j in range(scores.shape[1]):
                flat.append((float(scores[i, j]), i, j))
        flat.sort(key=lambda x: x[0], reverse=True)
        for score, i, j in flat[:top_k if top_k > 0 else len(flat)]:
            global_candidates.append(_candidate(idx, oid, i, score, prompts[j], prompt_index=j))

    global_candidates.sort(key=lambda x: x["score"], reverse=True)
>>>>>>> Stashed changes
    if top_k > 0:
        final_candidates = final_candidates[:top_k]

<<<<<<< Updated upstream
    no_results = not final_candidates
    out = {
        "query": query,
        "counts": counts,
        "search_mode": search_mode,
        "semantic_total": total_semantic,
        "literal_total": total_literal,
        "results": {
            "best_match": final_candidates[0] if final_candidates else None,
            "candidates": final_candidates,
=======
    result: Dict[str, Any] = {
        "prompts": prompts,
        "backend": "clap_asm",
        "counts": counts,
        "results": {
            "best_match": global_candidates[0] if global_candidates else None,
            "candidates": global_candidates,
        },
        "notes": {
            "asm_model_id": asm_model_id,
            "text_model_id": text_model_id,
            "similarity": "dot product over CLAP assembly/text embeddings",
            "temperature": temperature,
            "normalized": normalize,
            "sources": [
                "https://arxiv.org/abs/2402.16928",
                "https://github.com/Hustcw/CLAP",
                "https://huggingface.co/hustcw/clap-asm",
            ],
>>>>>>> Stashed changes
        },
    }
    if len(prompts) > 1:
        result["results"]["per_function_best_label"] = per_function_labels
    if not global_candidates:
        result["warning"] = "No indexed functions available from ghidra_disasm."
    return result

<<<<<<< Updated upstream
    if no_results:
        out["warning"] = "No indexed functions available (no decomp output or no functions found)."

    out["notes"] = {
        "model_id": model_id,
        "similarity": "cosine (normalized dot product)",
        "file_agg": file_agg,
        "attn_tau": attn_tau,
        "file_top_k": top_k,
    }
    if return_file_embeddings:
        out["file_embeddings"] = file_embeddings
        out["file_scores"] = file_scores
        out["notes"].update({"file_agg": file_agg, "attn_tau": attn_tau})

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
                "query_function done total_s=%.3f oids=%d semantic=%d literal=%d mode=%s",
                out["timing"]["total_s"],
                len(oids),
                total_semantic,
                total_literal,
                search_mode,
            )

    return out


# -----------------------------------------------------------------------------
# Index build + cache
# -----------------------------------------------------------------------------
def _load_or_build_index(
=======

def _load_or_build_decomp_index(
>>>>>>> Stashed changes
    *,
    oid: str,
    model_id: str,
    max_chars: int,
    batch_size: int,
    use_cache: bool,
    rebuild: bool,
<<<<<<< Updated upstream
    model: "SentenceTransformer",
    counts: Dict[str, Dict[str, Any]],
    timing: bool,
    progress: bool,
    progress_every: int,
) -> Tuple[Optional[Dict[str, Any]], Optional[Dict[str, Any]]]:
    t0 = time.perf_counter()
    key = _cache_key(oid, model_id, max_chars)
=======
    model: Optional[Any],
    counts: Dict[str, Dict[str, Any]],
) -> Optional[Dict[str, Any]]:
    key = _decomp_cache_key(oid, model_id, max_chars, model is not None)

    if use_cache and (not rebuild) and api.local_exists(NAME, key):
        try:
            blob = api.local_retrieve(NAME, key) or {}
            idx = blob.get(oid)
            if idx and ("codes" in idx) and ((model is None) or ("emb" in idx)):
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
    addrs: List[str] = []
    names: List[str] = []
    texts: List[str] = []
    previews: List[str] = []
    codes: List[str] = []

    for addr, finfo in f_list:
        text = _normalize_decomp_blob(_safe_decompile(oid, addr), max_chars=max_chars)
        if not text:
            continue
        addrs.append(str(addr))
        names.append(_extract_func_name(finfo, addr))
        previews.append(_first_preview_line(text))
        texts.append(text)
        codes.append(text)

    counts[oid] = {"cache": "miss", "num_functions": len(f_list), "num_indexed": len(texts)}
    if not texts:
        return None

    idx = {
        "num_functions": len(f_list),
        "num_indexed": len(texts),
        "addrs": addrs,
        "names": names,
        "previews": previews,
        "codes": codes,
    }
    if model is not None:
        idx["emb"] = model.encode(
            texts,
            batch_size=batch_size,
            normalize_embeddings=True,
            show_progress_bar=False,
        ).astype(np.float32)
    if use_cache:
        try:
            api.local_store(NAME, key, {oid: idx})
        except Exception:
            logger.exception("Failed to cache index for oid=%s", oid)
    return idx


def _load_or_build_clap_index(
    *,
    oid: str,
    asm_model_id: str,
    max_instructions: int,
    batch_size: int,
    use_cache: bool,
    rebuild: bool,
    normalize: bool,
    encoders: "_ClapEncoders",
    counts: Dict[str, Dict[str, Any]],
) -> Optional[Dict[str, Any]]:
    key = _clap_cache_key(oid, asm_model_id, max_instructions, normalize)
>>>>>>> Stashed changes

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
            logger.exception("Failed to load cached CLAP index for oid=%s", oid)

    # list functions
    t_list0 = time.perf_counter()
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    blocks = api.get_field("ghidra_disasm", oid, "original_blocks") or {}
    f_list = list(_iter_functions(funcs))
<<<<<<< Updated upstream
    t_list = time.perf_counter() - t_list0

    if timing and progress:
        logger.info(
            "oid=%s list funcs done num_functions=%d list_funcs_s=%.3f",
            oid,
            len(f_list),
            t_list,
        )

=======
>>>>>>> Stashed changes
    addrs: List[str] = []
    names: List[str] = []
    previews: List[str] = []
    texts: List[str] = []

<<<<<<< Updated upstream
    decompile = _get_decompile_map(oid)

    # decompile loop
    num_decomp_calls = 0
    t_decomp0 = time.perf_counter()
    last_report_t = t_decomp0

    for addr, finfo in f_list:
        num_decomp_calls += 1
        func_name = _name_from_finfo(finfo)
        raw_text = ""
        if func_name:
            key = func_name if func_name in decompile else _resolve_decomp_key(decompile, func_name)
            if key is not None:
                raw_text = _decomp_text_from_blocks(decompile.get(key))
        text = _normalize_decomp_blob(raw_text, max_chars=max_chars)
        if text:
            addrs.append(str(addr))
            names.append(func_name)
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
=======
    for addr, finfo in f_list:
        asm = _function_assembly(finfo, blocks, max_instructions=max_instructions)
        if not asm:
            continue
        addrs.append(str(addr))
        names.append(_extract_func_name(finfo, addr))
        texts.append(asm)
        previews.append(_first_preview_line(asm))
>>>>>>> Stashed changes

    counts[oid] = {"cache": "miss", "num_functions": len(f_list), "num_indexed": len(texts)}
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

<<<<<<< Updated upstream
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

=======
    emb = _encode_clap_asm(encoders, texts, batch_size=batch_size, normalize=normalize)
>>>>>>> Stashed changes
    idx = {
        "num_functions": len(f_list),
        "num_indexed": len(texts),
        "addrs": addrs,
        "names": names,
        "previews": previews,
        "texts": texts,
        "emb": emb,
    }
<<<<<<< Updated upstream

    # store
    t_store = 0.0
=======
>>>>>>> Stashed changes
    if use_cache:
        t_store0 = time.perf_counter()
        try:
            api.local_store(NAME, key, {oid: idx})
        except Exception:
<<<<<<< Updated upstream
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


def _literal_matches(
    oid: str,
    idx: Optional[Dict[str, Any]],
    query: str,
    top_k: int,
) -> List[Dict[str, Any]]:
    """Return functions whose decompiled text contains query as a substring."""
    if not idx:
        return []
    texts = idx.get("texts") or []
    addrs = idx.get("addrs") or []
    names = idx.get("names") or []
    previews = idx.get("previews") or []
    q_lower = query.lower()
    matches: List[Dict[str, Any]] = []
    for i, text in enumerate(texts):
        if q_lower in (text or "").lower():
            matches.append({
                "oid": oid,
                "func_addr": addrs[i] if i < len(addrs) else None,
                "func_name": names[i] if i < len(names) else None,
                "score": 1.0,
                "preview": previews[i] if i < len(previews) else "",
                "match_type": "literal",
            })
    if top_k > 0:
        return matches[:top_k]
    return matches


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
=======
            logger.exception("Failed to cache CLAP index for oid=%s", oid)
    return idx


def _rank_single_prompt(
    idx: Dict[str, Any],
    oid: str,
    sims: np.ndarray,
    top_k: int,
    prompt: Optional[str] = None,
) -> List[Dict[str, Any]]:
    k_local = sims.shape[0] if top_k <= 0 else min(top_k, sims.shape[0])
    if k_local <= 0:
        return []
    loc = np.argpartition(-sims, k_local - 1)[:k_local]
    loc = loc[np.argsort(-sims[loc])]
    return [_candidate(idx, oid, int(i), float(sims[i]), prompt) for i in loc]


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
            idx,
            oid,
            i,
            code=code,
            similarity=1.0,
            search_mode="literal",
            include_full_code=include_full_code,
            preview_length=preview_length,
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
    for i in np.argsort(-sims):
        similarity = float(sims[i])
        if similarity < similarity_threshold:
            continue
        codes = idx.get("codes", [])
        code = codes[int(i)] if int(i) < len(codes) else ""
        results.append(_decomp_search_candidate(
            idx,
            oid,
            int(i),
            code=code,
            similarity=similarity,
            search_mode="semantic",
            include_full_code=include_full_code,
            preview_length=preview_length,
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
    result_code = code if include_full_code else preview
    return {
        "oid": oid,
        "function_addr": idx["addrs"][i],
        "function_name": idx["names"][i],
        "code": result_code,
        "score": similarity,
        "similarity": similarity,
        "search_mode": search_mode,
        "preview": None if include_full_code else preview,
    }


def _preview(code: str, preview_length: int) -> str:
    if preview_length <= 0:
        return ""
    return code[:preview_length] + "..." if len(code) > preview_length else code


def _candidate(
    idx: Dict[str, Any],
    oid: str,
    i: int,
    score: float,
    prompt: Optional[str] = None,
    prompt_index: Optional[int] = None,
) -> Dict[str, Any]:
    out = {
        "oid": oid,
        "function_addr": idx["addrs"][i],
        "function_name": idx["names"][i],
        "score": score,
        "preview": idx["previews"][i],
    }
    if prompt is not None:
        out["prompt"] = prompt
    if prompt_index is not None:
        out["prompt_index"] = prompt_index
    return out
>>>>>>> Stashed changes


def _iter_functions(funcs: Any):
    if isinstance(funcs, dict):
        for addr, finfo in funcs.items():
            if addr == "meta":
                continue
            yield addr, finfo
    elif isinstance(funcs, (list, tuple)):
        for addr in funcs:
            yield addr, None

<<<<<<< Updated upstream

def _name_from_finfo(finfo: Any) -> Optional[str]:
    """Extract a function name from a ghidra_disasm functions-dict entry."""
    if isinstance(finfo, dict):
        n = finfo.get("name")
        return n if isinstance(n, str) and n else None
    if isinstance(finfo, str) and finfo:
        return finfo
    return None


def _get_decompile_map(oid: str) -> Dict[str, Any]:
    """Fetch the whole ghidra_decmap once and return its {func_name: blocks} dict.

    Done once per binary instead of once per function — see the build loop.
    """
    decmap = api.retrieve("ghidra_decmap", [oid], {"org_by_func": True})
    if not isinstance(decmap, dict) or not decmap:
        return {}
    inner = decmap.get(oid)
    dm = inner if isinstance(inner, dict) else decmap
    decompile = dm.get("decompile") if isinstance(dm, dict) else None
    return decompile if isinstance(decompile, dict) else {}


def _resolve_decomp_key(decompile: Dict[str, Any], want: str) -> Optional[str]:
    """Resolve a function name to a decompile key, tolerating C++ '::' qualifiers."""
    if want in decompile:
        return want
    want_short = want.split("::")[-1]
    cands = [
        k for k in decompile
        if isinstance(k, str) and k.split("::")[-1] == want_short
    ]
    return cands[0] if len(cands) == 1 else None


def _decomp_text_from_blocks(func_blocks: Any) -> str:
    """Reconstruct decompiled text from one function's ghidra_decmap blocks.

    Mirrors function_decomp.retrieve_function_decomp_text so indexed text is
    identical, but operates on an already-fetched block dict (no per-call I/O).
    """
    if not isinstance(func_blocks, dict):
        return ""
    decomp_map: Dict[int, str] = {}
    saw_any_tagged = False
    untagged_fallback: List[str] = []
    for _block_id, block in func_blocks.items():
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
                ln = int(left.strip())
                decomp_map.setdefault(ln, right.rstrip("\r\n"))
                saw_any_tagged = True
                continue
            except Exception:
                pass
            untagged_fallback.append(raw.rstrip("\r\n"))
    if saw_any_tagged and decomp_map:
        return "\n".join(decomp_map[ln] for ln in sorted(decomp_map))
    if untagged_fallback:
        return "\n".join(untagged_fallback)
    return ""
=======

def _safe_decompile(oid: str, addr: Any) -> Any:
    try:
        res = api.retrieve("function_decomp", [oid], {"function_addr": str(addr)})
        return res.get(oid, res) if isinstance(res, dict) else res
    except Exception:
        logger.debug("Decompile failed oid=%s addr=%s", oid, addr, exc_info=True)
        return None


def _function_assembly(finfo: Any, blocks: Dict[Any, Any], max_instructions: int) -> str:
    lines: List[str] = []
    for block_addr in _block_addrs(finfo):
        block = blocks.get(block_addr) or blocks.get(str(block_addr))
        if not isinstance(block, dict):
            continue
        for member in block.get("members", []) or []:
            if not isinstance(member, (list, tuple)) or len(member) < 2:
                continue
            text = str(member[1]).strip()
            if text:
                lines.append(text)
            if max_instructions > 0 and len(lines) >= max_instructions:
                return "\n".join(lines)
    return "\n".join(lines)


def _block_addrs(finfo: Any) -> Iterable[Any]:
    if isinstance(finfo, dict):
        return finfo.get("blocks", []) or []
    return []


def _extract_func_name(finfo: Any, addr: Any) -> str:
    if isinstance(finfo, dict):
        for key in ("name", "function_name", "symbol", "label"):
            value = finfo.get(key)
            if isinstance(value, str) and value.strip():
                return value.strip()
    if isinstance(finfo, str) and finfo.strip():
        return finfo.strip()
    return f"sub_{addr}"
>>>>>>> Stashed changes


def _first_preview_line(text: str) -> str:
    for line in text.splitlines():
        line = line.strip()
        if line:
            return line[:200]
    return ""

<<<<<<< Updated upstream
=======

def _load_prompts(opts: dict) -> List[str]:
    query = _load_text_option(opts, "query", "query_path")
    if query:
        return [query]

    raw = _load_text_option(opts, "prompts", "prompts_path")
    prompts = []
    for line in raw.splitlines():
        line = line.strip()
        if line:
            prompts.append(line)
    return prompts


def _load_text_option(opts: dict, value_key: str, path_key: str) -> str:
    text = (opts.get(value_key) or "").strip()
    path = (opts.get(path_key) or "").strip()
    if (not text) and path:
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as f:
                text = f.read().strip()
        except OSError:
            return ""
    return text


def _result_limit(opts: dict) -> int:
    limit = int(opts.get("limit", 0) or 0)
    if limit > 0:
        return limit
    return int(opts.get("top_k", 10) or 10)

>>>>>>> Stashed changes

def _normalize_decomp_blob(f_decomp: Any, max_chars: int) -> str:
    if not f_decomp:
        return ""
    if isinstance(f_decomp, list):
        text = "\n".join([x for x in f_decomp if isinstance(x, str)]).strip()
    elif isinstance(f_decomp, str):
        text = f_decomp.strip()
    else:
<<<<<<< Updated upstream
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
=======
        text = str(f_decomp).strip()
    return text[:max_chars] if (max_chars and len(text) > max_chars) else text


def _decomp_cache_key(oid: str, model_id: str, max_chars: int, include_embeddings: bool) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", f"decomp_v2_{oid}_{model_id}_{max_chars}_{include_embeddings}")


def _clap_cache_key(oid: str, asm_model_id: str, max_instructions: int, normalize: bool) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", f"clap_asm_{oid}_{asm_model_id}_{max_instructions}_{normalize}")


def _softmax(x: np.ndarray, axis: int) -> np.ndarray:
    shifted = x - np.max(x, axis=axis, keepdims=True)
    exp = np.exp(shifted)
    return exp / np.sum(exp, axis=axis, keepdims=True)


_SENTENCE_MODEL: Optional[Any] = None
_SENTENCE_MODEL_ID: Optional[str] = None


def _get_sentence_model(model_id: str) -> Any:
    global _SENTENCE_MODEL, _SENTENCE_MODEL_ID
    if _SENTENCE_MODEL is None or _SENTENCE_MODEL_ID != model_id:
        try:
            from sentence_transformers import SentenceTransformer
        except ImportError as err:
            raise ImportError("query_function backend='decomp_minilm' requires sentence-transformers.") from err
        _SENTENCE_MODEL = SentenceTransformer(model_id)
        _SENTENCE_MODEL_ID = model_id
    return _SENTENCE_MODEL


class _ClapEncoders:
    def __init__(self, asm_tokenizer: Any, asm_model: Any, text_tokenizer: Any, text_model: Any, torch: Any, device: Any):
        self.asm_tokenizer = asm_tokenizer
        self.asm_model = asm_model
        self.text_tokenizer = text_tokenizer
        self.text_model = text_model
        self.torch = torch
        self.device = device


_CLAP_ENCODERS: Optional[_ClapEncoders] = None
_CLAP_ENCODER_KEY: Optional[Tuple[str, str, str]] = None


def _get_clap_encoders(*, asm_model_id: str, text_model_id: str, device: str) -> _ClapEncoders:
    global _CLAP_ENCODERS, _CLAP_ENCODER_KEY
    key = (asm_model_id, text_model_id, device)
    if _CLAP_ENCODERS is not None and _CLAP_ENCODER_KEY == key:
        return _CLAP_ENCODERS

    try:
        import torch
        from transformers import AutoModel, AutoTokenizer
    except ImportError as err:
        raise ImportError("query_function backend='clap_asm' requires torch and transformers.") from err

    actual_device = torch.device("cuda" if device == "auto" and torch.cuda.is_available() else "cpu")
    if device and device != "auto":
        actual_device = torch.device(device)

    asm_tokenizer = AutoTokenizer.from_pretrained(asm_model_id, trust_remote_code=True)
    text_tokenizer = AutoTokenizer.from_pretrained(text_model_id, trust_remote_code=True)
    asm_model = AutoModel.from_pretrained(asm_model_id, trust_remote_code=True).to(actual_device)
    text_model = AutoModel.from_pretrained(text_model_id, trust_remote_code=True).to(actual_device)
    asm_model.eval()
    text_model.eval()

    _CLAP_ENCODERS = _ClapEncoders(asm_tokenizer, asm_model, text_tokenizer, text_model, torch, actual_device)
    _CLAP_ENCODER_KEY = key
    return _CLAP_ENCODERS


def _encode_clap_asm(encoders: _ClapEncoders, texts: Sequence[str], batch_size: int, normalize: bool) -> np.ndarray:
    return _encode_clap(encoders, encoders.asm_tokenizer, encoders.asm_model, texts, batch_size, normalize)


def _encode_clap_texts(encoders: _ClapEncoders, texts: Sequence[str], batch_size: int, normalize: bool) -> np.ndarray:
    return _encode_clap(encoders, encoders.text_tokenizer, encoders.text_model, texts, batch_size, normalize)


def _encode_clap(
    encoders: _ClapEncoders,
    tokenizer: Any,
    model: Any,
    texts: Sequence[str],
    batch_size: int,
    normalize: bool,
) -> np.ndarray:
    batches: List[np.ndarray] = []
    torch = encoders.torch
    with torch.no_grad():
        for start in range(0, len(texts), batch_size):
            batch = list(texts[start:start + batch_size])
            inputs = tokenizer(batch, padding=True, truncation=True, return_tensors="pt")
            inputs = {key: value.to(encoders.device) for key, value in inputs.items()}
            output = model(**inputs)
            emb = _clap_output_embedding(output, inputs, torch)
            if normalize:
                emb = torch.nn.functional.normalize(emb, p=2, dim=1)
            batches.append(emb.detach().cpu().numpy().astype(np.float32))
    return np.vstack(batches) if batches else np.empty((0, 0), dtype=np.float32)


def _clap_output_embedding(output: Any, inputs: Dict[str, Any], torch: Any) -> Any:
    emb = getattr(output, "last_hidden_state", None)
    if emb is None and isinstance(output, (tuple, list)) and output:
        emb = output[0]
    if emb is None:
        raise ValueError("CLAP model output did not include last_hidden_state")
    if len(emb.shape) == 2:
        return emb

    mask = inputs.get("attention_mask")
    if mask is None:
        return emb.mean(dim=1)
    mask = mask.unsqueeze(-1).expand(emb.size()).float()
    return torch.sum(emb * mask, dim=1) / torch.clamp(mask.sum(dim=1), min=1e-9)
>>>>>>> Stashed changes
