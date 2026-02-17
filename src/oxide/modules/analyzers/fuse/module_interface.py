DESC = "Strings-only file retrieval using auto-calibrated IDF evidence packing (+ optional BM25-confidence gate)"
NAME = "fuse"

import hashlib
import json
import math
import re
import logging
from collections import Counter
from typing import List, Dict, Tuple, Any, Optional

import numpy as np
from transformers import AutoTokenizer

from oxide.core import api

logger = logging.getLogger(NAME)

opts_doc = {
    "prompt": {"type": str, "mangle": False, "default": ""},
    "prompt_path": {"type": str, "mangle": False, "default": ""},
    "top_k": {"type": int, "mangle": False, "default": 50},
    "string_emb_batch_size": {"type": int, "mangle": False, "default": 128},
    "debug_select": {"type": bool, "mangle": False, "default": False},
    "pack_budget_tokens": {"type": int, "mangle": False, "default": 0},
    # Canonical FUSE behavior includes a BM25 confidence gate.
    # These options are for ablation experiments only.
    "ablate_no_gate": {"type": bool, "mangle": False, "default": False},
    "ablate_bm25_only": {"type": bool, "mangle": False, "default": False},
    "ablate_debug": {"type": bool, "mangle": False, "default": False},
}

# -------------------------------------------------------------
# Model setup
# -------------------------------------------------------------
MODEL_ID = "sentence-transformers/all-MiniLM-L6-v2"
# Bump to invalidate any localstore caches that depend on packed-doc behavior.
PACKED_DOC_CACHE_VERSION = 1

# Allow alnum tokens; keep this conservative but not letters-only
TERM = re.compile(r"[a-z][a-z0-9]{2,}", re.IGNORECASE)

def _infer_model_token_budget(tokenizer: Any, model: Any, default: int = 512) -> int:
    # HuggingFace tokenizers sometimes use a huge sentinel for "infinite" max length.
    tok_limit = getattr(tokenizer, "model_max_length", None)
    try:
        tok_limit_i = int(tok_limit) if tok_limit is not None else int(default)
    except Exception:
        tok_limit_i = int(default)
    if tok_limit_i <= 0 or tok_limit_i > 100000:
        tok_limit_i = int(default)

    mdl_limit = getattr(model, "max_seq_length", None)
    try:
        mdl_limit_i = int(mdl_limit) if mdl_limit is not None else 0
    except Exception:
        mdl_limit_i = 0

    if mdl_limit_i > 0:
        return int(min(tok_limit_i, mdl_limit_i))
    return int(tok_limit_i)


_MODEL_BUNDLE: Optional[Tuple["SentenceTransformer", Any, int]] = None


def _get_model() -> Tuple["SentenceTransformer", Any, int]:
    from sentence_transformers import SentenceTransformer

    global _MODEL_BUNDLE
    if _MODEL_BUNDLE is not None:
        return _MODEL_BUNDLE

    tok = AutoTokenizer.from_pretrained(MODEL_ID)
    mdl = SentenceTransformer(MODEL_ID)
    budget = _infer_model_token_budget(tok, mdl, default=512)
    _MODEL_BUNDLE = (mdl, tok, budget)
    return _MODEL_BUNDLE


def documentation() -> Dict[str, Any]:
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": True,
        "set": False,
        "atomic": True
    }


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    prompt = (opts.get("prompt") or "").strip()
    prompt_path = (opts.get("prompt_path") or "").strip()

    if not prompt and not prompt_path:
        return {"error": "Provide a prompt via 'prompt' or 'prompt_path'."}

    if not prompt and prompt_path:
        try:
            with open(prompt_path, "r", encoding="utf-8") as fp:
                prompt = fp.read().strip()
        except OSError as e:
            return {"error": f"Failed to read prompt_path: {e}"}

    top_k = int(opts.get("top_k", 50))
    string_emb_batch_size = int(opts.get("string_emb_batch_size", 128) or 128)
    debug_select = bool(opts.get("debug_select", False))
    pack_budget_tokens = int(opts.get("pack_budget_tokens", 0) or 0)

    # Canonical behavior: confidence-gated BM25 override is ON by default.
    # Ablations:
    # - ablate_no_gate: keep dense ranking (no BM25 override)
    # - ablate_bm25_only: ignore dense ranking and return BM25 ranking
    # Backward compat:
    # - hybrid_enable=False means ablate_no_gate=True
    # - hybrid_debug maps to ablate_debug
    ablate_no_gate = bool(opts.get("ablate_no_gate", False))
    ablate_bm25_only = bool(opts.get("ablate_bm25_only", False))
    ablate_debug = bool(opts.get("ablate_debug", False))

    if "hybrid_enable" in opts and "ablate_no_gate" not in opts:
        ablate_no_gate = not bool(opts.get("hybrid_enable", True))
    if "hybrid_debug" in opts and "ablate_debug" not in opts:
        ablate_debug = bool(opts.get("hybrid_debug", False))

    return search_prompt(
        oid_list,
        prompt,
        top_k=top_k,
        string_emb_batch_size=string_emb_batch_size,
        debug_select=debug_select,
        pack_budget_tokens=pack_budget_tokens,
        ablate_no_gate=ablate_no_gate,
        ablate_bm25_only=ablate_bm25_only,
        ablate_debug=ablate_debug,
    )


# -------------------------------------------------------------
# Embedding & Search
# -------------------------------------------------------------
def _cache_key(
    oids: List[str],
    config: Dict[str, Any],
) -> str:
    # Stable key across runs; includes model, selector config, and exact candidate set.
    cfg_blob = json.dumps(config, sort_keys=True, separators=(",", ":")).encode("utf-8")
    cfg_hash = hashlib.sha256(cfg_blob).hexdigest()[:12]

    h = hashlib.sha256()
    for oid in sorted(oids):
        h.update(oid.encode("utf-8"))
        h.update(b"\n")
    model_key = re.sub(r"[\\\\/]", "_", str(MODEL_ID))
    return (
        f"{model_key}|str_select=idf_pack_auto|cfg={cfg_hash}|"
        f"n={len(oids)}|{h.hexdigest()[:16]}"
    )


def build_embedding_matrix(
    oids: List[str],
    string_emb_batch_size: int = 128,
    debug_select: bool = False,
    debug_out: Optional[Dict[str, Any]] = None,
    pack_budget_tokens: int = 0,
) -> Tuple[np.ndarray, List[str]]:
    """
    Generate fused embedding matrix for the provided OIDs.
    Returns (matrix, ordered_oids).
    """
    model, tokenizer, max_tokens = _get_model()
    eps = 1e-8
    if string_emb_batch_size <= 0:
        string_emb_batch_size = 128

    ordered = list(oids)
    tokens_map = {oid: extract_tokens(oid) for oid in ordered}

    str_docs = {k: v["str"] for k, v in tokens_map.items()}

    pack_cfg: Dict[str, float] = {
        "noise_threshold": 0.70,
        "max_words": 48.0,
        "min_terms": 2.0,
        "redundancy_threshold": 0.80,
        "prune_keep_quantile": 0.75,
        "prune_min_keep": 8.0,
    }
    pack_cfg.update(derive_idf_pack_auto_params(str_docs))

    effective_budget = max_tokens
    if pack_budget_tokens > 0:
        # Do not exceed model tokenization budget; larger values would be truncated anyway.
        effective_budget = max(1, min(max_tokens, int(pack_budget_tokens)))

    str_term_idf = compute_term_idf_from_strings(
        str_docs,
        noise_threshold=float(pack_cfg["noise_threshold"]),
        max_words=int(pack_cfg["max_words"]),
        min_terms=int(pack_cfg["min_terms"]),
    )

    dim = model.get_sentence_embedding_dimension()
    vectors: List[np.ndarray] = []
    if debug_select and debug_out is not None:
        debug_out.setdefault("string_select_mode", "idf_pack_auto")
        debug_out.setdefault("string_counts", [])
        debug_out["idf_pack_params"] = dict(pack_cfg)
        debug_out["effective_pack_budget_tokens"] = int(effective_budget)

    for oid in ordered:
        strs = select_strings_by_idf_pack(
            tokens_map[oid]["str"],
            budget=effective_budget,
            tokenizer=tokenizer,
            term_idf=str_term_idf,
            redundancy_threshold=float(pack_cfg["redundancy_threshold"]),
            noise_threshold=float(pack_cfg["noise_threshold"]),
            max_words=int(pack_cfg["max_words"]),
            min_terms=int(pack_cfg["min_terms"]),
        )
        str_doc = _truncate_text_to_budget(
            " ".join(strs).strip(),
            tokenizer=tokenizer,
            budget=effective_budget,
        )

        # Encode empty docs safely
        if not str_doc:
            str_emb = np.zeros(dim, dtype=np.float32)
        else:
            str_emb = model.encode(str_doc, normalize_embeddings=True).astype(np.float32)
        vec = str_emb

        if debug_select and debug_out is not None:
            debug_out["string_counts"].append(len(strs))

        norm = float(np.linalg.norm(vec))
        if norm > eps:
            vec = vec / norm
        vectors.append(vec.astype(np.float32))

    return np.vstack(vectors).astype("float32"), ordered


def search_prompt(
    oids: List[str],
    prompt: str,
    top_k: int = 50,
    string_emb_batch_size: int = 128,
    debug_select: bool = False,
    pack_budget_tokens: int = 0,
    ablate_no_gate: bool = False,
    ablate_bm25_only: bool = False,
    ablate_debug: bool = False,
) -> Dict[str, Any]:
    """Search prompt over candidate OIDs; return ranked results."""
    model, _, _ = _get_model()
    debug_needed = bool(debug_select or ablate_debug)

    exes = filter_executables(oids)
    if not exes:
        return {"prompt": prompt, "results": {"best_match": None, "candidates": []}}

    q = model.encode(prompt, normalize_embeddings=True).astype("float32")
    cache_cfg: Dict[str, Any] = {
        "pack_budget_tokens": int(pack_budget_tokens),
        "cache_version": int(PACKED_DOC_CACHE_VERSION),
    }
    key = _cache_key(exes, cache_cfg)

    cached = api.local_retrieve(NAME, key) if api.local_exists(NAME, key) else None
    if cached and "oids" in cached and "emb" in cached and cached["oids"] == exes:
        emb_mat = cached["emb"]
        debug_out = {"cache_hit": True, "selection_config": cache_cfg} if debug_needed else None
    else:
        debug_out = {"cache_hit": False, "selection_config": cache_cfg} if debug_needed else None
        emb_mat, ordered = build_embedding_matrix(
            exes,
            string_emb_batch_size=string_emb_batch_size,
            debug_select=debug_select,
            debug_out=debug_out,
            pack_budget_tokens=pack_budget_tokens,
        )
        api.local_store(NAME, key, {"oids": ordered, "emb": emb_mat})
    sims = emb_mat.dot(q)

    idxs_all = np.argsort(-sims)
    idxs = idxs_all
    if top_k > 0:
        idxs = idxs[:top_k]

    def fmt(i: int) -> Dict[str, Any]:
        oid = exes[i]
        return {"oid": oid, "names": get_names(oid), "score": float(sims[i])}

    ranked = [fmt(i) for i in idxs]
    bm25_top_oid: Optional[str] = None
    override_applied = False
    gate_stats: Dict[str, Any] = {}

    # Canonical FUSE behavior uses a BM25 confidence gate to optionally override dense top-1.
    # Ablations can disable the gate or return BM25-only results.
    gate_enabled = not bool(ablate_no_gate) and not bool(ablate_bm25_only)
    if gate_enabled or ablate_bm25_only or debug_needed:
        raw_docs = _build_raw_string_docs(exes)
        query_terms = _query_terms_for_lexical(prompt)
        bm25_ranked, bm25_scores, bm25_meta = _bm25_rank_with_scores(raw_docs, query_terms)
        bm25_top_oid = bm25_ranked[0] if bm25_ranked else None

        docs_term_sets: Dict[str, set] = {}
        for oid, doc_text in raw_docs.items():
            terms = [t for t in doc_text.split() if TERM.fullmatch(t)]
            docs_term_sets[oid] = set(terms)
        term_idf = _term_idf_for_terms(set(query_terms), docs_term_sets)

        bm25_score_sorted = [float(bm25_scores.get(oid, 0.0)) for oid in bm25_ranked]
        bm25_top_terms = docs_term_sets.get(str(bm25_top_oid), set()) if bm25_top_oid else set()
        bm25_conf = _bm25_confidence(
            bm25_score_sorted,
            query_terms=query_terms,
            top_doc_terms=bm25_top_terms,
            term_idf=term_idf,
        )
        dense_sorted = [float(sims[i]) for i in idxs_all]
        fuse_conf = _dense_confidence(dense_sorted)
        should_override = _should_override_with_bm25(
            bm25_stats=bm25_conf,
            fuse_stats=fuse_conf,
        )

        if gate_enabled and should_override and bm25_top_oid:
            # Preserve FUSE ordering except for promoting BM25's top candidate.
            promoted = _apply_top1_override(ranked, bm25_top_oid)
            if promoted and promoted[0].get("oid") == bm25_top_oid:
                ranked = promoted
                override_applied = True
            else:
                oid_to_idx = {oid: i for i, oid in enumerate(exes)}
                top_idx = oid_to_idx.get(bm25_top_oid)
                if top_idx is not None:
                    bm25_top_item = fmt(top_idx)
                    keep = [r for r in ranked if r.get("oid") != bm25_top_oid]
                    ranked = [bm25_top_item] + keep
                    if top_k > 0:
                        ranked = ranked[:top_k]
                    override_applied = True

        try:
            from rank_bm25 import BM25Okapi as _BM25Okapi  # type: ignore

            bm25_supported = True
        except Exception:
            bm25_supported = False

        gate_stats = {
            "enabled": bool(gate_enabled),
            "bm25_backend": str(bm25_meta.get("backend", "unknown")),
            "query_term_count": len(query_terms),
            "bm25_top_oid": bm25_top_oid,
            "fuse_top_oid": ranked[0].get("oid") if ranked else None,
            "bm25_confidence": bm25_conf,
            "fuse_confidence": fuse_conf,
            "decision_rule": "bm25_conf > fuse_conf",
            "override_applied": bool(override_applied),
            "bm25_supported": bool(bm25_supported),
            "ablate_no_gate": bool(ablate_no_gate),
            "ablate_bm25_only": bool(ablate_bm25_only),
        }
        if "fallback_reason" in bm25_meta:
            gate_stats["fallback_reason"] = str(bm25_meta["fallback_reason"])

        if ablate_bm25_only:
            oid_to_idx = {oid: i for i, oid in enumerate(exes)}

            def fmt_bm25(oid: str) -> Dict[str, Any]:
                dense_i = oid_to_idx.get(oid)
                dense_score = float(sims[dense_i]) if dense_i is not None else None
                return {
                    "oid": oid,
                    "names": get_names(oid),
                    "score": float(bm25_scores.get(oid, 0.0)),
                    "bm25_score": float(bm25_scores.get(oid, 0.0)),
                    "dense_score": dense_score,
                }

            ranked = [fmt_bm25(oid) for oid in bm25_ranked]
            if top_k > 0:
                ranked = ranked[:top_k]

    best = ranked[0] if ranked else None

    resp = {"prompt": prompt, "results": {"best_match": best, "candidates": ranked}}
    if debug_needed:
        if debug_out is None:
            debug_out = {}
        if gate_enabled or ablate_debug or ablate_bm25_only:
            # New name:
            debug_out["confidence_gate"] = gate_stats or {
                "enabled": bool(gate_enabled),
                "override_applied": False,
            }
            # Backward-compat alias:
            debug_out["hybrid"] = debug_out["confidence_gate"]
        resp["debug_select"] = debug_out or {}
    return resp


def _clamp01(v: float) -> float:
    return float(min(1.0, max(0.0, float(v))))


def _query_terms_for_lexical(prompt: str) -> List[str]:
    norm = normalize(prompt or "")
    if not norm:
        return []
    return [t for t in norm.split() if TERM.fullmatch(t)]


def _build_raw_string_docs(exes: List[str]) -> Dict[str, str]:
    docs: Dict[str, str] = {}
    for oid in exes:
        raw_strs = api.get_field("strings", oid, oid) or {}
        parts: List[str] = []
        for s in raw_strs.values():
            if not isinstance(s, str):
                continue
            if len(s) >= 200:
                continue
            ns = normalize(s)
            if TERM.search(ns):
                parts.append(ns)
        docs[oid] = " ".join(parts).strip()
    return docs


def _bm25_lite_scores(
    query_terms: List[str],
    doc_terms_by_oid: Dict[str, List[str]],
) -> Dict[str, float]:
    N = max(1, len(doc_terms_by_oid))
    avgdl = (
        sum(len(terms) for terms in doc_terms_by_oid.values()) / float(N)
        if doc_terms_by_oid
        else 1.0
    )
    avgdl = max(avgdl, 1e-8)

    df = Counter()
    for terms in doc_terms_by_oid.values():
        for t in set(terms):
            df[t] += 1

    q_tf = Counter(query_terms)
    k1 = 1.2
    b = 0.75
    out: Dict[str, float] = {}
    for oid, terms in doc_terms_by_oid.items():
        tf = Counter(terms)
        dl = max(len(terms), 1)
        score = 0.0
        for t, qcnt in q_tf.items():
            f = float(tf.get(t, 0))
            if f <= 0:
                continue
            term_df = float(df.get(t, 0))
            idf = math.log((N - term_df + 0.5) / (term_df + 0.5) + 1.0)
            denom = f + k1 * (1.0 - b + b * (float(dl) / avgdl))
            score += float(qcnt) * idf * ((f * (k1 + 1.0)) / max(denom, 1e-8))
        out[oid] = float(score)
    return out


def _bm25_rank_with_scores(
    docs: Dict[str, str],
    query_terms: List[str],
) -> Tuple[List[str], Dict[str, float], Dict[str, Any]]:
    try:
        from rank_bm25 import BM25Okapi  # type: ignore
    except Exception:
        BM25Okapi = None

    ordered_oids = list(docs.keys())
    doc_terms_by_oid: Dict[str, List[str]] = {
        oid: [t for t in str(docs.get(oid, "")).split() if TERM.fullmatch(t)]
        for oid in ordered_oids
    }

    if not ordered_oids:
        return [], {}, {"backend": "none"}

    query_terms = [t for t in query_terms if TERM.fullmatch(t)]
    if not query_terms:
        scores = {oid: 0.0 for oid in ordered_oids}
        ranked = sorted(ordered_oids)
        return ranked, scores, {"backend": "no_query_terms"}

    if BM25Okapi is not None:
        try:
            corpus = [doc_terms_by_oid[oid] for oid in ordered_oids]
            bm25 = BM25Okapi(corpus)
            raw_scores = bm25.get_scores(query_terms)
            scores = {
                oid: float(raw_scores[i]) for i, oid in enumerate(ordered_oids)
            }
            ranked = sorted(ordered_oids, key=lambda oid: (-scores[oid], oid))
            return ranked, scores, {"backend": "rank_bm25"}
        except Exception as e:
            lite = _bm25_lite_scores(query_terms, doc_terms_by_oid)
            ranked = sorted(ordered_oids, key=lambda oid: (-lite.get(oid, 0.0), oid))
            return ranked, lite, {
                "backend": "bm25_lite",
                "fallback_reason": f"rank_bm25_failed:{e}",
            }

    lite = _bm25_lite_scores(query_terms, doc_terms_by_oid)
    ranked = sorted(ordered_oids, key=lambda oid: (-lite.get(oid, 0.0), oid))
    return ranked, lite, {"backend": "bm25_lite"}


def _term_idf_for_terms(
    query_terms: set,
    docs_term_sets: Dict[str, set],
) -> Dict[str, float]:
    if not query_terms:
        return {}
    N = max(1, len(docs_term_sets))
    out: Dict[str, float] = {}
    for t in query_terms:
        df = sum(1 for s in docs_term_sets.values() if t in s)
        out[t] = math.log((N + 1.0) / (float(df) + 1.0)) + 1.0
    return out


def _plain_coverage(query_terms: List[str], top_doc_terms: set) -> float:
    q = set(query_terms)
    if not q:
        return 0.0
    return _clamp01(float(sum(1 for t in q if t in top_doc_terms)) / float(len(q)))


def _idf_coverage(
    query_terms: List[str],
    top_doc_terms: set,
    term_idf: Dict[str, float],
) -> float:
    q = set(query_terms)
    if not q:
        return 0.0
    den = float(sum(float(term_idf.get(t, 1.0)) for t in q))
    if den <= 0.0:
        return 0.0
    num = float(sum(float(term_idf.get(t, 1.0)) for t in q if t in top_doc_terms))
    return _clamp01(num / den)


def _normalized_margin(s1: float, s2: float) -> float:
    gap = max(float(s1) - float(s2), 0.0)
    denom = abs(float(s1)) + abs(float(s2)) + 1e-8
    return _clamp01(gap / denom)


def _robust_spread(vals: List[float]) -> float:
    if not vals:
        return 0.0
    arr = np.asarray(vals, dtype=np.float32)
    if arr.size == 0:
        return 0.0
    med = float(np.median(arr))
    mad = float(np.median(np.abs(arr - med)))
    if mad > 1e-8:
        return float(1.4826 * mad)
    q75 = float(np.quantile(arr, 0.75))
    q25 = float(np.quantile(arr, 0.25))
    iqr = q75 - q25
    if iqr > 1e-8:
        return float(iqr / 1.349)
    std = float(np.std(arr))
    return std if std > 0.0 else 0.0


def _distribution_confidence(sorted_scores: List[float]) -> Dict[str, float]:
    if not sorted_scores:
        return {"top1": 0.0, "top2": 0.0, "gap": 0.0, "spread": 0.0, "conf": 0.0}
    s1 = float(sorted_scores[0])
    s2 = float(sorted_scores[1]) if len(sorted_scores) > 1 else s1
    gap = max(s1 - s2, 0.0)

    window = [float(x) for x in sorted_scores[: min(len(sorted_scores), 20)]]
    spread_input = window[1:] if len(window) > 1 else window
    spread = max(_robust_spread(spread_input), 1e-8)
    conf = _clamp01(gap / (gap + spread))
    return {
        "top1": s1,
        "top2": s2,
        "gap": float(gap),
        "spread": float(spread),
        "conf": float(conf),
    }


def _dense_confidence(sorted_sims: List[float]) -> Dict[str, float]:
    dist = _distribution_confidence(sorted_sims)
    return {
        "fuse_top1": float(dist["top1"]),
        "fuse_top2": float(dist["top2"]),
        "fuse_gap": float(dist["gap"]),
        "fuse_spread": float(dist["spread"]),
        "fuse_conf": float(dist["conf"]),
    }


def _bm25_confidence(
    scores_sorted: List[float],
    *,
    query_terms: List[str],
    top_doc_terms: set,
    term_idf: Dict[str, float],
) -> Dict[str, float]:
    dist = _distribution_confidence(scores_sorted)
    coverage = _plain_coverage(query_terms, top_doc_terms)
    idf_coverage = _idf_coverage(query_terms, top_doc_terms, term_idf)
    return {
        "bm25_top1": float(dist["top1"]),
        "bm25_top2": float(dist["top2"]),
        "bm25_gap": float(dist["gap"]),
        "bm25_spread": float(dist["spread"]),
        "bm25_coverage": float(coverage),
        "bm25_idf_coverage": float(idf_coverage),
        "bm25_conf": float(dist["conf"]),
    }


def _should_override_with_bm25(
    bm25_stats: Dict[str, float],
    fuse_stats: Dict[str, float],
) -> bool:
    bm25_conf = float(bm25_stats.get("bm25_conf", 0.0))
    fuse_conf = float(fuse_stats.get("fuse_conf", 0.0))
    return bm25_conf > fuse_conf


def _apply_top1_override(
    fuse_ranked: List[Dict[str, Any]],
    bm25_top_oid: Optional[str],
) -> List[Dict[str, Any]]:
    if not fuse_ranked or not bm25_top_oid:
        return list(fuse_ranked)
    if str(fuse_ranked[0].get("oid", "")) == str(bm25_top_oid):
        return list(fuse_ranked)

    idx = next(
        (i for i, row in enumerate(fuse_ranked) if str(row.get("oid", "")) == str(bm25_top_oid)),
        None,
    )
    if idx is None:
        return list(fuse_ranked)
    top = fuse_ranked[idx]
    return [top] + [row for i, row in enumerate(fuse_ranked) if i != idx]


# -------------------------------------------------------------
# Utilities
# -------------------------------------------------------------
def normalize(text: str) -> str:
    from unicodedata import normalize as u_norm
    text = u_norm("NFC", text)
    text = text.replace("_", " ")
    text = re.sub(r"[^\w\s]", " ", text)
    return re.sub(r"\s+", " ", text).strip().lower()


def get_names(oid: str) -> List[str]:
    return list(api.get_names_from_oid(oid))


def separate_oids(oids: List[str]) -> Tuple[List[str], List[str]]:
    exes, others = [], []
    for oid in oids:
        cat = api.get_field("categorize", oid, oid)
        (exes if cat == "executable" else others).append(oid)
    return exes, others


def filter_executables(oids: List[str]) -> List[str]:
    """Filter out .so and .ko (keep only likely main executables)."""
    exes, _ = separate_oids(oids)
    filtered = []
    for oid in exes:
        names = get_names(oid)
        if not any(ext in name for name in names for ext in (".so", ".ko")):
            filtered.append(oid)
    return filtered


def extract_tokens(
    oid: str,
) -> Dict[str, List[str]]:
    """Extract normalized strings for retrieval."""
    raw_strs = api.get_field("strings", oid, oid) or {}
    strings: List[str] = []
    for s in raw_strs.values():
        if not isinstance(s, str):
            continue
        if len(s) >= 200:
            continue
        # keep whole strings (minimal change), but normalize whitespace/punct
        ns = normalize(s)
        if TERM.search(ns):
            strings.append(ns)

    return {"str": strings}


def _canon_string_for_pack(text: str) -> str:
    s = (text or "").lower().strip()
    if not s:
        return ""
    s = re.sub(r"\s+", " ", s).strip()
    return s


def _token_ids_for_text_quiet(tokenizer: Any, text: str) -> List[int]:
    """
    Tokenize without max-length warnings; caller enforces chunk/budget behavior.
    """
    if tokenizer is None:
        return []
    try:
        enc = tokenizer(
            text,
            add_special_tokens=False,
            truncation=False,
            return_attention_mask=False,
            return_token_type_ids=False,
            verbose=False,
        )
    except TypeError:
        # Some tokenizers do not support the `verbose` kwarg.
        try:
            enc = tokenizer(
                text,
                add_special_tokens=False,
                truncation=False,
                return_attention_mask=False,
                return_token_type_ids=False,
            )
        except Exception:
            return []
    except Exception:
        return []

    ids = enc.get("input_ids") if isinstance(enc, dict) else None
    if ids is None:
        return []
    if isinstance(ids, list) and ids and isinstance(ids[0], list):
        ids = ids[0]
    return list(ids) if isinstance(ids, list) else []


def _token_len_quiet(tokenizer: Any, text: str) -> int:
    """
    Best-effort token length.
    Falls back to tokenizer.tokenize() and then whitespace terms if ID extraction fails.
    """
    ids = _token_ids_for_text_quiet(tokenizer, text)
    if ids:
        return len(ids)
    if tokenizer is not None:
        try:
            toks = tokenizer.tokenize(text)
            if isinstance(toks, list) and toks:
                return len(toks)
        except Exception:
            pass
    s = normalize(text or "")
    if not s:
        return 0
    return max(1, len(s.split()))


def _truncate_text_to_budget(text: str, tokenizer: Any, budget: int) -> str:
    """
    Hard cap text length by tokenizer token budget to avoid model overlength input.
    """
    s = (text or "").strip()
    if not s or budget <= 0:
        return s
    ids = _token_ids_for_text_quiet(tokenizer, s)
    if not ids:
        return s
    if len(ids) <= budget:
        return s
    ids = ids[:budget]
    try:
        return str(
            tokenizer.decode(
                ids,
                skip_special_tokens=True,
                clean_up_tokenization_spaces=True,
            )
            or ""
        ).strip()
    except Exception:
        return s


def _terms_for_pack(text: str) -> List[str]:
    return [t for t in text.split() if TERM.fullmatch(t)]


def _is_capability_candidate(canon: str, terms: List[str]) -> bool:
    """
    Vocabulary-agnostic proxy for semantically meaningful strings.
    This avoids hardcoded benchmark terms.
    """
    if not canon or not terms:
        return False

    chars = [c for c in canon if not c.isspace()]
    if not chars:
        return False

    n = float(len(chars))
    n_alpha = sum(1 for c in chars if c.isalpha())
    n_digit = sum(1 for c in chars if c.isdigit())
    alpha_ratio = n_alpha / n
    digit_ratio = n_digit / n

    term_count = len(terms)
    unique_terms = len(set(terms))
    has_long_term = any(len(t) >= 4 for t in set(terms))

    return (
        unique_terms >= 2
        and has_long_term
        and alpha_ratio >= 0.50
        and digit_ratio <= 0.45
        and term_count <= 64
        and (unique_terms / max(term_count, 1)) >= 0.35
    )


def _extract_string_features(
    tokens: List[str],
    dedup: bool = True,
) -> List[Dict[str, Any]]:
    """
    Build per-string features used by IDF packing and auto-calibration.
    """
    out: List[Dict[str, Any]] = []
    seen = set()
    for raw in tokens:
        if not raw:
            continue
        canon = _canon_string_for_pack(raw)
        if not canon:
            continue
        if dedup and canon in seen:
            continue
        seen.add(canon)

        terms = _terms_for_pack(canon)
        chars = [c for c in canon if not c.isspace()]
        if not chars:
            continue

        n = float(len(chars))
        n_digit = sum(1 for c in chars if c.isdigit())
        n_alpha = sum(1 for c in chars if c.isalpha())
        n_other = len(chars) - n_digit - n_alpha
        noise_ratio = (n_digit + n_other) / n
        is_cap = _is_capability_candidate(canon, terms)

        out.append(
            {
                "raw": raw,
                "canon": canon,
                "terms": terms,
                "term_set": set(terms),
                "term_count": len(terms),
                "is_cap": is_cap,
                "noise_ratio": float(noise_ratio),
                "word_count": len(canon.split()),
            }
        )
    return out


def _is_noisy_candidate(
    feat: Dict[str, Any],
    *,
    noise_threshold: float = 0.70,
    max_words: int = 48,
    min_terms: int = 2,
) -> bool:
    canon = str(feat.get("canon") or "")
    if not canon:
        return True
    is_cap = bool(feat.get("is_cap", False))
    noise_ratio = float(feat.get("noise_ratio", 0.0))
    word_count = int(feat.get("word_count", 0))
    term_count = int(feat.get("term_count", 0))

    if noise_ratio > noise_threshold and not is_cap:
        return True
    if word_count > max_words and not is_cap:
        return True
    if term_count < min_terms and not is_cap:
        return True
    return False


def _prepare_string_candidates(
    tokens: List[str],
    *,
    noise_threshold: float = 0.70,
    max_words: int = 48,
    min_terms: int = 2,
    apply_noise_filter: bool = True,
) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    for feat in _extract_string_features(tokens, dedup=True):
        if apply_noise_filter:
            if _is_noisy_candidate(
                feat,
                noise_threshold=noise_threshold,
                max_words=max_words,
                min_terms=min_terms,
            ):
                continue
        out.append(feat)
    return out


def _quantile_clip(
    vals: List[float], q: float, lo: float, hi: float, default: float
) -> float:
    if not vals:
        return float(default)
    v = float(np.quantile(np.asarray(vals, dtype=np.float32), q))
    return float(min(max(v, lo), hi))


def derive_idf_pack_auto_params(docs: Dict[str, List[str]]) -> Dict[str, float]:
    """
    Derive robust pack parameters from current corpus distributions.
    This avoids manually tuning per-dataset values.
    """
    noise_vals: List[float] = []
    word_vals: List[float] = []
    term_vals: List[float] = []
    file_sizes: List[float] = []
    overlaps: List[float] = []

    for toks in docs.values():
        feats = _extract_string_features(toks, dedup=True)
        if not feats:
            continue
        file_sizes.append(float(len(feats)))

        for f in feats:
            noise_vals.append(float(f.get("noise_ratio", 0.0)))
            word_vals.append(float(f.get("word_count", 0)))
            term_vals.append(float(f.get("term_count", 0)))

        # Light-weight overlap sampling per file for redundancy threshold.
        sets = [f["term_set"] for f in feats if f.get("term_set")]
        limit = min(len(sets), 48)
        pair_budget = 256
        seen_pairs = 0
        for i in range(limit):
            for j in range(i + 1, limit):
                js = _jaccard(sets[i], sets[j])
                if js > 0.0:
                    overlaps.append(js)
                seen_pairs += 1
                if seen_pairs >= pair_budget:
                    break
            if seen_pairs >= pair_budget:
                break

    noise_threshold = _quantile_clip(
        noise_vals, q=0.85, lo=0.60, hi=0.92, default=0.70
    )
    max_words = int(
        round(_quantile_clip(word_vals, q=0.95, lo=16.0, hi=96.0, default=48.0))
    )
    min_terms = int(
        round(_quantile_clip(term_vals, q=0.10, lo=1.0, hi=3.0, default=2.0))
    )
    redundancy_threshold = _quantile_clip(
        overlaps, q=0.90, lo=0.65, hi=0.95, default=0.80
    )

    min_keep = int(
        round(_quantile_clip(file_sizes, q=0.15, lo=6.0, hi=16.0, default=8.0))
    )
    med_size = _quantile_clip(file_sizes, q=0.50, lo=8.0, hi=128.0, default=32.0)
    keep_quantile = 1.0 - (float(min_keep) / max(float(min_keep + 1), float(med_size)))
    keep_quantile = float(min(max(keep_quantile, 0.60), 0.85))

    return {
        "noise_threshold": noise_threshold,
        "max_words": float(max_words),
        "min_terms": float(min_terms),
        "redundancy_threshold": redundancy_threshold,
        "prune_keep_quantile": keep_quantile,
        "prune_min_keep": float(min_keep),
    }


def compute_term_idf_from_strings(
    docs: Dict[str, List[str]],
    *,
    noise_threshold: float = 0.70,
    max_words: int = 48,
    min_terms: int = 2,
    apply_noise_filter: bool = True,
    use_idf: bool = True,
) -> Dict[str, float]:
    df = Counter()
    N = max(1, len(docs))
    for toks in docs.values():
        cands = _prepare_string_candidates(
            toks,
            noise_threshold=noise_threshold,
            max_words=max_words,
            min_terms=min_terms,
            apply_noise_filter=apply_noise_filter,
        )
        seen_terms = set()
        for c in cands:
            seen_terms.update(c["term_set"])
        for t in seen_terms:
            df[t] += 1
    if not df and apply_noise_filter:
        # Fallback: if adaptive filters prune everything, recompute IDF without filtering.
        return compute_term_idf_from_strings(
            docs,
            noise_threshold=noise_threshold,
            max_words=max_words,
            min_terms=min_terms,
            apply_noise_filter=False,
            use_idf=use_idf,
        )
    if not use_idf:
        return {t: 1.0 for t in df.keys()}
    return {t: math.log((N + 1) / (cnt + 1)) + 1.0 for t, cnt in df.items()}


def _idf_mass(terms: List[str], term_idf: Dict[str, float]) -> float:
    if not terms:
        return 0.0
    return float(sum(term_idf.get(t, 0.0) for t in set(terms)))


def _jaccard(a: set, b: set) -> float:
    if not a and not b:
        return 0.0
    inter = len(a & b)
    union = len(a | b)
    return float(inter) / float(union) if union > 0 else 0.0


def _redundant(term_set: set, picked_sets: List[set], threshold: float = 0.80) -> bool:
    for s in picked_sets:
        if _jaccard(term_set, s) >= threshold:
            return True
    return False


def select_strings_by_idf_pack(
    tokens: List[str],
    budget: int,
    tokenizer: Any,
    term_idf: Dict[str, float],
    *,
    redundancy_threshold: float = 0.80,
    noise_threshold: float = 0.70,
    max_words: int = 48,
    min_terms: int = 2,
    apply_noise_filter: bool = True,
    apply_redundancy: bool = True,
) -> List[str]:
    """
    Evidence packing under token budget:
      - junk normalization/filtering
      - string-level IDF mass scoring
      - near-duplicate suppression
    """
    if budget <= 0:
        return []

    cands = _prepare_string_candidates(
        tokens,
        noise_threshold=noise_threshold,
        max_words=max_words,
        min_terms=min_terms,
        apply_noise_filter=apply_noise_filter,
    )
    if not cands and apply_noise_filter:
        # Fallback when the adaptive noise filter is too strict for this collection.
        cands = _prepare_string_candidates(
            tokens,
            noise_threshold=noise_threshold,
            max_words=max_words,
            min_terms=min_terms,
            apply_noise_filter=False,
        )
    if not cands:
        # Last-resort candidate pool: retain any normalized string with at least one TERM token.
        for raw in tokens:
            canon = _canon_string_for_pack(raw)
            if not canon:
                continue
            terms = _terms_for_pack(canon)
            if not terms:
                continue
            cands.append(
                {
                    "raw": raw,
                    "canon": canon,
                    "terms": terms,
                    "term_set": set(terms),
                    "score": 0.0,
                }
            )
    if not cands:
        return []

    for c in cands:
        c["score"] = _idf_mass(c["terms"], term_idf)

    picked: List[str] = []
    picked_sets: List[set] = []
    used = 0

    def _pick_from(pool: List[Dict[str, Any]], stage_budget: Optional[int] = None) -> None:
        nonlocal used
        for c in sorted(pool, key=lambda x: (float(x["score"]), x["canon"]), reverse=True):
            tlen = _token_len_quiet(tokenizer, c["raw"])
            if tlen <= 0:
                continue
            if used + tlen > budget:
                continue
            if stage_budget is not None and used + tlen > stage_budget:
                continue
            if apply_redundancy:
                if _redundant(c["term_set"], picked_sets, threshold=redundancy_threshold):
                    continue
            picked.append(c["raw"])
            picked_sets.append(c["term_set"])
            used += tlen
            if used >= budget:
                break

    _pick_from(cands, stage_budget=None)
    if not picked:
        # Rescue pass: keep at least one candidate even if token-id extraction failed globally.
        for c in sorted(cands, key=lambda x: (float(x["score"]), x["canon"]), reverse=True):
            raw = str(c.get("raw") or "").strip()
            if not raw:
                continue
            picked.append(raw)
            break
    return picked


def build_packed_docs_for_oids(
    oids: List[str],
    *,
    pack_budget_tokens: int = 0,
) -> Dict[str, str]:
    """
    Build query-independent packed surrogate text per executable OID.

    This exposes the same IDF packing path used by fuse retrieval so other
    retrievers can index/search over packed documents directly.
    """
    _, tokenizer, max_tokens = _get_model()
    exes = filter_executables(list(oids))
    if not exes:
        return {}

    tokens_map = {oid: extract_tokens(oid) for oid in exes}
    str_docs = {oid: tokens_map[oid]["str"] for oid in exes}

    pack_cfg: Dict[str, float] = {
        "noise_threshold": 0.70,
        "max_words": 48.0,
        "min_terms": 2.0,
        "redundancy_threshold": 0.80,
        "prune_keep_quantile": 0.75,
        "prune_min_keep": 8.0,
    }
    pack_cfg.update(derive_idf_pack_auto_params(str_docs))

    effective_budget = max_tokens
    if pack_budget_tokens > 0:
        effective_budget = max(1, min(max_tokens, int(pack_budget_tokens)))

    str_term_idf = compute_term_idf_from_strings(
        str_docs,
        noise_threshold=float(pack_cfg["noise_threshold"]),
        max_words=int(pack_cfg["max_words"]),
        min_terms=int(pack_cfg["min_terms"]),
    )

    out: Dict[str, str] = {}
    for oid in exes:
        selected = select_strings_by_idf_pack(
            tokens_map[oid]["str"],
            budget=effective_budget,
            tokenizer=tokenizer,
            term_idf=str_term_idf,
            redundancy_threshold=float(pack_cfg["redundancy_threshold"]),
            noise_threshold=float(pack_cfg["noise_threshold"]),
            max_words=int(pack_cfg["max_words"]),
            min_terms=int(pack_cfg["min_terms"]),
        )
        out[oid] = " ".join(selected).strip()

    return out


def build_packed_docs_for_collection(
    cid: str,
    *,
    pack_budget_tokens: int = 0,
) -> Dict[str, str]:
    """Build packed surrogate text for all executable files in one collection."""
    oids = api.expand_oids(cid)
    return build_packed_docs_for_oids(
        oids,
        pack_budget_tokens=pack_budget_tokens,
    )


def build_packed_doc_for_oid(
    oid: str,
    *,
    corpus_oids: Optional[List[str]] = None,
    pack_budget_tokens: int = 0,
) -> str:
    """
    Build one packed surrogate text.

    If corpus_oids is provided, IDF is computed over that corpus and the target
    doc is extracted from it. Otherwise IDF is computed on the single OID only.
    """
    oids = list(corpus_oids) if corpus_oids else [oid]
    docs = build_packed_docs_for_oids(
        oids,
        pack_budget_tokens=pack_budget_tokens,
    )
    return docs.get(oid, "")
