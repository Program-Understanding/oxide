DESC = "Strings-only file retrieval using parameter-free IDF evidence packing with dense ranking"
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
    "prompt": {"type": str, "mangle": True, "default": ""},
    "prompt_path": {"type": str, "mangle": True, "default": ""},
    "top_k": {"type": int, "mangle": True, "default": 0},
    "include_string_rankings": {"type": bool, "mangle": True, "default": True},
    "strings_for_top_n_oids": {"type": int, "mangle": True, "default": 0},
    "top_k_strings_per_oid": {"type": int, "mangle": True, "default": 0},
    "string_emb_batch_size": {"type": int, "mangle": False, "default": 128},
    "pack_budget_tokens": {"type": int, "mangle": True, "default": 0},
}

# -------------------------------------------------------------
# Model setup
# -------------------------------------------------------------
MODEL_ID = "sentence-transformers/all-MiniLM-L6-v2"
# Bump to invalidate any localstore caches that depend on packed-doc behavior.
PACKED_DOC_CACHE_VERSION = 2

# Allow alnum tokens; keep this conservative but not letters-only
TERM = re.compile(r"[a-z][a-z0-9]{2,}", re.IGNORECASE)

def _infer_model_token_budget(tokenizer: Any, model: Any, default: int = 512) -> int:
    # Use the tokenizer's model_max_length as the budget.
    # We explicitly ignore model.max_seq_length because sentence-transformers sets it
    # conservatively (e.g. 256 for MiniLM) even when the underlying tokenizer supports 512.
    # We sync max_seq_length up to the tokenizer limit after loading so the model doesn't
    # silently truncate inputs we've already packed to the full budget.
    tok_limit = getattr(tokenizer, "model_max_length", None)
    try:
        tok_limit_i = int(tok_limit) if tok_limit is not None else int(default)
    except Exception:
        tok_limit_i = int(default)
    if tok_limit_i <= 0 or tok_limit_i > 100000:
        tok_limit_i = int(default)

    # Sync the model so it encodes up to the full tokenizer budget.
    try:
        model.max_seq_length = tok_limit_i
    except Exception:
        pass

    return tok_limit_i


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
    try:
        oid_list = api.expand_oids(oid_list)
    except Exception:
        pass

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

    top_k = int(opts.get("top_k", 0))
    include_string_rankings = bool(opts.get("include_string_rankings", True))
    strings_for_top_n_oids = int(opts.get("strings_for_top_n_oids", 0) or 0)
    try:
        top_k_strings_per_oid = int(opts.get("top_k_strings_per_oid", 0))
    except Exception:
        top_k_strings_per_oid = 0
    string_emb_batch_size = int(opts.get("string_emb_batch_size", 128) or 128)
    pack_budget_tokens = int(opts.get("pack_budget_tokens", 0) or 0)

    return search_prompt(
        oid_list,
        prompt,
        top_k=top_k,
        include_string_rankings=include_string_rankings,
        strings_for_top_n_oids=strings_for_top_n_oids,
        top_k_strings_per_oid=top_k_strings_per_oid,
        string_emb_batch_size=string_emb_batch_size,
        pack_budget_tokens=pack_budget_tokens,
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
    pack_budget_tokens: int = 0,
) -> Tuple[np.ndarray, List[str]]:
    """
    Generate packed-document embedding matrix for the provided OIDs.
    Returns (matrix, ordered_oids).
    """
    model, tokenizer, max_tokens = _get_model()
    if string_emb_batch_size <= 0:
        string_emb_batch_size = 128

    ordered = list(oids)
    tokens_map = {oid: extract_tokens(oid) for oid in ordered}

    str_docs = {k: v["str"] for k, v in tokens_map.items()}

    effective_budget = max_tokens
    if pack_budget_tokens > 0:
        # Do not exceed model tokenization budget; larger values would be truncated anyway.
        effective_budget = max(1, min(max_tokens, int(pack_budget_tokens)))

    str_term_idf = compute_term_idf_from_strings(str_docs)

    dim = model.get_sentence_embedding_dimension()
    vectors: List[np.ndarray] = []

    for oid in ordered:
        strs = select_strings_by_idf_pack(
            tokens_map[oid]["str"],
            budget=effective_budget,
            tokenizer=tokenizer,
            term_idf=str_term_idf,
        )
        str_doc = _truncate_text_to_budget(
            " ".join(strs).strip(),
            tokenizer=tokenizer,
            budget=effective_budget,
        )

        if not str_doc:
            vectors.append(np.zeros(dim, dtype=np.float32))
        else:
            vec = model.encode(str_doc, normalize_embeddings=True).astype(np.float32)
            vectors.append(vec)

    return np.vstack(vectors).astype("float32"), ordered


def search_prompt(
    oids: List[str],
    prompt: str,
    top_k: int = 0,
    include_string_rankings: bool = True,
    strings_for_top_n_oids: int = 0,
    top_k_strings_per_oid: int = 0,
    string_emb_batch_size: int = 128,
    pack_budget_tokens: int = 0,
) -> Dict[str, Any]:
    """Search prompt over candidate OIDs; return dense-ranked results."""
    model, _, _ = _get_model()

    exes = list(oids)
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
    else:
        emb_mat, ordered = build_embedding_matrix(
            exes,
            string_emb_batch_size=string_emb_batch_size,
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
    best = ranked[0] if ranked else None

    if include_string_rankings:
        candidate_limit = len(ranked)
        if strings_for_top_n_oids > 0:
            candidate_limit = min(len(ranked), strings_for_top_n_oids)
        for i, cand in enumerate(ranked):
            if i < candidate_limit:
                tokens = extract_tokens(str(cand.get("oid") or "")).get("str", [])
                cand["string_matches"] = _rank_strings_for_oid(
                    tokens,
                    q,
                    model=model,
                    top_k=top_k_strings_per_oid,
                    string_emb_batch_size=string_emb_batch_size,
                )
            else:
                cand["string_matches"] = []

    resp = {"prompt": prompt, "results": {"best_match": best, "candidates": ranked}}
    return resp


def _rank_strings_for_oid(
    tokens: List[str],
    query_vec: np.ndarray,
    *,
    model: Any,
    top_k: int = 0,
    string_emb_batch_size: int = 128,
) -> List[Dict[str, Any]]:
    k = int(top_k)

    batch_size = max(1, int(string_emb_batch_size))
    strings = list(dict.fromkeys(s for s in tokens if s))
    if not strings:
        return []

    embs = model.encode(strings, batch_size=batch_size, normalize_embeddings=True)
    embs_arr = np.asarray(embs, dtype=np.float32)
    q = np.asarray(query_vec, dtype=np.float32).reshape(-1)
    if embs_arr.ndim == 1:
        sims = [float(np.dot(embs_arr, q))]
    else:
        sims = [float(x) for x in embs_arr.dot(q).tolist()]

    rows = [{"string": s, "similarity": float(sim)} for s, sim in zip(strings, sims)]
    rows.sort(key=lambda x: (-float(x["similarity"]), str(x["string"])))
    for rank, row in enumerate(rows, start=1):
        row["rank"] = int(rank)
    if k > 0:
        return rows[:k]
    return rows


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


def compute_term_idf_from_strings(docs: Dict[str, List[str]]) -> Dict[str, float]:
    df = Counter()
    N = max(1, len(docs))
    for toks in docs.values():
        seen_terms: set = set()
        for s in toks:
            canon = _canon_string_for_pack(s)
            if canon:
                seen_terms.update(_terms_for_pack(canon))
        for t in seen_terms:
            df[t] += 1
    return {t: math.log((N + 1) / (cnt + 1)) + 1.0 for t, cnt in df.items()}


def select_strings_by_idf_pack(
    tokens: List[str],
    budget: int,
    tokenizer: Any,
    term_idf: Dict[str, float],
) -> List[str]:
    """
    Evidence packing under token budget: score each string by IDF mass,
    sort descending, greedily add until budget exhausted.
    """
    if budget <= 0:
        return []

    seen: set = set()
    cands: List[Dict[str, Any]] = []
    for raw in tokens:
        canon = _canon_string_for_pack(raw)
        if not canon or canon in seen:
            continue
        seen.add(canon)
        terms = _terms_for_pack(canon)
        if not terms:
            continue
        score = float(sum(term_idf.get(t, 0.0) for t in set(terms)))
        cands.append({"raw": raw, "canon": canon, "score": score})

    if not cands:
        return []

    picked: List[str] = []
    used = 0
    for c in sorted(cands, key=lambda x: (float(x["score"]), x["canon"]), reverse=True):
        tlen = _token_len_quiet(tokenizer, c["raw"])
        if tlen <= 0:
            continue
        if used + tlen > budget:
            continue
        picked.append(c["raw"])
        used += tlen
        if used >= budget:
            break

    if not picked and cands:
        # Keep at least one candidate even if token-id extraction yielded no lengths.
        picked.append(cands[0]["raw"])

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
    exes = list(oids)
    if not exes:
        return {}

    tokens_map = {oid: extract_tokens(oid) for oid in exes}
    str_docs = {oid: tokens_map[oid]["str"] for oid in exes}

    effective_budget = max_tokens
    if pack_budget_tokens > 0:
        effective_budget = max(1, min(max_tokens, int(pack_budget_tokens)))

    str_term_idf = compute_term_idf_from_strings(str_docs)

    out: Dict[str, str] = {}
    for oid in exes:
        selected = select_strings_by_idf_pack(
            tokens_map[oid]["str"],
            budget=effective_budget,
            tokenizer=tokenizer,
            term_idf=str_term_idf,
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
