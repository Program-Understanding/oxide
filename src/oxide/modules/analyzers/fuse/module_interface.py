DESC = "Retrieves the top file(s) for a given prompt using semantic embedding models"
NAME = "fuse"

import hashlib
import math
import re
import logging
from collections import Counter
from typing import List, Dict, Tuple, Any, Optional

import numpy as np
from sentence_transformers import SentenceTransformer
from transformers import AutoTokenizer

from oxide.core import api

logger = logging.getLogger(NAME)

opts_doc = {
    "prompt": {"type": str, "mangle": False, "default": ""},
    "prompt_path": {"type": str, "mangle": False, "default": ""},
    "use_tags": {"type": bool, "mangle": False, "default": True},
    "top_k": {"type": int, "mangle": False, "default": 50},
}

# -------------------------------------------------------------
# Model setup
# -------------------------------------------------------------
MODEL_ID = "sentence-transformers/all-MiniLM-L6-v2"
_MODEL: Optional[SentenceTransformer] = None
_TOKENIZER: Optional[Any] = None
_MAX_TOKENS: Optional[int] = None

# Allow alnum tokens; keep this conservative but not letters-only
TERM = re.compile(r"[a-z][a-z0-9]{2,}", re.IGNORECASE)

def _get_model() -> Tuple[SentenceTransformer, Any, int]:
    global _MODEL, _TOKENIZER, _MAX_TOKENS
    if _MODEL is None or _TOKENIZER is None or _MAX_TOKENS is None:
        tok = AutoTokenizer.from_pretrained(MODEL_ID)
        mdl = SentenceTransformer(MODEL_ID)

        # SentenceTransformers often truncates to mdl.max_seq_length (commonly 256)
        mdl_limit = getattr(mdl, "max_seq_length", None)
        tok_limit = getattr(tok, "model_max_length", None) or 512
        budget = min(tok_limit, mdl_limit) if mdl_limit else tok_limit

        _TOKENIZER = tok
        _MODEL = mdl
        _MAX_TOKENS = int(budget)
    return _MODEL, _TOKENIZER, _MAX_TOKENS


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

    use_tags = bool(opts.get("use_tags", True))
    top_k = int(opts.get("top_k", 50))

    return search_prompt(oid_list, prompt, use_tags=use_tags, top_k=top_k)


# -------------------------------------------------------------
# Embedding & Search
# -------------------------------------------------------------
def _cache_key(oids: List[str], use_tags: bool) -> str:
    # Stable key across runs; includes model + mode + exact candidate set.
    h = hashlib.sha256()
    for oid in sorted(oids):
        h.update(oid.encode("utf-8"))
        h.update(b"\n")
    return f"{MODEL_ID}|use_tags={use_tags}|n={len(oids)}|{h.hexdigest()[:16]}"


def build_embedding_matrix(oids: List[str], use_tags: bool = True) -> Tuple[np.ndarray, List[str]]:
    """
    Generate fused embedding matrix for the provided OIDs.
    Returns (matrix, ordered_oids).
    """
    model, tokenizer, max_tokens = _get_model()
    eps = 1e-8

    ordered = list(oids)
    tokens_map = {oid: extract_tokens(oid, use_tags) for oid in ordered}

    str_idf = compute_idf({k: v["str"] for k, v in tokens_map.items()})
    tag_idf = compute_idf({k: v["tag"] for k, v in tokens_map.items()}) if use_tags else {}

    dim = model.get_sentence_embedding_dimension()
    vectors: List[np.ndarray] = []

    for oid in ordered:
        strs = select_until(tokens_map[oid]["str"], str_idf, max_tokens, tokenizer)
        str_doc = " ".join(strs).strip()

        # Encode empty docs safely
        if not str_doc:
            str_emb = np.zeros(dim, dtype=np.float32)
        else:
            str_emb = model.encode(str_doc, normalize_embeddings=True).astype(np.float32)

        if use_tags:
            tags = select_until(tokens_map[oid]["tag"], tag_idf, max_tokens, tokenizer)
            tag_doc = " ".join(tags).strip()

            if not tag_doc:
                tag_emb = np.zeros(dim, dtype=np.float32)
            else:
                tag_emb = model.encode(tag_doc, normalize_embeddings=True).astype(np.float32)

            n_s = len(tokenizer.tokenize(str_doc)) if str_doc else 0
            n_t = len(tokenizer.tokenize(tag_doc)) if tag_doc else 0
            alpha = (n_t / (n_s + n_t + eps)) if (n_s + n_t) else 0.0
            vec = (1.0 - alpha) * str_emb + alpha * tag_emb
        else:
            vec = str_emb

        norm = float(np.linalg.norm(vec))
        if norm > eps:
            vec = vec / norm
        vectors.append(vec.astype(np.float32))

    return np.vstack(vectors).astype("float32"), ordered


def search_prompt(oids: List[str], prompt: str, use_tags: bool = True, top_k: int = 50) -> Dict[str, Any]:
    """Search prompt over candidate OIDs; return ranked results."""
    model, _, _ = _get_model()

    exes = filter_executables(oids)
    if not exes:
        return {"prompt": prompt, "results": {"best_match": None, "candidates": []}}

    key = _cache_key(exes, use_tags)

    cached = api.local_retrieve(NAME, key) if api.local_exists(NAME, key) else None
    if cached and "oids" in cached and "emb" in cached and cached["oids"] == exes:
        emb_mat = cached["emb"]
    else:
        emb_mat, ordered = build_embedding_matrix(exes, use_tags)
        api.local_store(NAME, key, {"oids": ordered, "emb": emb_mat})

    q = model.encode(prompt, normalize_embeddings=True).astype("float32")
    sims = emb_mat.dot(q)

    idxs = np.argsort(-sims)
    if top_k > 0:
        idxs = idxs[:top_k]

    def fmt(i: int) -> Dict[str, Any]:
        oid = exes[i]
        return {"oid": oid, "names": get_names(oid), "score": float(sims[i])}

    ranked = [fmt(i) for i in idxs]
    best = ranked[0] if ranked else None

    return {"prompt": prompt, "results": {"best_match": best, "candidates": ranked}}


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


def extract_tokens(oid: str, use_tags: bool = True) -> Dict[str, List[str]]:
    """Extract tokens from strings and (optionally) tags."""
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

    tags: List[str] = []
    if use_tags:
        inf = api.retrieve("tag_all_functions", oid) or {}
        func_tags = inf.get("func_tags") if isinstance(inf, dict) else None
        if isinstance(func_tags, dict):
            for entry in func_tags.values():
                if not isinstance(entry, str):
                    continue
                for term in normalize(entry).split():
                    if TERM.fullmatch(term):
                        tags.append(term)

    return {"str": strings, "tag": tags}


def compute_idf(docs: Dict[str, List[str]]) -> Dict[str, float]:
    df = Counter()
    N = max(1, len(docs))
    for toks in docs.values():
        for t in set(toks):
            df[t] += 1
    return {t: math.log((N + 1) / (cnt + 1)) + 1.0 for t, cnt in df.items()}


def select_until(tokens: List[str], idf: Dict[str, float], budget: int, tokenizer: Any) -> List[str]:
    """Select highest-IDF items until token budget."""
    picked: List[str] = []
    used = 0
    for tok in sorted(tokens, key=lambda x: idf.get(x, 0.0), reverse=True):
        tlen = len(tokenizer.tokenize(tok))
        if used + tlen > budget:
            continue
        picked.append(tok)
        used += tlen
        if used >= budget:
            break
    return picked
