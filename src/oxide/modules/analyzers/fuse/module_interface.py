DESC = "Strings-only file retrieval using auto-calibrated IDF evidence packing"
NAME = "fuse"

import hashlib
import json
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
    "top_k": {"type": int, "mangle": False, "default": 50},
    "string_emb_batch_size": {"type": int, "mangle": False, "default": 128},
    "debug_select": {"type": bool, "mangle": False, "default": False},
    "ablate_noise_filter": {"type": bool, "mangle": False, "default": False},
    "ablate_redundancy": {"type": bool, "mangle": False, "default": False},
    "ablate_idf": {"type": bool, "mangle": False, "default": False},
    "pack_budget_tokens": {"type": int, "mangle": False, "default": 0},
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
CAPABILITY_TERMS = {
    "http", "https", "tcp", "udp", "dns", "dhcp", "ssh", "rpc", "socket", "port",
    "config", "cfg", "json", "xml", "init", "daemon", "service", "system",
    "usr", "bin", "sbin", "etc", "lib", "tmp", "proc", "sys", "var",
    "uci", "ubus", "netifd", "opkg", "dropbear", "dnsmasq", "uhttpd", "odhcpd",
}

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

    top_k = int(opts.get("top_k", 50))
    string_emb_batch_size = int(opts.get("string_emb_batch_size", 128) or 128)
    debug_select = bool(opts.get("debug_select", False))
    ablate_noise_filter = bool(opts.get("ablate_noise_filter", False))
    ablate_redundancy = bool(opts.get("ablate_redundancy", False))
    ablate_idf = bool(opts.get("ablate_idf", False))
    pack_budget_tokens = int(opts.get("pack_budget_tokens", 0) or 0)

    return search_prompt(
        oid_list,
        prompt,
        top_k=top_k,
        string_emb_batch_size=string_emb_batch_size,
        debug_select=debug_select,
        ablate_noise_filter=ablate_noise_filter,
        ablate_redundancy=ablate_redundancy,
        ablate_idf=ablate_idf,
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
    return (
        f"{MODEL_ID}|str_select=idf_pack_auto|cfg={cfg_hash}|"
        f"n={len(oids)}|{h.hexdigest()[:16]}"
    )


def build_embedding_matrix(
    oids: List[str],
    string_emb_batch_size: int = 128,
    debug_select: bool = False,
    debug_out: Optional[Dict[str, Any]] = None,
    ablate_noise_filter: bool = False,
    ablate_redundancy: bool = False,
    ablate_idf: bool = False,
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
        apply_noise_filter=not ablate_noise_filter,
        use_idf=not ablate_idf,
    )

    dim = model.get_sentence_embedding_dimension()
    vectors: List[np.ndarray] = []
    if debug_select and debug_out is not None:
        debug_out.setdefault("string_select_mode", "idf_pack_auto")
        debug_out.setdefault("string_counts", [])
        debug_out["idf_pack_params"] = dict(pack_cfg)
        debug_out["effective_pack_budget_tokens"] = int(effective_budget)
        debug_out["ablation_flags"] = {
            "ablate_noise_filter": bool(ablate_noise_filter),
            "ablate_redundancy": bool(ablate_redundancy),
            "ablate_idf": bool(ablate_idf),
        }

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
            apply_noise_filter=not ablate_noise_filter,
            apply_redundancy=not ablate_redundancy,
        )
        str_doc = " ".join(strs).strip()

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
    ablate_noise_filter: bool = False,
    ablate_redundancy: bool = False,
    ablate_idf: bool = False,
    pack_budget_tokens: int = 0,
) -> Dict[str, Any]:
    """Search prompt over candidate OIDs; return ranked results."""
    model, _, _ = _get_model()

    exes = filter_executables(oids)
    if not exes:
        return {"prompt": prompt, "results": {"best_match": None, "candidates": []}}

    q = model.encode(prompt, normalize_embeddings=True).astype("float32")
    cache_cfg: Dict[str, Any] = {
        "ablate_noise_filter": bool(ablate_noise_filter),
        "ablate_redundancy": bool(ablate_redundancy),
        "ablate_idf": bool(ablate_idf),
        "pack_budget_tokens": int(pack_budget_tokens),
    }
    key = _cache_key(exes, cache_cfg)

    cached = api.local_retrieve(NAME, key) if api.local_exists(NAME, key) else None
    if cached and "oids" in cached and "emb" in cached and cached["oids"] == exes:
        emb_mat = cached["emb"]
        debug_out = {"cache_hit": True, "selection_config": cache_cfg} if debug_select else None
    else:
        debug_out = {"cache_hit": False, "selection_config": cache_cfg} if debug_select else None
        emb_mat, ordered = build_embedding_matrix(
            exes,
            string_emb_batch_size=string_emb_batch_size,
            debug_select=debug_select,
            debug_out=debug_out,
            ablate_noise_filter=ablate_noise_filter,
            ablate_redundancy=ablate_redundancy,
            ablate_idf=ablate_idf,
            pack_budget_tokens=pack_budget_tokens,
        )
        api.local_store(NAME, key, {"oids": ordered, "emb": emb_mat})
    sims = emb_mat.dot(q)

    idxs = np.argsort(-sims)
    if top_k > 0:
        idxs = idxs[:top_k]

    def fmt(i: int) -> Dict[str, Any]:
        oid = exes[i]
        return {"oid": oid, "names": get_names(oid), "score": float(sims[i])}

    ranked = [fmt(i) for i in idxs]
    best = ranked[0] if ranked else None

    resp = {"prompt": prompt, "results": {"best_match": best, "candidates": ranked}}
    if debug_select:
        resp["debug_select"] = debug_out or {}
    return resp


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


def _terms_for_pack(text: str) -> List[str]:
    return [t for t in text.split() if TERM.fullmatch(t)]


def _is_capability_candidate(terms: List[str]) -> bool:
    return any(t in CAPABILITY_TERMS for t in terms)


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
        is_cap = _is_capability_candidate(terms)
        chars = [c for c in canon if not c.isspace()]
        if not chars:
            continue

        n = float(len(chars))
        n_digit = sum(1 for c in chars if c.isdigit())
        n_alpha = sum(1 for c in chars if c.isalpha())
        n_other = len(chars) - n_digit - n_alpha
        noise_ratio = (n_digit + n_other) / n

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
            tlen = len(tokenizer.tokenize(c["raw"]))
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
    return picked
