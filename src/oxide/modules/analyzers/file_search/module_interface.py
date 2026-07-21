DESC = "Unified file retrieval over embedded strings with BM25 or PACT backends"
NAME = "file_search"

import hashlib
import json
import logging
import math
import re
from collections import Counter
from typing import Any, Dict, List, Optional, Sequence, Tuple

import numpy as np
from transformers import AutoTokenizer

from oxide.core import api

try:
    from rank_bm25 import BM25Okapi
except Exception:
    BM25Okapi = None

logger = logging.getLogger(NAME)

opts_doc = {
    "prompt": {"type": str, "mangle": True, "default": ""},
    "prompt_path": {"type": str, "mangle": True, "default": ""},
    "top_k": {"type": int, "mangle": True, "default": 0},
    "backend": {"type": str, "mangle": True, "default": "pact"},
    "oids": {"type": list, "mangle": False, "default": []},
    "include_string_rankings": {"type": bool, "mangle": True, "default": True},
    "strings_for_top_n_oids": {"type": int, "mangle": True, "default": 0},
    "top_k_strings_per_oid": {"type": int, "mangle": True, "default": 0},
    "string_emb_batch_size": {"type": int, "mangle": False, "default": 128},
    "pack_budget_tokens": {"type": int, "mangle": True, "default": 0},
}

RAW_TERM = re.compile(r"[A-Za-z]{3,}")
TERM = re.compile(r"[a-z][a-z0-9]{2,}", re.IGNORECASE)
MODEL_ID = "sentence-transformers/all-MiniLM-L6-v2"
PACKED_DOC_CACHE_VERSION = 2
_MODEL_BUNDLE: Optional[Tuple["SentenceTransformer", Any, int]] = None


def documentation() -> Dict[str, Any]:
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }


def _normalize_backend(raw: Any) -> str:
    backend = str(raw or "pact").strip().lower()
    alias = {
        "fuse": "pact",
        "pack": "pact",
        "emb": "pact",
        "semantic": "pact",
        "lexical": "bm25",
    }
    backend = alias.get(backend, backend)
    if backend not in {"bm25", "pact"}:
        backend = "pact"
    return backend


def _normalize_oids_opt(raw: Any) -> List[str]:
    if raw is None:
        return []
    vals: List[Any]
    if isinstance(raw, str):
        s = raw.strip()
        if not s:
            return []
        parsed = None
        if s.startswith("[") and s.endswith("]"):
            try:
                parsed = json.loads(s)
            except Exception:
                parsed = None
        if isinstance(parsed, list):
            vals = list(parsed)
        else:
            vals = [x.strip() for x in s.split(",")]
    elif isinstance(raw, (list, tuple, set)):
        vals = list(raw)
        if vals and all(isinstance(x, str) and len(x) == 1 for x in vals):
            joined = "".join(vals).strip()
            if joined:
                return _normalize_oids_opt(joined)
    else:
        vals = [raw]

    out: List[str] = []
    for v in vals:
        s = str(v or "").strip()
        if s:
            out.append(s)
    return list(dict.fromkeys(out))


def _resolve_scope(exe_scope: Sequence[str], requested_oids: Sequence[str]) -> Tuple[List[str], Optional[str]]:
    all_exes = [str(x) for x in exe_scope if str(x)]
    if not requested_oids:
        return all_exes, None

    requested = _normalize_oids_opt(list(requested_oids))
    allowed = set(all_exes)
    invalid = [x for x in requested if x not in allowed]
    if invalid:
        return [], (
            "Invalid scope OID(s): "
            + ", ".join(str(x) for x in invalid)
            + ". OID scope must be executable OIDs in this collection."
        )

    req_set = set(requested)
    scoped = [x for x in all_exes if x in req_set]
    return scoped, None


def results(oid_list: List[str], opts: dict) -> Dict[str, Any]:
    try:
        oid_list = api.expand_oids(oid_list)
    except Exception:
        pass

    prompt = str(opts.get("prompt") or "").strip()
    prompt_path = str(opts.get("prompt_path") or "").strip()
    if not prompt and not prompt_path:
        return {"error": "Provide a prompt via 'prompt' or 'prompt_path'."}
    if not prompt and prompt_path:
        try:
            with open(prompt_path, "r", encoding="utf-8") as fp:
                prompt = fp.read().strip()
        except OSError as e:
            return {"error": f"Failed to read prompt_path: {e}"}

    top_k = int(opts.get("top_k", 0))
    backend = _normalize_backend(opts.get("backend"))
    include_string_rankings = bool(opts.get("include_string_rankings", True))
    strings_for_top_n_oids = int(opts.get("strings_for_top_n_oids", 0) or 0)
    try:
        top_k_strings_per_oid = int(opts.get("top_k_strings_per_oid", 0))
    except Exception:
        top_k_strings_per_oid = 0
    string_emb_batch_size = int(opts.get("string_emb_batch_size", 128) or 128)
    pack_budget_tokens = int(opts.get("pack_budget_tokens", 0) or 0)
    requested_oids = _normalize_oids_opt(opts.get("oids", []))

    scope_oids, scope_err = _resolve_scope(list(oid_list), requested_oids)
    if scope_err:
        return {"error": scope_err}

    if backend == "bm25":
        return search_prompt_bm25(
            oids=scope_oids,
            prompt=prompt,
            top_k=top_k,
            requested_oids=[],
            include_string_rankings=include_string_rankings,
            strings_for_top_n_oids=strings_for_top_n_oids,
            top_k_strings_per_oid=top_k_strings_per_oid,
        )

    return search_prompt_pact(
        scope_oids,
        prompt,
        top_k=top_k,
        include_string_rankings=include_string_rankings,
        strings_for_top_n_oids=strings_for_top_n_oids,
        top_k_strings_per_oid=top_k_strings_per_oid,
        string_emb_batch_size=string_emb_batch_size,
        pack_budget_tokens=pack_budget_tokens,
    )


def search_prompt_bm25(
    oids: Sequence[str],
    prompt: str,
    *,
    top_k: int = 0,
    requested_oids: Optional[Sequence[str]] = None,
    include_string_rankings: bool = True,
    strings_for_top_n_oids: int = 0,
    top_k_strings_per_oid: int = 0,
) -> Dict[str, Any]:
    if BM25Okapi is None:
        return {"error": "rank_bm25 is not available; install rank-bm25."}

    scope_oids, scope_err = _resolve_scope(list(oids), requested_oids or [])
    if scope_err:
        return {"error": scope_err}
    if not scope_oids:
        return {"prompt": prompt, "results": {"best_match": None, "candidates": []}}

    ranked = _rank_oids_by_bm25(scope_oids, prompt)
    if top_k > 0:
        ranked = ranked[: int(top_k)]
    best = ranked[0] if ranked else None

    if include_string_rankings:
        candidate_limit = len(ranked)
        if int(strings_for_top_n_oids) > 0:
            candidate_limit = min(len(ranked), int(strings_for_top_n_oids))
        for i, cand in enumerate(ranked):
            if i < candidate_limit:
                cand["string_matches"] = _rank_strings_for_oid_bm25(
                    str(cand.get("oid") or ""),
                    prompt,
                    top_k=int(top_k_strings_per_oid),
                )
            else:
                cand["string_matches"] = []

    return {"prompt": prompt, "results": {"best_match": best, "candidates": ranked}}


def _rank_oids_by_bm25(oids: Sequence[str], prompt: str) -> List[Dict[str, Any]]:
    oids_list = [str(x) for x in oids if str(x)]
    if not oids_list:
        return []

    corpus = [_bm25_tokens_for_oid(oid) for oid in oids_list]
    bm25 = _safe_build_bm25(corpus)
    if bm25 is None:
        return []

    q_tokens = _bm25_tokens_for_text(str(prompt or ""))
    if not q_tokens:
        return []

    scores = bm25.get_scores(q_tokens)
    rows: List[Tuple[str, float]] = []
    for idx, oid in enumerate(oids_list):
        try:
            score = float(scores[idx])
        except Exception:
            score = 0.0
        rows.append((oid, score))
    rows.sort(key=lambda x: (-float(x[1]), str(x[0])))

    return [{"oid": oid, "names": get_names(oid), "score": float(score)} for oid, score in rows]


def _rank_strings_for_oid_bm25(oid: str, prompt: str, *, top_k: int = 0) -> List[Dict[str, Any]]:
    k = int(top_k)
    raw_strings = _raw_strings_for_oid(oid)
    if not raw_strings:
        return []
    strings = list(dict.fromkeys(raw_strings))
    if not strings:
        return []

    query_tokens = _bm25_tokens_for_text(prompt)
    if not query_tokens:
        return []

    corpus = [_bm25_tokens_for_text(s) for s in strings]
    bm25 = _safe_build_bm25(corpus)
    if bm25 is None:
        return []

    scores = bm25.get_scores(query_tokens)
    rows: List[Dict[str, Any]] = []
    for s, score in zip(strings, scores):
        try:
            sc = float(score)
        except Exception:
            sc = 0.0
        rows.append({"string": s, "bm25_score": sc})
    rows.sort(key=lambda x: (-float(x["bm25_score"]), str(x["string"])))
    for rank, row in enumerate(rows, start=1):
        row["rank"] = int(rank)
    return rows[:k] if k > 0 else rows


def _safe_build_bm25(corpus: Sequence[Sequence[str]]) -> Any:
    if BM25Okapi is None or not corpus:
        return None
    if not any(list(doc or []) for doc in corpus):
        return None
    try:
        return BM25Okapi([list(doc or []) for doc in corpus])
    except Exception:
        return None


def _raw_strings_for_oid(oid: str) -> List[str]:
    raw = api.get_field("strings", oid, oid) or {}
    out: List[str] = []
    if isinstance(raw, dict):
        vals = raw.values()
    elif isinstance(raw, (list, tuple)):
        vals = list(raw)
    else:
        vals = [raw]
    for v in vals:
        s = str(v or "").strip()
        if s:
            out.append(s)
    return out


def _bm25_tokens_for_oid(oid: str) -> List[str]:
    toks: List[str] = []
    for s in _raw_strings_for_oid(oid):
        toks.extend(_bm25_tokens_for_text(s))
    return toks


def _bm25_tokens_for_text(text: str) -> List[str]:
    if not text:
        return []
    return [t.lower() for t in RAW_TERM.findall(text)]


def _infer_model_token_budget(tokenizer: Any, model: Any, default: int = 512) -> int:
    tok_limit = getattr(tokenizer, "model_max_length", None)
    try:
        tok_limit_i = int(tok_limit) if tok_limit is not None else int(default)
    except Exception:
        tok_limit_i = int(default)
    if tok_limit_i <= 0 or tok_limit_i > 100000:
        tok_limit_i = int(default)
    try:
        model.max_seq_length = tok_limit_i
    except Exception:
        pass
    return tok_limit_i


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


def _cache_key(oids: List[str], config: Dict[str, Any]) -> str:
    cfg_blob = json.dumps(config, sort_keys=True, separators=(",", ":")).encode("utf-8")
    cfg_hash = hashlib.sha256(cfg_blob).hexdigest()[:12]

    h = hashlib.sha256()
    for oid in sorted(oids):
        h.update(oid.encode("utf-8"))
        h.update(b"\n")
    model_key = re.sub(r"[\\\\/]", "_", str(MODEL_ID))
    return f"{model_key}|str_select=idf_pack_auto|cfg={cfg_hash}|n={len(oids)}|{h.hexdigest()[:16]}"


def build_embedding_matrix(
    oids: List[str],
    string_emb_batch_size: int = 128,
    pack_budget_tokens: int = 0,
) -> Tuple[np.ndarray, List[str]]:
    model, tokenizer, max_tokens = _get_model()
    if string_emb_batch_size <= 0:
        string_emb_batch_size = 128

    ordered = list(oids)
    tokens_map = {oid: extract_tokens(oid) for oid in ordered}
    str_docs = {k: v["str"] for k, v in tokens_map.items()}

    effective_budget = max_tokens
    if pack_budget_tokens > 0:
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
        str_doc = _truncate_text_to_budget(" ".join(strs).strip(), tokenizer=tokenizer, budget=effective_budget)
        if not str_doc:
            vectors.append(np.zeros(dim, dtype=np.float32))
        else:
            vec = model.encode(str_doc, normalize_embeddings=True).astype(np.float32)
            vectors.append(vec)

    return np.vstack(vectors).astype("float32"), ordered


def search_prompt_pact(
    oids: List[str],
    prompt: str,
    top_k: int = 0,
    include_string_rankings: bool = True,
    strings_for_top_n_oids: int = 0,
    top_k_strings_per_oid: int = 0,
    string_emb_batch_size: int = 128,
    pack_budget_tokens: int = 0,
) -> Dict[str, Any]:
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

    idxs = np.argsort(-sims)
    if top_k > 0:
        idxs = idxs[:top_k]

    ranked = [
        {"oid": exes[i], "names": get_names(exes[i]), "score": float(sims[i])}
        for i in idxs
    ]
    best = ranked[0] if ranked else None

    if include_string_rankings:
        candidate_limit = len(ranked)
        if strings_for_top_n_oids > 0:
            candidate_limit = min(len(ranked), strings_for_top_n_oids)
        for i, cand in enumerate(ranked):
            if i < candidate_limit:
                tokens = extract_tokens(str(cand.get("oid") or "")).get("str", [])
                cand["string_matches"] = _rank_strings_for_oid_pact(
                    tokens,
                    q,
                    model=model,
                    top_k=top_k_strings_per_oid,
                    string_emb_batch_size=string_emb_batch_size,
                )
            else:
                cand["string_matches"] = []

    return {"prompt": prompt, "results": {"best_match": best, "candidates": ranked}}


def _rank_strings_for_oid_pact(
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
    return rows[:k] if k > 0 else rows


def normalize(text: str) -> str:
    from unicodedata import normalize as u_norm

    text = u_norm("NFC", text)
    text = text.replace("_", " ")
    text = re.sub(r"[^\w\s]", " ", text)
    return re.sub(r"\s+", " ", text).strip().lower()


def get_names(oid: str) -> List[str]:
    return list(api.get_names_from_oid(oid))


def separate_oids(oids: Sequence[str]) -> Tuple[List[str], List[str]]:
    exes: List[str] = []
    others: List[str] = []
    for oid in oids:
        cat = api.get_field("categorize", oid, oid)
        if cat == "executable":
            exes.append(str(oid))
        else:
            others.append(str(oid))
    return exes, others


def filter_executables(oids: Sequence[str]) -> List[str]:
    exes, _ = separate_oids(oids)
    filtered: List[str] = []
    for oid in exes:
        names = get_names(oid)
        if any(ext in name for name in names for ext in (".so", ".ko")):
            continue
        filtered.append(oid)
    return filtered


def extract_tokens(oid: str) -> Dict[str, List[str]]:
    raw_strs = api.get_field("strings", oid, oid) or {}
    strings: List[str] = []
    for s in raw_strs.values():
        if not isinstance(s, str):
            continue
        if len(s) >= 200:
            continue
        ns = normalize(s)
        if TERM.search(ns):
            strings.append(ns)
    return {"str": strings}


def _canon_string_for_pack(text: str) -> str:
    s = (text or "").lower().strip()
    if not s:
        return ""
    return re.sub(r"\s+", " ", s).strip()


def _token_ids_for_text_quiet(tokenizer: Any, text: str) -> List[int]:
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
    s = (text or "").strip()
    if not s or budget <= 0:
        return s
    ids = _token_ids_for_text_quiet(tokenizer, s)
    if not ids or len(ids) <= budget:
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
    count_docs = max(1, len(docs))
    for toks in docs.values():
        seen_terms: set = set()
        for s in toks:
            canon = _canon_string_for_pack(s)
            if canon:
                seen_terms.update(_terms_for_pack(canon))
        for term in seen_terms:
            df[term] += 1
    return {term: math.log((count_docs + 1) / (cnt + 1)) + 1.0 for term, cnt in df.items()}


def select_strings_by_idf_pack(
    tokens: List[str],
    budget: int,
    tokenizer: Any,
    term_idf: Dict[str, float],
) -> List[str]:
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
        score = float(sum(term_idf.get(term, 0.0) for term in set(terms)))
        cands.append({"raw": raw, "canon": canon, "score": score})

    if not cands:
        return []

    picked: List[str] = []
    used = 0
    for cand in sorted(cands, key=lambda x: (float(x["score"]), x["canon"]), reverse=True):
        tlen = _token_len_quiet(tokenizer, cand["raw"])
        if tlen <= 0 or used + tlen > budget:
            continue
        picked.append(cand["raw"])
        used += tlen
        if used >= budget:
            break

    if not picked and cands:
        picked.append(cands[0]["raw"])
    return picked


def build_packed_docs_for_oids(
    oids: List[str],
    *,
    pack_budget_tokens: int = 0,
) -> Dict[str, str]:
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
    oids = api.expand_oids(cid)
    return build_packed_docs_for_oids(oids, pack_budget_tokens=pack_budget_tokens)


def build_packed_doc_for_oid(
    oid: str,
    *,
    corpus_oids: Optional[List[str]] = None,
    pack_budget_tokens: int = 0,
) -> str:
    oids = list(corpus_oids) if corpus_oids else [oid]
    docs = build_packed_docs_for_oids(oids, pack_budget_tokens=pack_budget_tokens)
    return docs.get(oid, "")
