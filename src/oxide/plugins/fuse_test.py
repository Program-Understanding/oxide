import json
import time
import logging
import re
import hashlib
import math
import random
import statistics
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Sequence, Set, Tuple

from oxide.core import api

NAME = "fuse_test"
logger = logging.getLogger(NAME)

FUSE_TOOLSET = "fuse"
DEFAULT_TOP_K_FILES = 50
PAPER_OPT_KEYS = (
    "string_emb_batch_size",
    "debug_select",
    "pack_budget_tokens",
    # New ablation labels (preferred)
    "ablate_no_gate",
    "ablate_bm25_only",
    "ablate_debug",
    # Backward compat
    "hybrid_enable",
    "hybrid_debug",
)

try:
    from rank_bm25 import BM25Okapi
except Exception:
    BM25Okapi = None

try:
    import numpy as np
except Exception:
    np = None

try:
    import torch
except Exception:
    torch = None

try:
    from sentence_transformers import CrossEncoder, SentenceTransformer
except Exception:
    CrossEncoder = None
    SentenceTransformer = None

try:
    from transformers import AutoModel, AutoModelForMaskedLM, AutoTokenizer
except Exception:
    AutoModel = None
    AutoModelForMaskedLM = None
    AutoTokenizer = None

RAW_TERM = re.compile(r"[A-Za-z]{3,}")
PACK_TERM = re.compile(r"[a-z][a-z0-9]{2,}", re.IGNORECASE)
UUID_PAT = re.compile(
    r"\b[0-9a-f]{8}-[0-9a-f]{4}-[1-5][0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}\b",
    re.IGNORECASE,
)
HEX_PAT = re.compile(r"\b(?:0x)?[0-9a-f]{8,}\b", re.IGNORECASE)
NUM_PAT = re.compile(r"\b\d{4,}\b")
SPACE_PAT = re.compile(r"\s+")

DEFAULT_COMPARE_METHODS = [
    "paper_idf_pack_auto",
    "bm25_raw",
    "bm25_norm",
    "function_embeddings",
]
EXTRA_COMPARE_METHODS = [
    "bm25_rm3",
    "bm25f",
    "chargram_bm25",
    "splade_style",
    "dense_chunked",
    "colbert_style",
    "bm25_rerank_ce",
    "dense_rerank_ce",
    "bm25_dense_rrf",
    "bm25_splade_rrf",
]
ALL_COMPARE_METHODS = DEFAULT_COMPARE_METHODS + EXTRA_COMPARE_METHODS
METHOD_ALIASES = {
    "fuse": "paper_idf_pack_auto",
    "splade": "splade_style",
    "dense": "dense_chunked",
    "colbert": "colbert_style",
}

REPRESENTATION_IDS = ["r0_raw", "r1_norm", "r2_packed"]
REPRESENTATION_ALIASES = {
    "raw": "r0_raw",
    "norm": "r1_norm",
    "normalized": "r1_norm",
    "packed": "r2_packed",
    "fuse": "r2_packed",
}

# Bump to invalidate cached packed documents when packing logic changes.
R2_PACKED_DOCS_CACHE_VERSION = 1

FACTOR_RETRIEVER_IDS = [
    "bm25",
    "bm25_rm3",
    "bm25f",
    "chargram_bm25",
    "dense_chunked",
    "splade",
    "colbert",
    "bm25_ce",
    "dense_ce",
    "ce",
    "rrf_bm25_dense",
    "rrf_bm25_splade",
    "func",
]
FACTOR_RETRIEVER_ALIASES = {
    "splade_style": "splade",
    "colbert_style": "colbert",
    "bm25_rerank_ce": "bm25_ce",
    "dense_rerank_ce": "dense_ce",
    "bm25_dense_rrf": "rrf_bm25_dense",
    "bm25_splade_rrf": "rrf_bm25_splade",
}

TOOL_METHOD_IDS = [
    "bm25_tool",
    "bm25_ce_tool",
    "dense_tool",
    "func_emb_tool",
    "fuse_tool",
    "fuse_e_tool",
]
E1_METHODS = [
    "bm25_tool",
    "dense_tool",
    "bm25_ce_tool",
    "func_emb_tool",
    "fuse_tool",
]
E2_METHODS = [
    "bm25_tool",
    "fuse_tool",
    "fuse_e_tool",
]
E2_RETRIEVERS = ["bm25", "dense", "ce"]
E3_HIT_K_DEFAULT = [1, 2, 5, 10, 20, 50]
E4_METHODS = ["bm25_tool", "bm25_ce_tool", "func_emb_tool", "fuse_tool"]
E5_METHODS = ["bm25_tool", "bm25_ce_tool", "func_emb_tool", "fuse_tool"]
E1_METHOD_ALIASES = {
    "bm25": "bm25_tool",
    "bm25_ce": "bm25_ce_tool",
    "bm25_rerank_ce": "bm25_ce_tool",
    "bm25->ce": "bm25_ce_tool",
    "dense": "dense_tool",
    "func": "func_emb_tool",
    "function": "func_emb_tool",
    "fuse": "fuse_tool",
    "fuse_gate": "fuse_tool",
    "fuse_hybrid": "fuse_tool",
    "fuse_bm25_gate": "fuse_tool",
    "fuse_bm25_gate_tool": "fuse_tool",
    # FUSE-E: gate disabled (packed-surrogate dense retrieval only).
    "fuse_e": "fuse_e_tool",
    "fuse-e": "fuse_e_tool",
    "fuse_e_tool": "fuse_e_tool",
    "fuse_e_ablate": "fuse_e_tool",
    "fuse_ablate": "fuse_e_tool",
    "fuse_ablate_tool": "fuse_e_tool",
    "fuse_nogate": "fuse_e_tool",
    "fuse_no_gate": "fuse_e_tool",
    "fuse_nobm25": "fuse_e_tool",
    "fuse_no_bm25": "fuse_e_tool",
}
E2_RETRIEVER_ALIASES = {
    "dense_chunked": "dense",
    "bm25_ce": "ce",
    "cross_encoder": "ce",
}
E2_RETRIEVER_INTERNAL = {
    "bm25": "bm25",
    "dense": "dense_chunked",
    "ce": "ce",
}

DEFAULT_TEXT_MODE = "norm"
DEFAULT_LOCAL_FILES_ONLY = True

DEFAULT_RM3_FB_DOCS = 15
DEFAULT_RM3_FB_TERMS = 25
DEFAULT_RM3_ORIG_WEIGHT = 0.6

DEFAULT_BM25F_NAME_WEIGHT = 2.0
DEFAULT_BM25F_STRING_WEIGHT = 1.0
DEFAULT_BM25F_K1 = 1.2
DEFAULT_BM25F_B_NAME = 0.75
DEFAULT_BM25F_B_STRING = 0.75

DEFAULT_CHARGRAM_MIN_N = 3
DEFAULT_CHARGRAM_MAX_N = 5

DEFAULT_SPLADE_MODEL_ID = "bert-base-uncased"
DEFAULT_SPLADE_MAX_LENGTH = 256
DEFAULT_SPLADE_DOC_TOP_TERMS = 256
DEFAULT_SPLADE_QUERY_TOP_TERMS = 64

DEFAULT_DENSE_MODEL_ID = "sentence-transformers/all-MiniLM-L6-v2"
DEFAULT_DENSE_CHUNK_TOKENS = 128
DEFAULT_DENSE_CHUNK_OVERLAP = 32

DEFAULT_COLBERT_MODEL_ID = "sentence-transformers/all-MiniLM-L6-v2"
DEFAULT_COLBERT_MAX_LENGTH = 256
DEFAULT_COLBERT_DOC_TOKEN_CAP = 384

DEFAULT_RERANK_MODEL_ID = "cross-encoder/ms-marco-MiniLM-L-6-v2"
DEFAULT_RERANK_CANDIDATE_KS = "50"
DEFAULT_RERANK_EVAL_K = 50

DEFAULT_RRF_K = 60

_SENTENCE_MODEL_CACHE: Dict[Tuple[str, bool], Any] = {}
_CROSS_ENCODER_CACHE: Dict[Tuple[str, bool], Any] = {}
_HF_TOKENIZER_CACHE: Dict[Tuple[str, bool], Any] = {}
_HF_MODEL_CACHE: Dict[Tuple[str, str, bool], Any] = {}
_FACTORIZED_DOC_MEM_CACHE: Dict[str, Dict[str, str]] = {}
_FACTORIZED_DOC_META_MEM_CACHE: Dict[str, Dict[str, Any]] = {}
_FACTORIZED_INDEX_MEM_CACHE: Dict[str, Any] = {}


# ---------------------------------------------------------------------------
# Shared option/model/text helpers
# ---------------------------------------------------------------------------


def _as_bool(v: Any, default: bool) -> bool:
    if isinstance(v, bool):
        return v
    if v is None:
        return default
    s = str(v).strip().lower()
    if s in {"1", "true", "yes", "y", "on"}:
        return True
    if s in {"0", "false", "no", "n", "off"}:
        return False
    return default


def _as_int_opt(
    opts: Dict[str, Any],
    key: str,
    default: int,
    *,
    min_value: Optional[int] = None,
    max_value: Optional[int] = None,
) -> int:
    try:
        v = int(opts.get(key, default) or default)
    except Exception:
        v = int(default)
    if min_value is not None and v < min_value:
        v = int(min_value)
    if max_value is not None and v > max_value:
        v = int(max_value)
    return v


def _as_float_opt(
    opts: Dict[str, Any],
    key: str,
    default: float,
    *,
    min_value: Optional[float] = None,
    max_value: Optional[float] = None,
) -> float:
    try:
        v = float(opts.get(key, default) or default)
    except Exception:
        v = float(default)
    if min_value is not None and v < min_value:
        v = float(min_value)
    if max_value is not None and v > max_value:
        v = float(max_value)
    return v


def _safe_build_bm25(corpus: List[List[str]]) -> Any:
    if BM25Okapi is None or not corpus:
        return None
    # rank_bm25 fails when every document is empty (idf dictionary is empty).
    if not any(len(doc) > 0 for doc in corpus):
        return None
    try:
        return BM25Okapi(corpus)
    except ZeroDivisionError:
        return None


def _parse_int_csv(raw: str) -> List[int]:
    out: List[int] = []
    for tok in str(raw or "").split(","):
        tok = tok.strip()
        if not tok:
            continue
        try:
            val = int(tok)
        except Exception:
            continue
        if val > 0:
            out.append(val)
    return sorted(set(out))


def _parse_text_mode(opts: Dict[str, Any]) -> Tuple[Optional[str], Optional[str]]:
    text_mode = (
        str(opts.get("text_mode", DEFAULT_TEXT_MODE) or DEFAULT_TEXT_MODE)
        .strip()
        .lower()
    )
    if text_mode not in {"raw", "norm"}:
        return None, f"Invalid text_mode '{text_mode}'. Use one of: raw,norm."
    return text_mode, None


def _parse_methods_opt(
    opts: Dict[str, Any],
    *,
    default_methods: Sequence[str],
    allowed_methods: Sequence[str],
) -> Tuple[Optional[List[str]], Optional[str]]:
    allowed = list(allowed_methods)
    allowed_set = set(allowed)

    raw = str(opts.get("methods", "") or "").strip()
    if not raw:
        return list(default_methods), None

    tokens = [t.strip().lower() for t in raw.split(",") if t.strip()]
    expanded: List[str] = []
    for tok in tokens:
        if tok == "all":
            expanded.extend(allowed)
            continue
        expanded.append(METHOD_ALIASES.get(tok, tok))

    deduped: List[str] = []
    seen: Set[str] = set()
    for m in expanded:
        if m in seen:
            continue
        seen.add(m)
        deduped.append(m)

    unknown = [m for m in deduped if m not in allowed_set]
    if unknown:
        aliases = ",".join(sorted(METHOD_ALIASES.keys()))
        allowed_str = ",".join(allowed)
        return None, (
            f"Unknown methods: {','.join(unknown)}. "
            f"Allowed methods: {allowed_str}. Aliases: {aliases}. "
            "You can also use methods=all."
        )
    return deduped, None


def _parse_representation_ids_opt(
    opts: Dict[str, Any],
) -> Tuple[Optional[List[str]], Optional[str]]:
    raw = str(opts.get("representations", "") or "").strip().lower()
    if not raw:
        return list(REPRESENTATION_IDS), None

    toks = [t.strip() for t in raw.split(",") if t.strip()]
    expanded: List[str] = []
    for tok in toks:
        if tok == "all":
            expanded.extend(REPRESENTATION_IDS)
            continue
        expanded.append(REPRESENTATION_ALIASES.get(tok, tok))

    out: List[str] = []
    seen: Set[str] = set()
    for rep in expanded:
        if rep in seen:
            continue
        seen.add(rep)
        out.append(rep)

    unknown = [r for r in out if r not in set(REPRESENTATION_IDS)]
    if unknown:
        return (
            None,
            "Unknown representations: "
            + ",".join(unknown)
            + ". Allowed: "
            + ",".join(REPRESENTATION_IDS)
            + ". Aliases: "
            + ",".join(sorted(REPRESENTATION_ALIASES.keys()))
            + ".",
        )
    return out, None


def _parse_factorized_retriever_ids_opt(
    opts: Dict[str, Any],
) -> Tuple[Optional[List[str]], Optional[str]]:
    raw = str(opts.get("retrievers", "") or "").strip().lower()
    if not raw:
        return list(FACTOR_RETRIEVER_IDS), None

    toks = [t.strip() for t in raw.split(",") if t.strip()]
    expanded: List[str] = []
    for tok in toks:
        if tok == "all":
            expanded.extend(FACTOR_RETRIEVER_IDS)
            continue
        expanded.append(FACTOR_RETRIEVER_ALIASES.get(tok, tok))

    out: List[str] = []
    seen: Set[str] = set()
    for rid in expanded:
        if rid in seen:
            continue
        seen.add(rid)
        out.append(rid)

    unknown = [r for r in out if r not in set(FACTOR_RETRIEVER_IDS)]
    if unknown:
        return (
            None,
            "Unknown retrievers: "
            + ",".join(unknown)
            + ". Allowed: "
            + ",".join(FACTOR_RETRIEVER_IDS)
            + ". Aliases: "
            + ",".join(sorted(FACTOR_RETRIEVER_ALIASES.keys()))
            + ".",
        )
    return out, None


def _load_eval_inputs(
    opts: Dict[str, Any],
) -> Tuple[
    Optional[Dict[str, Dict[str, str]]], Optional[Dict[str, str]], Optional[str]
]:
    comp_path = opts.get("comp_path")
    prompt_path = opts.get("prompt_path")
    if not comp_path or not prompt_path:
        return None, None, "Provide comp_path and prompt_path."

    ground_truth = create_ground_truth(comp_path)
    try:
        prompt_map = json.loads(Path(prompt_path).read_text())
    except Exception as e:
        return None, None, f"Failed to load prompt_path JSON: {e}"
    if not isinstance(prompt_map, dict):
        return None, None, "prompt_path must map component -> prompt string."

    out: Dict[str, str] = {}
    for k, v in prompt_map.items():
        if isinstance(k, str) and isinstance(v, str):
            s = v.strip()
            if s:
                out[k] = s
    return ground_truth, out, None


def _tokens_for_text_mode(text: str, text_mode: str) -> List[str]:
    return _bm25_tokens_for_text(text, normalize=(text_mode == "norm"))


def _tokens_for_oid_text_mode(oid: str, text_mode: str) -> List[str]:
    return _bm25_tokens_for_oid(oid, normalize=(text_mode == "norm"))


def _strings_for_oid(oid: str) -> List[str]:
    raw = api.get_field("strings", oid, oid) or {}
    out: List[str] = []
    for s in raw.values():
        if isinstance(s, str):
            t = s.strip()
            if t:
                out.append(t)
    return out


def _document_text_from_tokens(tokens: Sequence[str]) -> str:
    if not tokens:
        return ""
    return " ".join(tokens)


def _document_text_for_oid(oid: str, text_mode: str) -> str:
    return _document_text_from_tokens(_tokens_for_oid_text_mode(oid, text_mode))


def _char_ngrams(tokens: Sequence[str], min_n: int, max_n: int) -> List[str]:
    grams: List[str] = []
    if min_n <= 0 or max_n < min_n:
        return grams
    for tok in tokens:
        t = tok.strip().lower()
        if not t:
            continue
        nmax = min(max_n, len(t))
        for n in range(min_n, nmax + 1):
            for i in range(0, len(t) - n + 1):
                grams.append(t[i : i + n])
    return grams


def _hash_items(items: Sequence[str]) -> str:
    h = hashlib.sha256()
    for item in sorted(items):
        h.update(item.encode("utf-8"))
        h.update(b"\n")
    return h.hexdigest()[:16]


def _cache_key_for_collection(
    *,
    method: str,
    cid: str,
    oids: Sequence[str],
    config: Dict[str, Any],
) -> str:
    cfg = json.dumps(config, sort_keys=True, separators=(",", ":"))
    cfg_hash = hashlib.sha256(cfg.encode("utf-8")).hexdigest()[:12]
    return f"{method}|cid={cid}|cfg={cfg_hash}|n={len(oids)}|{_hash_items(list(oids))}"


def _rep_query_text(query: str, rep: str) -> str:
    s = str(query or "").strip()
    if not s:
        return ""
    if rep == "r0_raw":
        return s
    toks = _bm25_tokens_for_text(s, normalize=True)
    return " ".join(toks).strip() or s


def _rep_config_from_opts(rep: str, rep_opts: Dict[str, Any]) -> Dict[str, Any]:
    if rep != "r2_packed":
        return {"representation": rep}
    return {
        "representation": rep,
        "pack_budget_tokens": int(rep_opts.get("pack_budget_tokens", 0) or 0),
        "cache_version": int(R2_PACKED_DOCS_CACHE_VERSION),
    }


def _build_docs_for_collection_with_timing(
    cid: str, rep: str, rep_opts: Dict[str, Any]
) -> Tuple[Optional[Dict[str, str]], Optional[Dict[str, Any]], Optional[str]]:
    if rep not in set(REPRESENTATION_IDS):
        return None, None, f"Unknown representation '{rep}'."

    exes = filter_executables(api.expand_oids(cid))
    rep_cfg = _rep_config_from_opts(rep, rep_opts)
    key = _cache_key_for_collection(
        method=f"{NAME}_factorized_docs_{rep}",
        cid=cid,
        oids=exes,
        config=rep_cfg,
    )

    if key in _FACTORIZED_DOC_MEM_CACHE and key in _FACTORIZED_DOC_META_MEM_CACHE:
        meta = dict(_FACTORIZED_DOC_META_MEM_CACHE[key])
        meta["cache_hit"] = True
        return dict(_FACTORIZED_DOC_MEM_CACHE[key]), meta, None

    cache_plugin = f"{NAME}_factorized_docs"
    try:
        cached = (
            api.local_retrieve(cache_plugin, key)
            if api.local_exists(cache_plugin, key)
            else None
        )
    except Exception:
        cached = None
    if isinstance(cached, dict):
        cached_docs = cached.get("docs")
        cached_oids = cached.get("oids")
        if (
            isinstance(cached_docs, dict)
            and isinstance(cached_oids, list)
            and cached_oids == exes
        ):
            docs = {str(k): str(v or "") for k, v in cached_docs.items()}
            for oid in exes:
                docs.setdefault(oid, "")
            meta = dict(cached.get("meta") or {})
            meta.update(
                {"cache_hit": True, "cache_key": key, "representation": rep, "cid": cid}
            )
            if rep == "r2_packed":
                empty = sum(
                    1 for oid in exes if not str(docs.get(oid) or "").strip()
                )
                if empty == len(exes) and len(exes) > 0:
                    # Old caches can be poisoned (all-empty packed docs). Treat as a cache miss.
                    logger.warning(
                        "Discarding cached packed docs (all empty): cid=%s key=%s", cid, key
                    )
                else:
                    _FACTORIZED_DOC_MEM_CACHE[key] = docs
                    _FACTORIZED_DOC_META_MEM_CACHE[key] = meta
                    return dict(docs), dict(meta), None
            else:
                _FACTORIZED_DOC_MEM_CACHE[key] = docs
                _FACTORIZED_DOC_META_MEM_CACHE[key] = meta
                return dict(docs), dict(meta), None

    t0 = time.perf_counter_ns()
    docs: Dict[str, str] = {}
    if rep == "r0_raw":
        for oid in exes:
            docs[oid] = " ".join(_strings_for_oid(oid)).strip()
    elif rep == "r1_norm":
        for oid in exes:
            docs[oid] = _document_text_from_tokens(
                _tokens_for_oid_text_mode(oid, "norm")
            )
    else:
        try:
            from oxide.modules.analyzers.fuse import module_interface as fuse_module
        except Exception as e:
            return None, None, f"Failed importing fuse packed-doc helpers: {e}"
        try:
            docs = fuse_module.build_packed_docs_for_oids(
                exes,
                pack_budget_tokens=int(rep_opts.get("pack_budget_tokens", 0) or 0),
            )
        except Exception as e:
            return None, None, f"Failed building packed docs: {e}"
        for oid in exes:
            docs.setdefault(oid, "")

    one_time_doc_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
    meta = {
        "cid": cid,
        "representation": rep,
        "cache_key": key,
        "cache_hit": False,
        "one_time_doc_ms": float(f"{one_time_doc_ms:.3f}"),
        "candidate_count": len(exes),
        "doc_count": len(docs),
        "rep_config": rep_cfg,
    }

    if rep == "r2_packed":
        empty = sum(1 for oid in exes if not str(docs.get(oid) or "").strip())
        if empty == len(exes) and len(exes) > 0:
            return (
                None,
                None,
                "Packed-doc representation produced all-empty documents; "
                "refusing to cache. (This usually means a poisoned cache was reused, "
                "strings extraction returned nothing, or packing filters are too strict.)",
            )

    _FACTORIZED_DOC_MEM_CACHE[key] = dict(docs)
    _FACTORIZED_DOC_META_MEM_CACHE[key] = dict(meta)
    try:
        api.local_store(
            cache_plugin,
            key,
            {
                "oids": list(exes),
                "docs": dict(docs),
                "meta": dict(meta),
            },
        )
    except Exception:
        pass
    return dict(docs), dict(meta), None


def build_docs_for_collection(
    cid: str, rep: str, rep_opts: Dict[str, Any]
) -> Dict[str, str]:
    docs, _, err = _build_docs_for_collection_with_timing(cid, rep, rep_opts)
    if err or docs is None:
        return {}
    return docs


def build_doc_for_oid(oid: str, rep: str, rep_opts: Dict[str, Any]) -> str:
    if rep not in set(REPRESENTATION_IDS):
        return ""
    cid = str(rep_opts.get("cid", "") or "").strip()
    if cid:
        docs = build_docs_for_collection(cid, rep, rep_opts)
        if oid in docs:
            return docs.get(oid, "")

    if rep == "r0_raw":
        return " ".join(_strings_for_oid(oid)).strip()
    if rep == "r1_norm":
        return _document_text_from_tokens(_tokens_for_oid_text_mode(oid, "norm"))

    try:
        from oxide.modules.analyzers.fuse import module_interface as fuse_module
    except Exception:
        return ""
    try:
        return str(
            fuse_module.build_packed_doc_for_oid(
                oid,
                pack_budget_tokens=int(rep_opts.get("pack_budget_tokens", 0) or 0),
            )
            or ""
        )
    except Exception:
        return ""


def _rank_from_oid_list(oid_list: Sequence[str], gold_oid: str) -> Optional[int]:
    try:
        return list(oid_list).index(gold_oid) + 1
    except ValueError:
        return None


def _metrics_from_rank_values(ranks: Sequence[int]) -> Dict[str, float]:
    n = len(ranks)
    if n <= 0:
        return {"P@1": 0.0, "Hit@2": 0.0, "Hit@5": 0.0, "MRR": 0.0, "Mean": 0.0}
    return {
        "P@1": sum(1 for r in ranks if r == 1) / n,
        "Hit@2": sum(1 for r in ranks if r <= 2) / n,
        "Hit@5": sum(1 for r in ranks if r <= 5) / n,
        "MRR": sum((1.0 / r) for r in ranks) / n,
        "Mean": sum(ranks) / n,
    }


def _safe_float(v: Any) -> Optional[float]:
    try:
        if v is None:
            return None
        return float(v)
    except Exception:
        return None


def _metric_delta(a: Optional[float], b: Optional[float]) -> Optional[float]:
    if a is None or b is None:
        return None
    return float(a - b)


def _fmt_num(v: Optional[float], digits: int = 4) -> str:
    if v is None:
        return "-"
    return f"{v:.{digits}f}"


def _build_compare_table(
    results: Dict[str, Any],
    *,
    reference_method: str = "paper_idf_pack_auto",
) -> Dict[str, Any]:
    ref = results.get(reference_method) if isinstance(results, dict) else None
    ref_metrics = (ref.get("global_metrics") or {}) if isinstance(ref, dict) else {}
    ref_mrr = _safe_float(ref_metrics.get("MRR"))
    ref_p1 = _safe_float(ref_metrics.get("P@1"))
    ref_ms = (
        _safe_float((ref or {}).get("avg_retrieval_ms"))
        if isinstance(ref, dict)
        else None
    )

    rows: List[Dict[str, Any]] = []
    md_lines = [
        "| method | status | MRR | dMRR_vs_ref | P@1 | dP@1_vs_ref | Hit@5 | Mean | avg_ms | speedup_vs_ref |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]

    for method, out in (results or {}).items():
        if not isinstance(out, dict):
            row = {
                "method": method,
                "status": "non_dict",
                "error": "Method output was not a dictionary.",
            }
            rows.append(row)
            md_lines.append(f"| {method} | non_dict | - | - | - | - | - | - | - | - |")
            continue

        err = out.get("error")
        if err:
            row = {"method": method, "status": "error", "error": str(err)}
            rows.append(row)
            md_lines.append(f"| {method} | error | - | - | - | - | - | - | - | - |")
            continue

        gm = out.get("global_metrics") or {}
        mrr = _safe_float(gm.get("MRR"))
        p1 = _safe_float(gm.get("P@1"))
        hit5 = _safe_float(gm.get("Hit@5"))
        mean = _safe_float(gm.get("Mean"))
        ms = _safe_float(out.get("avg_retrieval_ms"))

        status = "ok" if mrr is not None else "no_metrics"
        d_mrr = _metric_delta(mrr, ref_mrr)
        d_p1 = _metric_delta(p1, ref_p1)
        speedup = (
            (ref_ms / ms)
            if (ref_ms is not None and ms is not None and ms > 0.0)
            else None
        )

        row = {
            "method": method,
            "status": status,
            "global_metrics": {
                "MRR": mrr,
                "P@1": p1,
                "Hit@5": hit5,
                "Mean": mean,
            },
            "avg_retrieval_ms": ms,
            "delta_vs_reference": {
                "MRR": d_mrr,
                "P@1": d_p1,
            },
            "speedup_vs_reference": speedup,
        }
        rows.append(row)
        md_lines.append(
            "| "
            + method
            + " | "
            + status
            + " | "
            + _fmt_num(mrr)
            + " | "
            + _fmt_num(d_mrr)
            + " | "
            + _fmt_num(p1)
            + " | "
            + _fmt_num(d_p1)
            + " | "
            + _fmt_num(hit5)
            + " | "
            + _fmt_num(mean)
            + " | "
            + _fmt_num(ms, 3)
            + " | "
            + _fmt_num(speedup, 2)
            + " |"
        )

    return {
        "reference_method": reference_method,
        "reference_present": isinstance(ref, dict),
        "columns": [
            "method",
            "status",
            "MRR",
            "dMRR_vs_ref",
            "P@1",
            "dP@1_vs_ref",
            "Hit@5",
            "Mean",
            "avg_ms",
            "speedup_vs_ref",
        ],
        "rows": rows,
        "markdown": "\n".join(md_lines),
    }


def _run_batch_from_ranker(
    *,
    toolset: str,
    top_k_files: int,
    ground_truth: Dict[str, Dict[str, str]],
    prompt_map: Dict[str, str],
    ranker: Callable[[str, str, int], Dict[str, Any]],
    extra_payload: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    per_collection: Dict[str, Any] = {}
    attempted = 0
    sum_p1 = 0
    sum_h2 = 0
    sum_h5 = 0
    sum_mrr = 0.0
    sum_rank_effort = 0.0
    total_ms = 0.0
    total_tool_calls = 0.0

    for cid, golds in ground_truth.items():
        colname = api.get_colname_from_oid(cid)
        ranks_by_component: Dict[str, Optional[int]] = {}
        attempted_here = 0

        for comp, gold_oid in golds.items():
            prompt = prompt_map.get(comp)
            if not prompt:
                ranks_by_component[comp] = None
                continue

            out = ranker(cid, prompt, top_k_files)
            if not isinstance(out, dict) or not out.get("evaluated", False):
                ranks_by_component[comp] = None
                continue

            oid_list = out.get("oid_list") or []
            if not isinstance(oid_list, list):
                oid_list = []

            attempted += 1
            attempted_here += 1
            total_ms += float(out.get("elapsed_ms", 0.0) or 0.0)
            total_tool_calls += float(out.get("tool_calls", 1.0) or 1.0)

            rank = _rank_from_oid_list(oid_list, gold_oid)
            ranks_by_component[comp] = rank
            if rank is not None:
                sum_p1 += int(rank == 1)
                sum_h2 += int(rank <= 2)
                sum_h5 += int(rank <= 5)
                sum_mrr += 1.0 / rank
                sum_rank_effort += rank
            else:
                sum_rank_effort += top_k_files + 1

        if attempted_here > 0:
            p1 = sum(1 for r in ranks_by_component.values() if r == 1) / attempted_here
            h2 = (
                sum(1 for r in ranks_by_component.values() if r is not None and r <= 2)
                / attempted_here
            )
            h5 = (
                sum(1 for r in ranks_by_component.values() if r is not None and r <= 5)
                / attempted_here
            )
            mrr = (
                sum((1.0 / r) for r in ranks_by_component.values() if r is not None)
                / attempted_here
            )
            mean_rank_effort = (
                sum(
                    (r if r is not None else (top_k_files + 1))
                    for r in ranks_by_component.values()
                )
                / attempted_here
            )
            per_collection[colname] = {
                "metrics": {
                    "P@1": p1,
                    "Hit@2": h2,
                    "Hit@5": h5,
                    "MRR": mrr,
                    "mean_rank": mean_rank_effort,
                },
                "ranks_by_prompt": ranks_by_component,
            }
        else:
            per_collection[colname] = {
                "metrics": {},
                "ranks_by_prompt": ranks_by_component,
            }

    if attempted == 0:
        return {"error": f"No prompts evaluated for {toolset} baseline."}

    avg_ms = total_ms / max(attempted, 1)
    avg_calls = total_tool_calls / max(attempted, 1)
    payload = {
        "toolset": toolset,
        "use_tags": False,
        "top_k_files": top_k_files,
        "per_collection": per_collection,
        "global_metrics": {
            "P@1": sum_p1 / attempted,
            "Hit@2": sum_h2 / attempted,
            "Hit@5": sum_h5 / attempted,
            "MRR": sum_mrr / attempted,
            "Mean": sum_rank_effort / attempted,
        },
        "avg_retrieval_time_ms": f"{avg_ms:.3f}",
        "avg_retrieval_ms": float(f"{avg_ms:.3f}"),
        "avg_tool_calls": float(f"{avg_calls:.3f}"),
        "attempted_queries": attempted,
    }
    if extra_payload:
        payload.update(extra_payload)
    return payload


def _require_numpy() -> Optional[str]:
    if np is None:
        return "numpy is not available; install numpy."
    return None


def _get_sentence_model(model_id: str, *, local_files_only: bool) -> Any:
    key = (model_id, bool(local_files_only))
    if key in _SENTENCE_MODEL_CACHE:
        return _SENTENCE_MODEL_CACHE[key]
    if SentenceTransformer is None:
        raise RuntimeError(
            "sentence_transformers is not available; install sentence-transformers."
        )
    try:
        mdl = SentenceTransformer(model_id, local_files_only=bool(local_files_only))
    except TypeError:
        mdl = SentenceTransformer(model_id)
    _SENTENCE_MODEL_CACHE[key] = mdl
    return mdl


def _get_cross_encoder(model_id: str, *, local_files_only: bool) -> Any:
    key = (model_id, bool(local_files_only))
    if key in _CROSS_ENCODER_CACHE:
        return _CROSS_ENCODER_CACHE[key]
    if CrossEncoder is None:
        raise RuntimeError(
            "sentence_transformers CrossEncoder is not available; install sentence-transformers."
        )
    try:
        ce = CrossEncoder(model_id, local_files_only=bool(local_files_only))
    except TypeError:
        ce = CrossEncoder(model_id)
    _CROSS_ENCODER_CACHE[key] = ce
    return ce


def _get_hf_tokenizer(model_id: str, *, local_files_only: bool) -> Any:
    key = (model_id, bool(local_files_only))
    if key in _HF_TOKENIZER_CACHE:
        return _HF_TOKENIZER_CACHE[key]
    if AutoTokenizer is None:
        raise RuntimeError(
            "transformers tokenizer is not available; install transformers."
        )
    tok = AutoTokenizer.from_pretrained(
        model_id, local_files_only=bool(local_files_only)
    )
    _HF_TOKENIZER_CACHE[key] = tok
    return tok


def _get_hf_model(
    model_id: str,
    *,
    mode: str,
    local_files_only: bool,
) -> Any:
    key = (model_id, mode, bool(local_files_only))
    if key in _HF_MODEL_CACHE:
        return _HF_MODEL_CACHE[key]
    if mode == "mlm":
        if AutoModelForMaskedLM is None:
            raise RuntimeError(
                "transformers AutoModelForMaskedLM is not available; install transformers."
            )
        model = AutoModelForMaskedLM.from_pretrained(
            model_id, local_files_only=bool(local_files_only)
        )
    else:
        if AutoModel is None:
            raise RuntimeError(
                "transformers AutoModel is not available; install transformers."
            )
        model = AutoModel.from_pretrained(
            model_id, local_files_only=bool(local_files_only)
        )
    model.eval()
    _HF_MODEL_CACHE[key] = model
    return model


# ---------------------------------------------------------------------------
# Exposed plugin functions
# ---------------------------------------------------------------------------


def agent_search(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Execute one retrieval query on one collection.

    args: [<cid>]
    opts:
      - query / query_path
      - toolset: optional, must be "fuse" if provided
      - top_k_files or top_k
      - string_emb_batch_size
      - debug_select
    """
    tool_err = _validate_toolset(opts)
    if tool_err:
        return {"error": tool_err}

    cid = _get_cid(args)
    query = _load_text_opt(opts, "query", "query_path")
    if not query:
        return {"error": "Provide query or query_path."}

    top_k_files = int(
        opts.get("top_k_files", opts.get("top_k", DEFAULT_TOP_K_FILES))
        or DEFAULT_TOP_K_FILES
    )
    paper_opts = _extract_paper_opts(opts)

    t0 = time.perf_counter_ns()
    out = _call_fuse(
        cid,
        query,
        top_k=top_k_files,
        fuse_opts=paper_opts,
    )
    ranked_files = _extract_file_candidates_from_fuse(out, top_k=top_k_files)
    elapsed_ms = (time.perf_counter_ns() - t0) / 1_000_000.0

    resp: Dict[str, Any] = {
        "cid": cid,
        "collection": api.get_colname_from_oid(cid),
        "query": query,
        "toolset": FUSE_TOOLSET,
        "use_tags": False,
        "tool_calls": 1.0,
        "elapsed_ms": float(f"{elapsed_ms:.3f}"),
        "results": {
            "best_match": ranked_files[0] if ranked_files else None,
            "candidates": ranked_files,
        },
        "trace": [
            {
                "tool": FUSE_TOOLSET,
                "top_k": top_k_files,
                "use_tags": False,
            }
        ],
    }

    if isinstance(out, dict):
        if "debug_select" in out:
            resp["debug_select"] = out["debug_select"]
        if "notes" in out:
            resp["notes"] = out["notes"]

    return resp


def agent_batch(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Batch evaluation for strings-only mode.

    opts:
      - comp_path: json mapping collection_name -> { component -> path(s) }
      - prompt_path: json mapping component -> prompt string
      - toolset: optional, must be "fuse" if provided
      - top_k_files
      - string_emb_batch_size
      - debug_select
    """
    tool_err = _validate_toolset(opts)
    if tool_err:
        return {"error": tool_err}

    comp_path = opts.get("comp_path")
    prompt_path = opts.get("prompt_path")
    if not comp_path or not prompt_path:
        return {"error": "Provide comp_path and prompt_path."}

    ground_truth = create_ground_truth(comp_path)

    try:
        prompt_map = json.loads(Path(prompt_path).read_text())
    except Exception as e:
        return {"error": f"Failed to load prompt_path JSON: {e}"}

    top_k_files = int(
        opts.get("top_k_files", DEFAULT_TOP_K_FILES) or DEFAULT_TOP_K_FILES
    )

    per_collection: Dict[str, Any] = {}

    attempted = 0
    sum_p1 = 0
    sum_h2 = 0
    sum_h5 = 0
    sum_mrr = 0.0
    sum_rank_effort = 0.0

    total_ms = 0.0
    total_tool_calls = 0.0

    for cid, golds in ground_truth.items():
        colname = api.get_colname_from_oid(cid)
        ranks_by_component: Dict[str, Optional[int]] = {}

        for comp, gold_oid in golds.items():
            prompt = prompt_map.get(comp)
            if not prompt:
                ranks_by_component[comp] = None
                continue

            search_opts = {
                "query": prompt,
                "toolset": FUSE_TOOLSET,
                "top_k_files": top_k_files,
                **_extract_paper_opts(opts),
            }
            out = agent_search([cid], search_opts)

            if isinstance(out, dict) and out.get("error"):
                ranks_by_component[comp] = None
                continue

            attempted += 1
            total_ms += float(out.get("elapsed_ms", 0.0))
            total_tool_calls += float(out.get("tool_calls", 0.0))

            cands = (out.get("results") or {}).get("candidates") or []
            oid_list = [c.get("oid") for c in cands if isinstance(c, dict)]

            try:
                rank = oid_list.index(gold_oid) + 1
            except ValueError:
                rank = None

            ranks_by_component[comp] = rank

            if rank is not None:
                sum_p1 += int(rank == 1)
                sum_h2 += int(rank <= 2)
                sum_h5 += int(rank <= 5)
                sum_mrr += 1.0 / rank
                sum_rank_effort += rank
            else:
                sum_rank_effort += top_k_files + 1

        attempted_here = len([p for p in golds.keys() if prompt_map.get(p)])
        if attempted_here > 0:
            p1 = sum(1 for r in ranks_by_component.values() if r == 1) / attempted_here
            h2 = (
                sum(1 for r in ranks_by_component.values() if r is not None and r <= 2)
                / attempted_here
            )
            h5 = (
                sum(1 for r in ranks_by_component.values() if r is not None and r <= 5)
                / attempted_here
            )
            mrr = (
                sum((1.0 / r) for r in ranks_by_component.values() if r)
                / attempted_here
            )
            mean_rank_effort = (
                sum(
                    (r if r is not None else (top_k_files + 1))
                    for r in ranks_by_component.values()
                )
                / attempted_here
            )

            per_collection[colname] = {
                "metrics": {
                    "P@1": p1,
                    "Hit@2": h2,
                    "Hit@5": h5,
                    "MRR": mrr,
                    "mean_rank": mean_rank_effort,
                },
                "ranks_by_prompt": ranks_by_component,
            }
        else:
            per_collection[colname] = {
                "metrics": {},
                "ranks_by_prompt": ranks_by_component,
            }

    if attempted == 0:
        return {
            "error": "No prompts evaluated (check comp_path/prompt_path alignment)."
        }

    global_metrics = {
        "P@1": sum_p1 / attempted,
        "Hit@2": sum_h2 / attempted,
        "Hit@5": sum_h5 / attempted,
        "MRR": sum_mrr / attempted,
        "Mean": sum_rank_effort / attempted,
    }

    avg_ms = total_ms / max(attempted, 1)
    avg_calls = total_tool_calls / max(attempted, 1)

    return {
        "toolset": FUSE_TOOLSET,
        "use_tags": False,
        "top_k_files": top_k_files,
        "per_collection": per_collection,
        "global_metrics": global_metrics,
        "avg_retrieval_time_ms": f"{avg_ms:.3f}",
        "avg_retrieval_ms": float(f"{avg_ms:.3f}"),
        "avg_tool_calls": float(f"{avg_calls:.3f}"),
        "attempted_queries": attempted,
    }


# Final exported command list is defined at end-of-file.
exports: List[Callable[..., Any]] = []


# ---------------------------------------------------------------------------
# Tool calls + result normalization
# ---------------------------------------------------------------------------


def _call_fuse(
    cid: str,
    query: str,
    top_k: int,
    fuse_opts: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    try:
        opts = {"prompt": query, "top_k": top_k}
        if fuse_opts:
            opts.update(fuse_opts)
        out = api.retrieve(FUSE_TOOLSET, [cid], opts)
        if isinstance(out, dict):
            return out
    except Exception:
        pass

    exes = filter_executables(api.expand_oids(cid))
    opts = {"prompt": query, "top_k": top_k}
    if fuse_opts:
        opts.update(fuse_opts)
    return api.retrieve(FUSE_TOOLSET, exes, opts)


def _extract_file_candidates_from_fuse(
    fuse_out: Dict[str, Any], top_k: int
) -> List[Dict[str, Any]]:
    cands = None
    if isinstance(fuse_out, dict):
        if "results" in fuse_out and isinstance(fuse_out["results"], dict):
            cands = fuse_out["results"].get("candidates")
        elif "results" in fuse_out and isinstance(fuse_out["results"], list):
            cands = fuse_out["results"]
        elif "candidates" in fuse_out:
            cands = fuse_out.get("candidates")

    if not cands:
        return []

    items = [c for c in cands if isinstance(c, dict) and "oid" in c]
    items.sort(key=lambda x: x.get("score", 0.0), reverse=True)
    return items[:top_k] if top_k > 0 else items


# ---------------------------------------------------------------------------
# Ground truth + utilities
# ---------------------------------------------------------------------------


def create_ground_truth(data_path: str) -> Dict[str, Dict[str, str]]:
    """
    Build mapping {cid: {component: oid}} by matching basenames from JSON to oid names.
    JSON shape: { collection_name: { component: [paths...] or path } }
    """
    data = json.loads(Path(data_path).read_text())

    ground_truth: Dict[str, Dict[str, str]] = {}
    for cid in api.collection_cids():
        c_name = api.get_colname_from_oid(cid)
        if c_name not in data:
            continue

        collection_data = data[c_name]
        basename_map: Dict[str, str] = {}

        for component, paths in collection_data.items():
            candidates = paths if isinstance(paths, list) else [paths]
            for p in candidates:
                basename_map[component] = Path(p).name

        exes = filter_executables(api.expand_oids(cid))
        ground_truth[cid] = build_col_gt(exes, basename_map)

    return ground_truth


def build_col_gt(exes: List[str], basename_map: Dict[str, str]) -> Dict[str, str]:
    col_gt: Dict[str, str] = {}
    for oid in exes:
        for name in api.get_names_from_oid(oid):
            match = next((c for c, f in basename_map.items() if f == name), None)
            if match is not None:
                col_gt[match] = oid
                break
    return col_gt


def filter_executables(oids: List[str]) -> List[str]:
    exes = []
    for oid in oids:
        cat = api.get_field("categorize", oid, oid)
        if cat != "executable":
            continue
        names = list(api.get_names_from_oid(oid))
        if any(ext in n for n in names for ext in (".so", ".ko")):
            continue
        exes.append(oid)
    return exes


def _get_cid(args: List[str]) -> str:
    cids, _ = api.valid_oids(args)
    if not cids:
        return args[0]
    return cids[0]


def _load_text_opt(opts: Dict[str, Any], key: str, key_path: str) -> str:
    s = (opts.get(key) or "").strip()
    p = (opts.get(key_path) or "").strip()
    if not s and p:
        try:
            s = Path(p).read_text(encoding="utf-8", errors="replace").strip()
        except Exception:
            return ""
    return s


def _extract_paper_opts(opts: Dict[str, Any]) -> Dict[str, Any]:
    return {k: opts[k] for k in PAPER_OPT_KEYS if k in opts}


def _write_json(outdir: Path, filename: str, payload: Dict[str, Any]) -> str:
    p = outdir / filename
    p.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    return str(p)


def _validate_toolset(opts: Dict[str, Any]) -> Optional[str]:
    toolset = (opts.get("toolset") or FUSE_TOOLSET).strip().lower()
    if toolset != FUSE_TOOLSET:
        return f"This plugin is fixed to fuse. Use toolset='{FUSE_TOOLSET}' (got '{toolset}')."
    return None


def _batch_function_embeddings(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    comp_path = opts.get("comp_path")
    prompt_path = opts.get("prompt_path")
    if not comp_path or not prompt_path:
        return {"error": "Provide comp_path and prompt_path."}

    ground_truth = create_ground_truth(comp_path)
    try:
        prompt_map = json.loads(Path(prompt_path).read_text())
    except Exception as e:
        return {"error": f"Failed to load prompt_path JSON: {e}"}

    top_k_files = int(
        opts.get("top_k_files", DEFAULT_TOP_K_FILES) or DEFAULT_TOP_K_FILES
    )
    top_k_funcs = int(opts.get("top_k_funcs", 1) or 1)
    if top_k_funcs <= 0:
        top_k_funcs = 1

    func_file_agg = (opts.get("func_file_agg") or "top1").strip().lower()
    if func_file_agg not in {"top1", "mean", "attn"}:
        func_file_agg = "top1"
    try:
        func_attn_tau = float(opts.get("func_attn_tau", 0.07) or 0.07)
    except Exception:
        func_attn_tau = 0.07
    if func_attn_tau <= 0:
        func_attn_tau = 0.07

    try:
        func_similarity_threshold = float(
            opts.get("func_similarity_threshold", 0.0) or 0.0
        )
    except Exception:
        func_similarity_threshold = 0.0
    if func_similarity_threshold < 0:
        func_similarity_threshold = 0.0

    per_collection: Dict[str, Any] = {}
    attempted = 0
    sum_p1 = 0
    sum_h2 = 0
    sum_h5 = 0
    sum_mrr = 0.0
    sum_rank_effort = 0.0
    total_ms = 0.0
    total_tool_calls = 0.0

    for cid, golds in ground_truth.items():
        colname = api.get_colname_from_oid(cid)
        exes = filter_executables(api.expand_oids(cid))
        ranks_by_component: Dict[str, Optional[int]] = {}
        attempted_here = 0

        for comp, gold_oid in golds.items():
            prompt = prompt_map.get(comp)
            if not prompt:
                ranks_by_component[comp] = None
                continue

            t0 = time.perf_counter_ns()
            qf_out = api.retrieve(
                "query_function",
                exes,
                {
                    "query": prompt,
                    "top_k": top_k_funcs,
                    "return_file_embeddings": True,
                    "file_agg": func_file_agg,
                    "attn_tau": func_attn_tau,
                    "timing": False,
                    "progress": False,
                },
            )
            ranked_files = _rank_files_from_qf_file_scores(
                qf_out,
                top_k_files=top_k_files,
                min_score=func_similarity_threshold,
            )
            if not ranked_files:
                ranked_files = _aggregate_functions_to_files(
                    qf_out, top_k_files=top_k_files
                )
            elapsed_ms = (time.perf_counter_ns() - t0) / 1_000_000.0

            attempted += 1
            attempted_here += 1
            total_ms += elapsed_ms
            total_tool_calls += 1.0

            oid_list = [r["oid"] for r in ranked_files]
            try:
                rank = oid_list.index(gold_oid) + 1
            except ValueError:
                rank = None

            ranks_by_component[comp] = rank
            if rank is not None:
                sum_p1 += int(rank == 1)
                sum_h2 += int(rank <= 2)
                sum_h5 += int(rank <= 5)
                sum_mrr += 1.0 / rank
                sum_rank_effort += rank
            else:
                sum_rank_effort += top_k_files + 1

        if attempted_here > 0:
            p1 = sum(1 for r in ranks_by_component.values() if r == 1) / attempted_here
            h2 = (
                sum(1 for r in ranks_by_component.values() if r is not None and r <= 2)
                / attempted_here
            )
            h5 = (
                sum(1 for r in ranks_by_component.values() if r is not None and r <= 5)
                / attempted_here
            )
            mrr = (
                sum((1.0 / r) for r in ranks_by_component.values() if r)
                / attempted_here
            )
            mean_rank_effort = (
                sum(
                    (r if r is not None else (top_k_files + 1))
                    for r in ranks_by_component.values()
                )
                / attempted_here
            )
            per_collection[colname] = {
                "metrics": {
                    "P@1": p1,
                    "Hit@2": h2,
                    "Hit@5": h5,
                    "MRR": mrr,
                    "mean_rank": mean_rank_effort,
                },
                "ranks_by_prompt": ranks_by_component,
            }
        else:
            per_collection[colname] = {
                "metrics": {},
                "ranks_by_prompt": ranks_by_component,
            }

    if attempted == 0:
        return {"error": "No prompts evaluated for function_embeddings baseline."}

    avg_ms = total_ms / max(attempted, 1)
    avg_calls = total_tool_calls / max(attempted, 1)
    return {
        "toolset": "function_embeddings",
        "use_tags": False,
        "top_k_files": top_k_files,
        "top_k_funcs": top_k_funcs,
        "func_file_agg": func_file_agg,
        "func_attn_tau": func_attn_tau,
        "func_similarity_threshold": func_similarity_threshold,
        "per_collection": per_collection,
        "global_metrics": {
            "P@1": sum_p1 / attempted,
            "Hit@2": sum_h2 / attempted,
            "Hit@5": sum_h5 / attempted,
            "MRR": sum_mrr / attempted,
            "Mean": sum_rank_effort / attempted,
        },
        "avg_retrieval_time_ms": f"{avg_ms:.3f}",
        "avg_retrieval_ms": float(f"{avg_ms:.3f}"),
        "avg_tool_calls": float(f"{avg_calls:.3f}"),
        "attempted_queries": attempted,
    }


def _build_bm25_index_for_text_mode(cid: str, *, text_mode: str) -> Dict[str, Any]:
    exes = filter_executables(api.expand_oids(cid))
    exe_oids: List[str] = []
    corpus: List[List[str]] = []
    for oid in exes:
        toks = _tokens_for_oid_text_mode(oid, text_mode)
        if toks:
            exe_oids.append(oid)
            corpus.append(toks)
    bm25 = _safe_build_bm25(corpus)
    return {"bm25": bm25, "exe_oids": exe_oids, "corpus": corpus}


def _rm3_expand_query_tokens(
    *,
    query_tokens: List[str],
    corpus: List[List[str]],
    scores: Sequence[float],
    fb_docs: int,
    fb_terms: int,
    orig_weight: float,
) -> List[str]:
    if not query_tokens or not corpus:
        return query_tokens

    idxs = sorted(range(len(scores)), key=lambda i: scores[i], reverse=True)[
        : max(1, fb_docs)
    ]
    term_scores: Dict[str, float] = defaultdict(float)
    for i in idxs:
        doc = corpus[i]
        if not doc:
            continue
        tf = Counter(doc)
        denom = float(len(doc))
        if denom <= 0.0:
            continue
        w = float(scores[i])
        for term, cnt in tf.items():
            term_scores[term] += w * (float(cnt) / denom)

    orig_set = set(query_tokens)
    fb_candidates = sorted(
        ((t, s) for t, s in term_scores.items() if t not in orig_set and s > 0),
        key=lambda x: (-x[1], x[0]),
    )[: max(1, fb_terms)]
    fb_terms_only = [t for t, _ in fb_candidates]

    ow = min(1.0, max(0.0, float(orig_weight)))
    fw = max(0.0, 1.0 - ow)
    orig_mult = max(1, int(round(ow * 10.0)))
    fb_mult = max(1, int(round(fw * 10.0))) if fb_terms_only else 0
    expanded = list(query_tokens) * orig_mult
    for t in fb_terms_only:
        expanded.extend([t] * fb_mult)
    return expanded if expanded else query_tokens


def _batch_bm25_rm3(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    if BM25Okapi is None:
        return {"error": "rank_bm25 is not available; install rank-bm25."}
    ground_truth, prompt_map, err = _load_eval_inputs(opts)
    if err:
        return {"error": err}
    if ground_truth is None or prompt_map is None:
        return {"error": "Failed to load evaluation inputs."}

    text_mode, text_mode_err = _parse_text_mode(opts)
    if text_mode_err:
        return {"error": text_mode_err}

    fb_docs = _as_int_opt(opts, "rm3_fb_docs", DEFAULT_RM3_FB_DOCS, min_value=1)
    fb_terms = _as_int_opt(opts, "rm3_fb_terms", DEFAULT_RM3_FB_TERMS, min_value=1)
    orig_weight = _as_float_opt(
        opts, "rm3_orig_weight", DEFAULT_RM3_ORIG_WEIGHT, min_value=0.0, max_value=1.0
    )
    top_k_files = _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)

    by_cid: Dict[str, Dict[str, Any]] = {
        cid: _build_bm25_index_for_text_mode(cid, text_mode=text_mode)
        for cid in ground_truth.keys()
    }

    def ranker(cid: str, prompt: str, top_k: int) -> Dict[str, Any]:
        state = by_cid.get(cid) or {}
        bm25 = state.get("bm25")
        exe_oids = state.get("exe_oids") or []
        corpus = state.get("corpus") or []
        if bm25 is None or not exe_oids or not corpus:
            return {"evaluated": False}
        q_tokens = _tokens_for_text_mode(prompt, text_mode)
        if not q_tokens:
            return {"evaluated": False}
        t0 = time.perf_counter_ns()
        scores_1 = bm25.get_scores(q_tokens)
        q_rm3 = _rm3_expand_query_tokens(
            query_tokens=q_tokens,
            corpus=corpus,
            scores=scores_1,
            fb_docs=fb_docs,
            fb_terms=fb_terms,
            orig_weight=orig_weight,
        )
        scores_2 = bm25.get_scores(q_rm3)
        idxs = sorted(range(len(scores_2)), key=lambda i: scores_2[i], reverse=True)
        ranked = [exe_oids[i] for i in idxs[:top_k]]
        elapsed_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
        return {
            "evaluated": True,
            "oid_list": ranked,
            "elapsed_ms": elapsed_ms,
            "tool_calls": 1.0,
        }

    return _run_batch_from_ranker(
        toolset="bm25_rm3",
        top_k_files=top_k_files,
        ground_truth=ground_truth,
        prompt_map=prompt_map,
        ranker=ranker,
        extra_payload={
            "text_mode": text_mode,
            "rm3_fb_docs": fb_docs,
            "rm3_fb_terms": fb_terms,
            "rm3_orig_weight": orig_weight,
        },
    )


def _build_bm25f_index_for_text_mode(
    cid: str,
    *,
    text_mode: str,
) -> Dict[str, Any]:
    exes = filter_executables(api.expand_oids(cid))
    docs: List[Dict[str, Any]] = []
    df: Dict[str, int] = defaultdict(int)
    total_name_len = 0.0
    total_str_len = 0.0
    for oid in exes:
        name_tokens: List[str] = []
        for nm in api.get_names_from_oid(oid):
            if isinstance(nm, str):
                name_tokens.extend(_tokens_for_text_mode(nm, text_mode))
        str_tokens = _tokens_for_oid_text_mode(oid, text_mode)
        if not name_tokens and not str_tokens:
            continue
        name_tf = Counter(name_tokens)
        str_tf = Counter(str_tokens)
        total_name_len += len(name_tokens)
        total_str_len += len(str_tokens)
        docs.append(
            {
                "oid": oid,
                "name_tf": name_tf,
                "str_tf": str_tf,
                "name_len": len(name_tokens),
                "str_len": len(str_tokens),
            }
        )
        seen_terms = set(name_tf.keys()) | set(str_tf.keys())
        for t in seen_terms:
            df[t] += 1

    n_docs = len(docs)
    avg_name_len = (total_name_len / n_docs) if n_docs > 0 else 0.0
    avg_str_len = (total_str_len / n_docs) if n_docs > 0 else 0.0
    idf: Dict[str, float] = {}
    for t, d in df.items():
        idf[t] = math.log((n_docs - d + 0.5) / (d + 0.5) + 1.0)
    return {
        "docs": docs,
        "idf": idf,
        "avg_name_len": avg_name_len,
        "avg_str_len": avg_str_len,
    }


def _score_bm25f_doc(
    *,
    q_tf: Counter,
    doc: Dict[str, Any],
    idf: Dict[str, float],
    k1: float,
    b_name: float,
    b_str: float,
    name_weight: float,
    string_weight: float,
    avg_name_len: float,
    avg_str_len: float,
) -> float:
    score = 0.0
    name_tf: Counter = doc.get("name_tf") or Counter()
    str_tf: Counter = doc.get("str_tf") or Counter()
    name_len = float(doc.get("name_len") or 0.0)
    str_len = float(doc.get("str_len") or 0.0)
    name_norm_den = (1.0 - b_name) + b_name * (name_len / max(avg_name_len, 1e-6))
    str_norm_den = (1.0 - b_str) + b_str * (str_len / max(avg_str_len, 1e-6))
    for term, qcnt in q_tf.items():
        term_idf = idf.get(term)
        if term_idf is None:
            continue
        tf_name = float(name_tf.get(term, 0))
        tf_str = float(str_tf.get(term, 0))
        tf_mix = (name_weight * (tf_name / max(name_norm_den, 1e-6))) + (
            string_weight * (tf_str / max(str_norm_den, 1e-6))
        )
        if tf_mix <= 0.0:
            continue
        sat = ((k1 + 1.0) * tf_mix) / (k1 + tf_mix)
        score += float(qcnt) * term_idf * sat
    return score


def _batch_bm25f(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    ground_truth, prompt_map, err = _load_eval_inputs(opts)
    if err:
        return {"error": err}
    if ground_truth is None or prompt_map is None:
        return {"error": "Failed to load evaluation inputs."}

    text_mode, text_mode_err = _parse_text_mode(opts)
    if text_mode_err:
        return {"error": text_mode_err}
    top_k_files = _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
    name_weight = _as_float_opt(
        opts, "bm25f_name_weight", DEFAULT_BM25F_NAME_WEIGHT, min_value=0.0
    )
    string_weight = _as_float_opt(
        opts, "bm25f_string_weight", DEFAULT_BM25F_STRING_WEIGHT, min_value=0.0
    )
    k1 = _as_float_opt(opts, "bm25f_k1", DEFAULT_BM25F_K1, min_value=0.01)
    b_name = _as_float_opt(
        opts, "bm25f_b_name", DEFAULT_BM25F_B_NAME, min_value=0.0, max_value=1.0
    )
    b_str = _as_float_opt(
        opts, "bm25f_b_string", DEFAULT_BM25F_B_STRING, min_value=0.0, max_value=1.0
    )

    by_cid = {
        cid: _build_bm25f_index_for_text_mode(cid, text_mode=text_mode)
        for cid in ground_truth.keys()
    }

    def ranker(cid: str, prompt: str, top_k: int) -> Dict[str, Any]:
        st = by_cid.get(cid) or {}
        docs = st.get("docs") or []
        if not docs:
            return {"evaluated": False}
        q_tokens = _tokens_for_text_mode(prompt, text_mode)
        if not q_tokens:
            return {"evaluated": False}
        q_tf = Counter(q_tokens)
        t0 = time.perf_counter_ns()
        scored: List[Tuple[str, float]] = []
        for doc in docs:
            scored.append(
                (
                    doc["oid"],
                    _score_bm25f_doc(
                        q_tf=q_tf,
                        doc=doc,
                        idf=st.get("idf") or {},
                        k1=k1,
                        b_name=b_name,
                        b_str=b_str,
                        name_weight=name_weight,
                        string_weight=string_weight,
                        avg_name_len=float(st.get("avg_name_len") or 0.0),
                        avg_str_len=float(st.get("avg_str_len") or 0.0),
                    ),
                )
            )
        scored.sort(key=lambda x: x[1], reverse=True)
        ranked = [oid for oid, _ in scored[:top_k]]
        elapsed_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
        return {
            "evaluated": True,
            "oid_list": ranked,
            "elapsed_ms": elapsed_ms,
            "tool_calls": 1.0,
        }

    return _run_batch_from_ranker(
        toolset="bm25f",
        top_k_files=top_k_files,
        ground_truth=ground_truth,
        prompt_map=prompt_map,
        ranker=ranker,
        extra_payload={
            "text_mode": text_mode,
            "bm25f_name_weight": name_weight,
            "bm25f_string_weight": string_weight,
            "bm25f_k1": k1,
            "bm25f_b_name": b_name,
            "bm25f_b_string": b_str,
        },
    )


def _batch_chargram_bm25(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    if BM25Okapi is None:
        return {"error": "rank_bm25 is not available; install rank-bm25."}
    ground_truth, prompt_map, err = _load_eval_inputs(opts)
    if err:
        return {"error": err}
    if ground_truth is None or prompt_map is None:
        return {"error": "Failed to load evaluation inputs."}
    text_mode, text_mode_err = _parse_text_mode(opts)
    if text_mode_err:
        return {"error": text_mode_err}
    top_k_files = _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
    min_n = _as_int_opt(opts, "chargram_min_n", DEFAULT_CHARGRAM_MIN_N, min_value=1)
    max_n = _as_int_opt(opts, "chargram_max_n", DEFAULT_CHARGRAM_MAX_N, min_value=min_n)

    by_cid: Dict[str, Dict[str, Any]] = {}
    for cid in ground_truth.keys():
        exes = filter_executables(api.expand_oids(cid))
        exe_oids: List[str] = []
        corpus: List[List[str]] = []
        for oid in exes:
            toks = _tokens_for_oid_text_mode(oid, text_mode)
            grams = _char_ngrams(toks, min_n=min_n, max_n=max_n)
            if grams:
                exe_oids.append(oid)
                corpus.append(grams)
        bm25 = _safe_build_bm25(corpus)
        by_cid[cid] = {"bm25": bm25, "exe_oids": exe_oids}

    def ranker(cid: str, prompt: str, top_k: int) -> Dict[str, Any]:
        st = by_cid.get(cid) or {}
        bm25 = st.get("bm25")
        exe_oids = st.get("exe_oids") or []
        if bm25 is None or not exe_oids:
            return {"evaluated": False}
        q_tokens = _tokens_for_text_mode(prompt, text_mode)
        q_grams = _char_ngrams(q_tokens, min_n=min_n, max_n=max_n)
        if not q_grams:
            return {"evaluated": False}
        t0 = time.perf_counter_ns()
        scores = bm25.get_scores(q_grams)
        idxs = sorted(range(len(scores)), key=lambda i: scores[i], reverse=True)
        ranked = [exe_oids[i] for i in idxs[:top_k]]
        elapsed_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
        return {
            "evaluated": True,
            "oid_list": ranked,
            "elapsed_ms": elapsed_ms,
            "tool_calls": 1.0,
        }

    return _run_batch_from_ranker(
        toolset="chargram_bm25",
        top_k_files=top_k_files,
        ground_truth=ground_truth,
        prompt_map=prompt_map,
        ranker=ranker,
        extra_payload={
            "text_mode": text_mode,
            "chargram_min_n": min_n,
            "chargram_max_n": max_n,
        },
    )


def _rrf_fuse(
    rank_lists: Sequence[Sequence[str]], *, rrf_k: int, depth: int
) -> List[str]:
    scores: Dict[str, float] = defaultdict(float)
    for rank_list in rank_lists:
        for idx, oid in enumerate(list(rank_list)[: max(1, depth)], start=1):
            scores[oid] += 1.0 / float(max(1, rrf_k) + idx)
    return [oid for oid, _ in sorted(scores.items(), key=lambda x: (-x[1], x[0]))]


def _chunk_token_windows(
    tokens: Sequence[Any], chunk_size: int, overlap: int
) -> List[List[Any]]:
    if chunk_size <= 0:
        chunk_size = DEFAULT_DENSE_CHUNK_TOKENS
    overlap = max(0, min(overlap, chunk_size - 1))
    step = max(1, chunk_size - overlap)
    out: List[List[Any]] = []
    i = 0
    n = len(tokens)
    while i < n:
        chunk = list(tokens[i : i + chunk_size])
        if chunk:
            out.append(chunk)
        if i + chunk_size >= n:
            break
        i += step
    return out


def _token_ids_for_text_quiet(tokenizer: Any, text: str) -> List[int]:
    """
    Tokenize without emitting max-length warnings; caller handles chunking/truncation.
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
    except Exception:
        return []

    ids = enc.get("input_ids") if isinstance(enc, dict) else None
    if ids is None:
        return []
    if isinstance(ids, list) and ids and isinstance(ids[0], list):
        ids = ids[0]
    return list(ids) if isinstance(ids, list) else []


def _chunk_text_for_tokenizer(
    text: str,
    *,
    tokenizer: Any,
    chunk_tokens: int,
    chunk_overlap: int,
) -> List[str]:
    s = str(text or "").strip()
    if not s:
        return []

    # Fallback when a model tokenizer is unavailable.
    if tokenizer is None:
        pieces = _chunk_token_windows(s.split(), chunk_tokens, chunk_overlap)
        out = [" ".join(p) for p in pieces if p]
        return out if out else [s]

    token_ids = _token_ids_for_text_quiet(tokenizer, s)

    if not token_ids:
        pieces = _chunk_token_windows(s.split(), chunk_tokens, chunk_overlap)
        out = [" ".join(p) for p in pieces if p]
        return out if out else [s]

    id_windows = _chunk_token_windows(token_ids, chunk_tokens, chunk_overlap)
    out: List[str] = []
    for ids in id_windows:
        if not ids:
            continue
        piece = ""
        try:
            piece = str(
                tokenizer.decode(
                    ids,
                    skip_special_tokens=True,
                    clean_up_tokenization_spaces=True,
                )
                or ""
            ).strip()
        except Exception:
            piece = ""
        if not piece:
            try:
                toks = tokenizer.convert_ids_to_tokens(ids)
                piece = str(tokenizer.convert_tokens_to_string(toks) or "").strip()
            except Exception:
                piece = ""
        if piece:
            out.append(piece)

    return out if out else [s]


def _ensure_np_array(v: Any) -> Any:
    if np is None:
        return v
    if isinstance(v, np.ndarray):
        return v.astype(np.float32)
    return np.asarray(v, dtype=np.float32)


def _dot(a: Any, b: Any) -> float:
    if np is None:
        return 0.0
    return float(np.dot(a, b))


def _maxsim_score(query_tok_emb: Any, doc_tok_emb: Any) -> float:
    if np is None:
        return 0.0
    if (
        not isinstance(query_tok_emb, np.ndarray)
        or not isinstance(doc_tok_emb, np.ndarray)
        or query_tok_emb.size == 0
        or doc_tok_emb.size == 0
    ):
        return 0.0
    sims = query_tok_emb.dot(doc_tok_emb.T)
    if sims.size == 0:
        return 0.0
    return float(np.max(sims, axis=1).sum())


def _build_dense_engine(
    cids: Sequence[str], opts: Dict[str, Any], *, text_mode: str
) -> Tuple[Optional[Dict[str, Any]], Optional[Dict[str, Any]], Optional[str]]:
    dep_err = _require_numpy()
    if dep_err:
        return None, None, dep_err
    model_id = str(
        opts.get("dense_model_id", DEFAULT_DENSE_MODEL_ID) or DEFAULT_DENSE_MODEL_ID
    ).strip()
    local_files_only = _as_bool(
        opts.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY), DEFAULT_LOCAL_FILES_ONLY
    )
    chunk_tokens = _as_int_opt(
        opts, "dense_chunk_tokens", DEFAULT_DENSE_CHUNK_TOKENS, min_value=8
    )
    chunk_overlap = _as_int_opt(
        opts, "dense_chunk_overlap", DEFAULT_DENSE_CHUNK_OVERLAP, min_value=0
    )
    chunk_overlap = min(chunk_overlap, chunk_tokens - 1)
    try:
        model = _get_sentence_model(model_id, local_files_only=local_files_only)
    except Exception as e:
        return None, None, f"dense_chunked model load failed: {e}"

    by_cid: Dict[str, Any] = {}
    cache_plugin = f"{NAME}_dense_chunked"
    cfg = {
        "text_mode": text_mode,
        "dense_model_id": model_id,
        "dense_chunk_tokens": chunk_tokens,
        "dense_chunk_overlap": chunk_overlap,
    }
    for cid in cids:
        exes = filter_executables(api.expand_oids(cid))
        key = _cache_key_for_collection(
            method="dense_chunked", cid=cid, oids=exes, config=cfg
        )
        cached = (
            api.local_retrieve(cache_plugin, key)
            if api.local_exists(cache_plugin, key)
            else None
        )
        if isinstance(cached, dict) and cached.get("oids") == exes:
            by_cid[cid] = cached
            continue

        oid_texts: Dict[str, str] = {}
        owners: List[str] = []
        chunk_texts: List[str] = []
        for oid in exes:
            tokens = _tokens_for_oid_text_mode(oid, text_mode)
            oid_texts[oid] = _document_text_from_tokens(tokens)
            windows = _chunk_token_windows(tokens, chunk_tokens, chunk_overlap)
            if not windows and tokens:
                windows = [list(tokens)]
            for w in windows:
                if not w:
                    continue
                chunk_texts.append(" ".join(w))
                owners.append(oid)
        oid_chunks: Dict[str, Any] = {}
        if chunk_texts:
            embs = model.encode(
                chunk_texts,
                batch_size=32,
                show_progress_bar=False,
                normalize_embeddings=True,
            )
            embs = _ensure_np_array(embs)
            spans: Dict[str, List[Any]] = defaultdict(list)
            for i, oid in enumerate(owners):
                spans[oid].append(embs[i])
            for oid in exes:
                rows = spans.get(oid) or []
                if rows:
                    oid_chunks[oid] = _ensure_np_array(rows)
                else:
                    oid_chunks[oid] = _ensure_np_array(
                        np.zeros((0, embs.shape[1]), dtype=np.float32)
                    )
        else:
            dim = int(getattr(model, "get_sentence_embedding_dimension")())
            for oid in exes:
                oid_chunks[oid] = _ensure_np_array(np.zeros((0, dim), dtype=np.float32))
        blob = {"oids": exes, "oid_chunks": oid_chunks, "oid_texts": oid_texts}
        try:
            api.local_store(cache_plugin, key, blob)
        except Exception:
            pass
        by_cid[cid] = blob
    meta = {
        "dense_model_id": model_id,
        "dense_chunk_tokens": chunk_tokens,
        "dense_chunk_overlap": chunk_overlap,
        "local_files_only": local_files_only,
        "text_mode": text_mode,
        "model": model,
    }
    return by_cid, meta, None


def _dense_rank(
    *,
    state: Dict[str, Any],
    prompt: str,
    top_k_files: int,
    model: Any,
    text_mode: str,
) -> Dict[str, Any]:
    q_tokens = _tokens_for_text_mode(prompt, text_mode)
    if not q_tokens:
        return {"evaluated": False}
    q_text = _document_text_from_tokens(q_tokens)
    if not q_text:
        return {"evaluated": False}
    t0 = time.perf_counter_ns()
    q_vec = _ensure_np_array(
        model.encode(q_text, show_progress_bar=False, normalize_embeddings=True)
    )
    scored: List[Tuple[str, float]] = []
    for oid in state.get("oids") or []:
        emb = state.get("oid_chunks", {}).get(oid)
        if not isinstance(emb, np.ndarray) or emb.size == 0:
            scored.append((oid, -1e9))
            continue
        scored.append((oid, float(np.max(emb.dot(q_vec)))))
    scored.sort(key=lambda x: x[1], reverse=True)
    ranked = [oid for oid, _ in scored[:top_k_files]]
    elapsed_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
    return {
        "evaluated": True,
        "oid_list": ranked,
        "elapsed_ms": elapsed_ms,
        "tool_calls": 1.0,
    }


def _splade_encode_sparse(
    *,
    text: str,
    tokenizer: Any,
    model: Any,
    max_length: int,
    top_terms: int,
) -> Dict[int, float]:
    if torch is None:
        return {}
    if not text:
        return {}
    with torch.no_grad():
        inp = tokenizer(
            text,
            return_tensors="pt",
            truncation=True,
            max_length=max_length,
        )
        out = model(**inp)
        logits = out.logits.squeeze(0)
        attn = inp["attention_mask"].squeeze(0).unsqueeze(-1).float()
        scores = torch.log1p(torch.relu(logits)) * attn
        vec = torch.max(scores, dim=0).values
        if top_terms > 0 and vec.numel() > top_terms:
            vals, idx = torch.topk(vec, k=top_terms)
            keep = vals > 0
            idx = idx[keep]
            vals = vals[keep]
        else:
            idx = torch.nonzero(vec > 0, as_tuple=False).flatten()
            vals = vec[idx]
    return {int(i): float(v) for i, v in zip(idx.tolist(), vals.tolist())}


def _sparse_dot(q: Dict[int, float], d: Dict[int, float]) -> float:
    if len(q) > len(d):
        q, d = d, q
    s = 0.0
    for k, v in q.items():
        dv = d.get(k)
        if dv is not None:
            s += float(v) * float(dv)
    return s


def _build_splade_engine(
    cids: Sequence[str], opts: Dict[str, Any], *, text_mode: str
) -> Tuple[Optional[Dict[str, Any]], Optional[Dict[str, Any]], Optional[str]]:
    if torch is None or AutoTokenizer is None or AutoModelForMaskedLM is None:
        return None, None, "splade_style requires torch + transformers."
    model_id = str(
        opts.get("splade_model_id", DEFAULT_SPLADE_MODEL_ID) or DEFAULT_SPLADE_MODEL_ID
    ).strip()
    max_length = _as_int_opt(
        opts, "splade_max_length", DEFAULT_SPLADE_MAX_LENGTH, min_value=8
    )
    doc_top_terms = _as_int_opt(
        opts, "splade_doc_top_terms", DEFAULT_SPLADE_DOC_TOP_TERMS, min_value=8
    )
    query_top_terms = _as_int_opt(
        opts, "splade_query_top_terms", DEFAULT_SPLADE_QUERY_TOP_TERMS, min_value=4
    )
    local_files_only = _as_bool(
        opts.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY), DEFAULT_LOCAL_FILES_ONLY
    )
    try:
        tokenizer = _get_hf_tokenizer(model_id, local_files_only=local_files_only)
        model = _get_hf_model(model_id, mode="mlm", local_files_only=local_files_only)
    except Exception as e:
        return None, None, f"splade_style model load failed: {e}"

    by_cid: Dict[str, Any] = {}
    cache_plugin = f"{NAME}_splade_style"
    cfg = {
        "text_mode": text_mode,
        "splade_model_id": model_id,
        "splade_max_length": max_length,
        "splade_doc_top_terms": doc_top_terms,
    }
    for cid in cids:
        exes = filter_executables(api.expand_oids(cid))
        key = _cache_key_for_collection(
            method="splade_style", cid=cid, oids=exes, config=cfg
        )
        cached = (
            api.local_retrieve(cache_plugin, key)
            if api.local_exists(cache_plugin, key)
            else None
        )
        if isinstance(cached, dict) and cached.get("oids") == exes:
            by_cid[cid] = cached
            continue
        oid_sparse: Dict[str, Dict[int, float]] = {}
        oid_texts: Dict[str, str] = {}
        for oid in exes:
            text = _document_text_for_oid(oid, text_mode)
            oid_texts[oid] = text
            oid_sparse[oid] = _splade_encode_sparse(
                text=text,
                tokenizer=tokenizer,
                model=model,
                max_length=max_length,
                top_terms=doc_top_terms,
            )
        blob = {"oids": exes, "oid_sparse": oid_sparse, "oid_texts": oid_texts}
        try:
            api.local_store(cache_plugin, key, blob)
        except Exception:
            pass
        by_cid[cid] = blob
    meta = {
        "splade_model_id": model_id,
        "splade_max_length": max_length,
        "splade_doc_top_terms": doc_top_terms,
        "splade_query_top_terms": query_top_terms,
        "local_files_only": local_files_only,
        "text_mode": text_mode,
        "tokenizer": tokenizer,
        "model": model,
    }
    return by_cid, meta, None


def _splade_rank(
    *,
    state: Dict[str, Any],
    prompt: str,
    top_k_files: int,
    tokenizer: Any,
    model: Any,
    max_length: int,
    query_top_terms: int,
) -> Dict[str, Any]:
    t0 = time.perf_counter_ns()
    q_sparse = _splade_encode_sparse(
        text=prompt,
        tokenizer=tokenizer,
        model=model,
        max_length=max_length,
        top_terms=query_top_terms,
    )
    if not q_sparse:
        return {"evaluated": False}
    scored: List[Tuple[str, float]] = []
    for oid in state.get("oids") or []:
        d_sparse = (state.get("oid_sparse") or {}).get(oid) or {}
        scored.append((oid, _sparse_dot(q_sparse, d_sparse)))
    scored.sort(key=lambda x: x[1], reverse=True)
    ranked = [oid for oid, _ in scored[:top_k_files]]
    elapsed_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
    return {
        "evaluated": True,
        "oid_list": ranked,
        "elapsed_ms": elapsed_ms,
        "tool_calls": 1.0,
    }


def _colbert_encode_tokens(
    *,
    text: str,
    tokenizer: Any,
    model: Any,
    max_length: int,
    token_cap: int,
) -> Any:
    if np is None or torch is None:
        return None
    if not text:
        dim = int(getattr(model.config, "hidden_size", 384))
        return np.zeros((0, dim), dtype=np.float32)
    with torch.no_grad():
        inp = tokenizer(
            text,
            return_tensors="pt",
            truncation=True,
            max_length=max_length,
        )
        out = model(**inp)
        tok = out.last_hidden_state.squeeze(0)
        ids = inp["input_ids"].squeeze(0)
        mask = inp["attention_mask"].squeeze(0).bool()
        special_ids = set(getattr(tokenizer, "all_special_ids", []) or [])
        keep = mask.clone()
        for sid in special_ids:
            keep = keep & (ids != int(sid))
        tok = tok[keep]
        if token_cap > 0 and tok.shape[0] > token_cap:
            tok = tok[:token_cap]
        if tok.shape[0] == 0:
            dim = (
                int(tok.shape[1])
                if len(tok.shape) > 1
                else int(getattr(model.config, "hidden_size", 384))
            )
            return np.zeros((0, dim), dtype=np.float32)
        tok = torch.nn.functional.normalize(tok, p=2.0, dim=1)
    return tok.cpu().numpy().astype("float32")


def _build_colbert_engine(
    cids: Sequence[str], opts: Dict[str, Any], *, text_mode: str
) -> Tuple[Optional[Dict[str, Any]], Optional[Dict[str, Any]], Optional[str]]:
    dep_err = _require_numpy()
    if dep_err:
        return None, None, dep_err
    if torch is None or AutoTokenizer is None or AutoModel is None:
        return None, None, "colbert_style requires torch + transformers."
    model_id = str(
        opts.get("colbert_model_id", DEFAULT_COLBERT_MODEL_ID)
        or DEFAULT_COLBERT_MODEL_ID
    ).strip()
    max_length = _as_int_opt(
        opts, "colbert_max_length", DEFAULT_COLBERT_MAX_LENGTH, min_value=8
    )
    doc_token_cap = _as_int_opt(
        opts, "colbert_doc_token_cap", DEFAULT_COLBERT_DOC_TOKEN_CAP, min_value=16
    )
    local_files_only = _as_bool(
        opts.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY), DEFAULT_LOCAL_FILES_ONLY
    )
    try:
        tokenizer = _get_hf_tokenizer(model_id, local_files_only=local_files_only)
        model = _get_hf_model(model_id, mode="base", local_files_only=local_files_only)
    except Exception as e:
        return None, None, f"colbert_style model load failed: {e}"

    by_cid: Dict[str, Any] = {}
    cache_plugin = f"{NAME}_colbert_style"
    cfg = {
        "text_mode": text_mode,
        "colbert_model_id": model_id,
        "colbert_max_length": max_length,
        "colbert_doc_token_cap": doc_token_cap,
    }
    for cid in cids:
        exes = filter_executables(api.expand_oids(cid))
        key = _cache_key_for_collection(
            method="colbert_style", cid=cid, oids=exes, config=cfg
        )
        cached = (
            api.local_retrieve(cache_plugin, key)
            if api.local_exists(cache_plugin, key)
            else None
        )
        if isinstance(cached, dict) and cached.get("oids") == exes:
            by_cid[cid] = cached
            continue
        oid_tok_emb: Dict[str, Any] = {}
        oid_texts: Dict[str, str] = {}
        for oid in exes:
            text = _document_text_for_oid(oid, text_mode)
            oid_texts[oid] = text
            oid_tok_emb[oid] = _colbert_encode_tokens(
                text=text,
                tokenizer=tokenizer,
                model=model,
                max_length=max_length,
                token_cap=doc_token_cap,
            )
        blob = {"oids": exes, "oid_tok_emb": oid_tok_emb, "oid_texts": oid_texts}
        try:
            api.local_store(cache_plugin, key, blob)
        except Exception:
            pass
        by_cid[cid] = blob
    meta = {
        "colbert_model_id": model_id,
        "colbert_max_length": max_length,
        "colbert_doc_token_cap": doc_token_cap,
        "local_files_only": local_files_only,
        "text_mode": text_mode,
        "tokenizer": tokenizer,
        "model": model,
    }
    return by_cid, meta, None


def _colbert_rank(
    *,
    state: Dict[str, Any],
    prompt: str,
    top_k_files: int,
    tokenizer: Any,
    model: Any,
    max_length: int,
) -> Dict[str, Any]:
    q_emb = _colbert_encode_tokens(
        text=prompt,
        tokenizer=tokenizer,
        model=model,
        max_length=max_length,
        token_cap=0,
    )
    if not isinstance(q_emb, np.ndarray) or q_emb.size == 0:
        return {"evaluated": False}
    t0 = time.perf_counter_ns()
    scored: List[Tuple[str, float]] = []
    for oid in state.get("oids") or []:
        d_emb = (state.get("oid_tok_emb") or {}).get(oid)
        scored.append((oid, _maxsim_score(q_emb, d_emb)))
    scored.sort(key=lambda x: x[1], reverse=True)
    ranked = [oid for oid, _ in scored[:top_k_files]]
    elapsed_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
    return {
        "evaluated": True,
        "oid_list": ranked,
        "elapsed_ms": elapsed_ms,
        "tool_calls": 1.0,
    }


def _batch_dense_chunked(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    ground_truth, prompt_map, err = _load_eval_inputs(opts)
    if err:
        return {"error": err}
    if ground_truth is None or prompt_map is None:
        return {"error": "Failed to load evaluation inputs."}
    text_mode, text_mode_err = _parse_text_mode(opts)
    if text_mode_err:
        return {"error": text_mode_err}
    top_k_files = _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
    by_cid, meta, build_err = _build_dense_engine(
        list(ground_truth.keys()), opts, text_mode=text_mode
    )
    if build_err:
        return {"error": build_err}
    if by_cid is None or meta is None:
        return {"error": "Failed to build dense engine."}
    model = meta["model"]

    def ranker(cid: str, prompt: str, top_k: int) -> Dict[str, Any]:
        state = by_cid.get(cid) or {}
        if not state:
            return {"evaluated": False}
        return _dense_rank(
            state=state,
            prompt=prompt,
            top_k_files=top_k,
            model=model,
            text_mode=text_mode,
        )

    return _run_batch_from_ranker(
        toolset="dense_chunked",
        top_k_files=top_k_files,
        ground_truth=ground_truth,
        prompt_map=prompt_map,
        ranker=ranker,
        extra_payload={k: v for k, v in meta.items() if k != "model"},
    )


def _batch_splade_style(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    ground_truth, prompt_map, err = _load_eval_inputs(opts)
    if err:
        return {"error": err}
    if ground_truth is None or prompt_map is None:
        return {"error": "Failed to load evaluation inputs."}
    text_mode, text_mode_err = _parse_text_mode(opts)
    if text_mode_err:
        return {"error": text_mode_err}
    top_k_files = _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
    by_cid, meta, build_err = _build_splade_engine(
        list(ground_truth.keys()), opts, text_mode=text_mode
    )
    if build_err:
        return {"error": build_err}
    if by_cid is None or meta is None:
        return {"error": "Failed to build splade engine."}

    def ranker(cid: str, prompt: str, top_k: int) -> Dict[str, Any]:
        state = by_cid.get(cid) or {}
        if not state:
            return {"evaluated": False}
        return _splade_rank(
            state=state,
            prompt=prompt,
            top_k_files=top_k,
            tokenizer=meta["tokenizer"],
            model=meta["model"],
            max_length=int(meta["splade_max_length"]),
            query_top_terms=int(meta["splade_query_top_terms"]),
        )

    return _run_batch_from_ranker(
        toolset="splade_style",
        top_k_files=top_k_files,
        ground_truth=ground_truth,
        prompt_map=prompt_map,
        ranker=ranker,
        extra_payload={
            k: v for k, v in meta.items() if k not in {"tokenizer", "model"}
        },
    )


def _batch_colbert_style(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    ground_truth, prompt_map, err = _load_eval_inputs(opts)
    if err:
        return {"error": err}
    if ground_truth is None or prompt_map is None:
        return {"error": "Failed to load evaluation inputs."}
    text_mode, text_mode_err = _parse_text_mode(opts)
    if text_mode_err:
        return {"error": text_mode_err}
    top_k_files = _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
    by_cid, meta, build_err = _build_colbert_engine(
        list(ground_truth.keys()), opts, text_mode=text_mode
    )
    if build_err:
        return {"error": build_err}
    if by_cid is None or meta is None:
        return {"error": "Failed to build colbert engine."}

    def ranker(cid: str, prompt: str, top_k: int) -> Dict[str, Any]:
        state = by_cid.get(cid) or {}
        if not state:
            return {"evaluated": False}
        return _colbert_rank(
            state=state,
            prompt=prompt,
            top_k_files=top_k,
            tokenizer=meta["tokenizer"],
            model=meta["model"],
            max_length=int(meta["colbert_max_length"]),
        )

    return _run_batch_from_ranker(
        toolset="colbert_style",
        top_k_files=top_k_files,
        ground_truth=ground_truth,
        prompt_map=prompt_map,
        ranker=ranker,
        extra_payload={
            k: v for k, v in meta.items() if k not in {"tokenizer", "model"}
        },
    )


def _rerank_with_cross_encoder(
    *,
    cross_encoder: Any,
    prompt: str,
    candidate_oids: Sequence[str],
    oid_texts: Dict[str, str],
    oid_passages: Optional[Dict[str, List[str]]] = None,
    chunk_tokens: int = DEFAULT_DENSE_CHUNK_TOKENS,
    chunk_overlap: int = DEFAULT_DENSE_CHUNK_OVERLAP,
) -> List[str]:
    if not candidate_oids:
        return []
    if cross_encoder is None:
        return list(candidate_oids)

    tokenizer = getattr(cross_encoder, "tokenizer", None)
    pairs: List[Tuple[str, str]] = []
    owners: List[str] = []
    for oid in candidate_oids:
        passages = list((oid_passages or {}).get(oid) or [])
        if not passages:
            passages = _chunk_text_for_tokenizer(
                oid_texts.get(oid, ""),
                tokenizer=tokenizer,
                chunk_tokens=chunk_tokens,
                chunk_overlap=chunk_overlap,
            )
        if not passages:
            passages = [""]
        for p in passages:
            pairs.append((prompt, p))
            owners.append(oid)

    if not pairs:
        return list(candidate_oids)

    scores = cross_encoder.predict(pairs, batch_size=32, show_progress_bar=False)
    by_oid: Dict[str, float] = defaultdict(lambda: float("-inf"))
    for oid, s in zip(owners, scores):
        sc = float(s)
        if sc > by_oid[oid]:
            by_oid[oid] = sc

    scored = [(oid, by_oid.get(oid, float("-inf"))) for oid in candidate_oids]
    scored.sort(key=lambda x: x[1], reverse=True)
    return [oid for oid, _ in scored]


def _build_rerank_stage1_bm25(cids: Sequence[str], *, text_mode: str) -> Dict[str, Any]:
    return {
        cid: _build_bm25_index_for_text_mode(cid, text_mode=text_mode) for cid in cids
    }


def _stage1_bm25_rank(
    *,
    state: Dict[str, Any],
    prompt: str,
    top_k: int,
    text_mode: str,
) -> Dict[str, Any]:
    bm25 = state.get("bm25")
    exe_oids = state.get("exe_oids") or []
    if bm25 is None or not exe_oids:
        return {"evaluated": False}
    q_tokens = _tokens_for_text_mode(prompt, text_mode)
    if not q_tokens:
        return {"evaluated": False}
    t0 = time.perf_counter_ns()
    scores = bm25.get_scores(q_tokens)
    idxs = sorted(range(len(scores)), key=lambda i: scores[i], reverse=True)
    ranked = [exe_oids[i] for i in idxs[:top_k]]
    elapsed_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
    return {"evaluated": True, "oid_list": ranked, "elapsed_ms": elapsed_ms}


def _batch_rerank_ce(
    *,
    args: List[str],
    opts: Dict[str, Any],
    stage1_name: str,
) -> Dict[str, Any]:
    ground_truth, prompt_map, err = _load_eval_inputs(opts)
    if err:
        return {"error": err}
    if ground_truth is None or prompt_map is None:
        return {"error": "Failed to load evaluation inputs."}
    text_mode, text_mode_err = _parse_text_mode(opts)
    if text_mode_err:
        return {"error": text_mode_err}
    top_k_files = _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
    rerank_model_id = str(
        opts.get("rerank_model_id", DEFAULT_RERANK_MODEL_ID) or DEFAULT_RERANK_MODEL_ID
    ).strip()
    local_files_only = _as_bool(
        opts.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY), DEFAULT_LOCAL_FILES_ONLY
    )
    candidate_ks = _parse_int_csv(
        str(opts.get("rerank_candidate_ks", DEFAULT_RERANK_CANDIDATE_KS))
    )
    if not candidate_ks:
        candidate_ks = _parse_int_csv(DEFAULT_RERANK_CANDIDATE_KS)
    rerank_eval_k = _as_int_opt(
        opts, "rerank_eval_k", DEFAULT_RERANK_EVAL_K, min_value=1
    )
    if rerank_eval_k not in candidate_ks:
        candidate_ks = sorted(set(candidate_ks + [rerank_eval_k]))
    max_k = max(candidate_ks)

    try:
        ce = _get_cross_encoder(rerank_model_id, local_files_only=local_files_only)
    except Exception as e:
        return {"error": f"{stage1_name}_rerank_ce model load failed: {e}"}

    # Stage-1 build
    stage1_by_cid: Dict[str, Any] = {}
    oid_texts_by_cid: Dict[str, Dict[str, str]] = {}
    if stage1_name == "bm25":
        if BM25Okapi is None:
            return {"error": "rank_bm25 is not available; install rank-bm25."}
        stage1_by_cid = _build_rerank_stage1_bm25(
            list(ground_truth.keys()), text_mode=text_mode
        )
        for cid in ground_truth.keys():
            exes = (stage1_by_cid.get(cid) or {}).get("exe_oids") or []
            oid_texts_by_cid[cid] = {
                oid: _document_text_for_oid(oid, text_mode) for oid in exes
            }
    else:
        dense_by_cid, dense_meta, dense_err = _build_dense_engine(
            list(ground_truth.keys()), opts, text_mode=text_mode
        )
        if dense_err:
            return {"error": dense_err}
        if dense_by_cid is None or dense_meta is None:
            return {"error": "Failed building dense stage-1 engine."}
        stage1_by_cid = {"dense": dense_by_cid, "meta": dense_meta}
        for cid in ground_truth.keys():
            st = dense_by_cid.get(cid) or {}
            oid_texts_by_cid[cid] = dict((st.get("oid_texts") or {}))

    # Main accumulators for primary eval_k.
    per_collection: Dict[str, Any] = {}
    attempted = 0
    sum_p1 = 0
    sum_h2 = 0
    sum_h5 = 0
    sum_mrr = 0.0
    sum_rank_effort = 0.0
    total_ms = 0.0
    total_tool_calls = 0.0

    by_k: Dict[int, Dict[str, Any]] = {
        k: {
            "attempted": 0,
            "sum_p1": 0,
            "sum_h2": 0,
            "sum_h5": 0,
            "sum_mrr": 0.0,
            "sum_rank_effort": 0.0,
            "total_ms": 0.0,
        }
        for k in candidate_ks
    }

    for cid, golds in ground_truth.items():
        colname = api.get_colname_from_oid(cid)
        ranks_by_component: Dict[str, Optional[int]] = {}
        attempted_here = 0
        for comp, gold_oid in golds.items():
            prompt = prompt_map.get(comp)
            if not prompt:
                ranks_by_component[comp] = None
                continue

            # stage-1 candidates
            if stage1_name == "bm25":
                st = stage1_by_cid.get(cid) or {}
                out = _stage1_bm25_rank(
                    state=st,
                    prompt=prompt,
                    top_k=max_k,
                    text_mode=text_mode,
                )
            else:
                dense_state = (stage1_by_cid.get("dense") or {}).get(cid) or {}
                dense_model = (stage1_by_cid.get("meta") or {}).get("model")
                if dense_state and dense_model is not None:
                    out = _dense_rank(
                        state=dense_state,
                        prompt=prompt,
                        top_k_files=max_k,
                        model=dense_model,
                        text_mode=text_mode,
                    )
                else:
                    out = {"evaluated": False}
            if not out.get("evaluated", False):
                ranks_by_component[comp] = None
                continue

            stage1_oids = out.get("oid_list") or []
            if not stage1_oids:
                ranks_by_component[comp] = None
                continue

            attempted += 1
            attempted_here += 1
            total_tool_calls += 1.0

            rank_primary: Optional[int] = None
            for cand_k in candidate_ks:
                cands = list(stage1_oids[:cand_k])
                t0 = time.perf_counter_ns()
                reranked = _rerank_with_cross_encoder(
                    cross_encoder=ce,
                    prompt=prompt,
                    candidate_oids=cands,
                    oid_texts=oid_texts_by_cid.get(cid) or {},
                )
                elapsed_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
                st_k = by_k[cand_k]
                st_k["attempted"] += 1
                st_k["total_ms"] += elapsed_ms
                r = _rank_from_oid_list(reranked, gold_oid)
                if r is not None:
                    st_k["sum_p1"] += int(r == 1)
                    st_k["sum_h2"] += int(r <= 2)
                    st_k["sum_h5"] += int(r <= 5)
                    st_k["sum_mrr"] += 1.0 / r
                    st_k["sum_rank_effort"] += r
                else:
                    st_k["sum_rank_effort"] += top_k_files + 1
                if cand_k == rerank_eval_k:
                    rank_primary = r
                    total_ms += elapsed_ms

            ranks_by_component[comp] = rank_primary
            if rank_primary is not None:
                sum_p1 += int(rank_primary == 1)
                sum_h2 += int(rank_primary <= 2)
                sum_h5 += int(rank_primary <= 5)
                sum_mrr += 1.0 / rank_primary
                sum_rank_effort += rank_primary
            else:
                sum_rank_effort += top_k_files + 1

        if attempted_here > 0:
            p1 = sum(1 for r in ranks_by_component.values() if r == 1) / attempted_here
            h2 = (
                sum(1 for r in ranks_by_component.values() if r is not None and r <= 2)
                / attempted_here
            )
            h5 = (
                sum(1 for r in ranks_by_component.values() if r is not None and r <= 5)
                / attempted_here
            )
            mrr = (
                sum((1.0 / r) for r in ranks_by_component.values() if r is not None)
                / attempted_here
            )
            mean_rank = (
                sum(
                    (r if r is not None else (top_k_files + 1))
                    for r in ranks_by_component.values()
                )
                / attempted_here
            )
            per_collection[colname] = {
                "metrics": {
                    "P@1": p1,
                    "Hit@2": h2,
                    "Hit@5": h5,
                    "MRR": mrr,
                    "mean_rank": mean_rank,
                },
                "ranks_by_prompt": ranks_by_component,
            }
        else:
            per_collection[colname] = {
                "metrics": {},
                "ranks_by_prompt": ranks_by_component,
            }

    if attempted == 0:
        return {"error": f"No prompts evaluated for {stage1_name}_rerank_ce baseline."}

    by_k_payload: Dict[str, Any] = {}
    for k in candidate_ks:
        st = by_k[k]
        a = max(int(st["attempted"]), 1)
        by_k_payload[str(k)] = {
            "attempted_queries": int(st["attempted"]),
            "global_metrics": {
                "P@1": st["sum_p1"] / a,
                "Hit@2": st["sum_h2"] / a,
                "Hit@5": st["sum_h5"] / a,
                "MRR": st["sum_mrr"] / a,
                "Mean": st["sum_rank_effort"] / a,
            },
            "avg_retrieval_ms": float(f"{(st['total_ms'] / a):.3f}"),
        }

    avg_ms = total_ms / max(attempted, 1)
    avg_calls = total_tool_calls / max(attempted, 1)
    toolset = "bm25_rerank_ce" if stage1_name == "bm25" else "dense_rerank_ce"
    payload = {
        "toolset": toolset,
        "use_tags": False,
        "top_k_files": top_k_files,
        "per_collection": per_collection,
        "global_metrics": {
            "P@1": sum_p1 / attempted,
            "Hit@2": sum_h2 / attempted,
            "Hit@5": sum_h5 / attempted,
            "MRR": sum_mrr / attempted,
            "Mean": sum_rank_effort / attempted,
        },
        "avg_retrieval_time_ms": f"{avg_ms:.3f}",
        "avg_retrieval_ms": float(f"{avg_ms:.3f}"),
        "avg_tool_calls": float(f"{avg_calls:.3f}"),
        "attempted_queries": attempted,
        "text_mode": text_mode,
        "rerank_model_id": rerank_model_id,
        "rerank_candidate_ks": candidate_ks,
        "rerank_eval_k": rerank_eval_k,
        "by_candidate_k": by_k_payload,
        "local_files_only": local_files_only,
    }
    return payload


def _batch_bm25_rerank_ce(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    return _batch_rerank_ce(args=args, opts=opts, stage1_name="bm25")


def _batch_dense_rerank_ce(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    return _batch_rerank_ce(args=args, opts=opts, stage1_name="dense")


def _batch_bm25_dense_rrf(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    if BM25Okapi is None:
        return {"error": "rank_bm25 is not available; install rank-bm25."}
    ground_truth, prompt_map, err = _load_eval_inputs(opts)
    if err:
        return {"error": err}
    if ground_truth is None or prompt_map is None:
        return {"error": "Failed to load evaluation inputs."}
    text_mode, text_mode_err = _parse_text_mode(opts)
    if text_mode_err:
        return {"error": text_mode_err}
    top_k_files = _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
    rrf_k = _as_int_opt(opts, "rrf_k", DEFAULT_RRF_K, min_value=1)
    rrf_depth = _as_int_opt(opts, "rrf_depth", top_k_files, min_value=1)
    bm25_by_cid = {
        cid: _build_bm25_index_for_text_mode(cid, text_mode=text_mode)
        for cid in ground_truth.keys()
    }
    dense_by_cid, dense_meta, dense_err = _build_dense_engine(
        list(ground_truth.keys()), opts, text_mode=text_mode
    )
    if dense_err:
        return {"error": dense_err}
    if dense_by_cid is None or dense_meta is None:
        return {"error": "Failed building dense engine."}
    model = dense_meta["model"]

    def ranker(cid: str, prompt: str, top_k: int) -> Dict[str, Any]:
        bm25_state = bm25_by_cid.get(cid) or {}
        dense_state = dense_by_cid.get(cid) or {}
        out_b = _stage1_bm25_rank(
            state=bm25_state, prompt=prompt, top_k=rrf_depth, text_mode=text_mode
        )
        out_d = _dense_rank(
            state=dense_state,
            prompt=prompt,
            top_k_files=rrf_depth,
            model=model,
            text_mode=text_mode,
        )
        if not out_b.get("evaluated") and not out_d.get("evaluated"):
            return {"evaluated": False}
        t0 = time.perf_counter_ns()
        fused = _rrf_fuse(
            [
                out_b.get("oid_list") or [],
                out_d.get("oid_list") or [],
            ],
            rrf_k=rrf_k,
            depth=rrf_depth,
        )
        elapsed_ms = (
            float(out_b.get("elapsed_ms", 0.0) or 0.0)
            + float(out_d.get("elapsed_ms", 0.0) or 0.0)
            + (time.perf_counter_ns() - t0) / 1_000_000.0
        )
        return {
            "evaluated": True,
            "oid_list": fused[:top_k],
            "elapsed_ms": elapsed_ms,
            "tool_calls": 1.0,
        }

    return _run_batch_from_ranker(
        toolset="bm25_dense_rrf",
        top_k_files=top_k_files,
        ground_truth=ground_truth,
        prompt_map=prompt_map,
        ranker=ranker,
        extra_payload={
            "text_mode": text_mode,
            "rrf_k": rrf_k,
            "rrf_depth": rrf_depth,
            "dense_model_id": dense_meta.get("dense_model_id"),
        },
    )


def _batch_bm25_splade_rrf(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    if BM25Okapi is None:
        return {"error": "rank_bm25 is not available; install rank-bm25."}
    ground_truth, prompt_map, err = _load_eval_inputs(opts)
    if err:
        return {"error": err}
    if ground_truth is None or prompt_map is None:
        return {"error": "Failed to load evaluation inputs."}
    text_mode, text_mode_err = _parse_text_mode(opts)
    if text_mode_err:
        return {"error": text_mode_err}
    top_k_files = _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
    rrf_k = _as_int_opt(opts, "rrf_k", DEFAULT_RRF_K, min_value=1)
    rrf_depth = _as_int_opt(opts, "rrf_depth", top_k_files, min_value=1)
    bm25_by_cid = {
        cid: _build_bm25_index_for_text_mode(cid, text_mode=text_mode)
        for cid in ground_truth.keys()
    }
    splade_by_cid, splade_meta, splade_err = _build_splade_engine(
        list(ground_truth.keys()), opts, text_mode=text_mode
    )
    if splade_err:
        return {"error": splade_err}
    if splade_by_cid is None or splade_meta is None:
        return {"error": "Failed building splade engine."}

    def ranker(cid: str, prompt: str, top_k: int) -> Dict[str, Any]:
        bm25_state = bm25_by_cid.get(cid) or {}
        spl_state = splade_by_cid.get(cid) or {}
        out_b = _stage1_bm25_rank(
            state=bm25_state, prompt=prompt, top_k=rrf_depth, text_mode=text_mode
        )
        out_s = _splade_rank(
            state=spl_state,
            prompt=prompt,
            top_k_files=rrf_depth,
            tokenizer=splade_meta["tokenizer"],
            model=splade_meta["model"],
            max_length=int(splade_meta["splade_max_length"]),
            query_top_terms=int(splade_meta["splade_query_top_terms"]),
        )
        if not out_b.get("evaluated") and not out_s.get("evaluated"):
            return {"evaluated": False}
        t0 = time.perf_counter_ns()
        fused = _rrf_fuse(
            [out_b.get("oid_list") or [], out_s.get("oid_list") or []],
            rrf_k=rrf_k,
            depth=rrf_depth,
        )
        elapsed_ms = (
            float(out_b.get("elapsed_ms", 0.0) or 0.0)
            + float(out_s.get("elapsed_ms", 0.0) or 0.0)
            + (time.perf_counter_ns() - t0) / 1_000_000.0
        )
        return {
            "evaluated": True,
            "oid_list": fused[:top_k],
            "elapsed_ms": elapsed_ms,
            "tool_calls": 1.0,
        }

    return _run_batch_from_ranker(
        toolset="bm25_splade_rrf",
        top_k_files=top_k_files,
        ground_truth=ground_truth,
        prompt_map=prompt_map,
        ranker=ranker,
        extra_payload={
            "text_mode": text_mode,
            "rrf_k": rrf_k,
            "rrf_depth": rrf_depth,
            "splade_model_id": splade_meta.get("splade_model_id"),
        },
    )


def _time_breakdown_from_batch_output(
    toolset: str, batch_out: Dict[str, Any], *, top_k_files: int
) -> Dict[str, Any]:
    if not isinstance(batch_out, dict):
        return {"error": f"{toolset} batch output was not a dict."}
    if batch_out.get("error"):
        return {"error": batch_out.get("error")}
    attempted = int(batch_out.get("attempted_queries", 0) or 0)
    avg_ms = float(batch_out.get("avg_retrieval_ms", 0.0) or 0.0)
    retrieval_total = avg_ms * float(max(attempted, 0))
    per_collection_out: Dict[str, Any] = {}
    for colname, col in (batch_out.get("per_collection") or {}).items():
        ranks = (col or {}).get("ranks_by_prompt") or {}
        attempted_here = sum(1 for r in ranks.values() if r is not None)
        per_collection_out[colname] = {
            "one_time_ms": "0.000",
            "warmup_query_ms": "0.000",
            "retrieval_ms": f"{0.0:.3f}",
            "attempted_queries": attempted_here,
        }
    return {
        "toolset": toolset,
        "top_k_files": top_k_files,
        "attempted_queries": attempted,
        "one_time_processing_ms": f"{0.0:.3f}",
        "warmup_query_ms_total": f"{0.0:.3f}",
        "retrieval_only_ms_total": f"{retrieval_total:.3f}",
        "avg_retrieval_ms": f"{avg_ms:.3f}",
        "amortized_ms_per_query": f"{avg_ms:.3f}",
        "per_collection": per_collection_out,
    }


def _time_breakdown_bm25(
    ground_truth: Dict[str, Dict[str, str]],
    prompt_map: Dict[str, str],
    opts: Dict[str, Any],
    *,
    normalize: bool,
) -> Dict[str, Any]:
    if BM25Okapi is None:
        return {"error": "rank_bm25 is not available; install rank-bm25."}

    top_k_files = int(
        opts.get("top_k_files", DEFAULT_TOP_K_FILES) or DEFAULT_TOP_K_FILES
    )

    one_time_ms = 0.0
    warmup_query_ms_total = 0.0
    retrieval_ms = 0.0
    attempted = 0
    per_collection: Dict[str, Any] = {}

    for cid, golds in ground_truth.items():
        colname = api.get_colname_from_oid(cid)
        exes = filter_executables(api.expand_oids(cid))

        t0 = time.perf_counter_ns()
        exe_oids: List[str] = []
        corpus: List[List[str]] = []
        for oid in exes:
            toks = _bm25_tokens_for_oid(oid, normalize=normalize)
            if toks:
                exe_oids.append(oid)
                corpus.append(toks)
        bm25 = _safe_build_bm25(corpus)
        prep_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
        one_time_ms += prep_ms

        coll_attempted = 0
        coll_retrieval_ms = 0.0

        if bm25 is not None:
            for comp in golds.keys():
                prompt = prompt_map.get(comp)
                if not prompt:
                    continue
                q_tokens = _bm25_tokens_for_text(prompt, normalize=normalize)
                if not q_tokens:
                    continue

                t1 = time.perf_counter_ns()
                _ = bm25.get_scores(q_tokens)
                coll_retrieval_ms += (time.perf_counter_ns() - t1) / 1_000_000.0
                coll_attempted += 1
                attempted += 1

        retrieval_ms += coll_retrieval_ms
        per_collection[colname] = {
            "one_time_ms": f"{prep_ms:.3f}",
            "retrieval_ms": f"{coll_retrieval_ms:.3f}",
            "attempted_queries": coll_attempted,
        }

    avg_retrieval_ms = retrieval_ms / max(attempted, 1)
    amortized_ms = (one_time_ms + retrieval_ms) / max(attempted, 1)
    return {
        "toolset": "bm25_norm" if normalize else "bm25_raw",
        "top_k_files": top_k_files,
        "attempted_queries": attempted,
        "one_time_processing_ms": f"{one_time_ms:.3f}",
        "warmup_query_ms_total": f"{warmup_query_ms_total:.3f}",
        "retrieval_only_ms_total": f"{retrieval_ms:.3f}",
        "avg_retrieval_ms": f"{avg_retrieval_ms:.3f}",
        "amortized_ms_per_query": f"{amortized_ms:.3f}",
        "per_collection": per_collection,
    }


def _time_breakdown_function_embeddings(
    ground_truth: Dict[str, Dict[str, str]],
    prompt_map: Dict[str, str],
    opts: Dict[str, Any],
) -> Dict[str, Any]:
    top_k_files = int(
        opts.get("top_k_files", DEFAULT_TOP_K_FILES) or DEFAULT_TOP_K_FILES
    )
    top_k_funcs = int(opts.get("top_k_funcs", 1) or 1)
    if top_k_funcs <= 0:
        top_k_funcs = 1

    func_file_agg = (opts.get("func_file_agg") or "top1").strip().lower()
    if func_file_agg not in {"top1", "mean", "attn"}:
        func_file_agg = "top1"
    try:
        func_attn_tau = float(opts.get("func_attn_tau", 0.07) or 0.07)
    except Exception:
        func_attn_tau = 0.07
    if func_attn_tau <= 0:
        func_attn_tau = 0.07
    try:
        func_similarity_threshold = float(
            opts.get("func_similarity_threshold", 0.0) or 0.0
        )
    except Exception:
        func_similarity_threshold = 0.0
    if func_similarity_threshold < 0:
        func_similarity_threshold = 0.0

    one_time_ms = 0.0
    warmup_query_ms_total = 0.0
    retrieval_ms = 0.0
    attempted = 0
    per_collection: Dict[str, Any] = {}

    for cid, golds in ground_truth.items():
        colname = api.get_colname_from_oid(cid)
        exes = filter_executables(api.expand_oids(cid))
        prompts = [
            prompt_map.get(comp) for comp in golds.keys() if prompt_map.get(comp)
        ]

        prep_ms = 0.0
        warmup_query_ms = 0.0
        if exes and prompts:
            warm_prompt = prompts[0]
            t0 = time.perf_counter_ns()
            _ = api.retrieve(
                "query_function",
                exes,
                {
                    "query": warm_prompt,
                    "top_k": top_k_funcs,
                    "return_file_embeddings": True,
                    "file_agg": func_file_agg,
                    "attn_tau": func_attn_tau,
                    "timing": False,
                    "progress": False,
                    "rebuild": True,
                    "use_cache": True,
                },
            )
            prep_with_query_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
            t1 = time.perf_counter_ns()
            _ = api.retrieve(
                "query_function",
                exes,
                {
                    "query": warm_prompt,
                    "top_k": top_k_funcs,
                    "return_file_embeddings": True,
                    "file_agg": func_file_agg,
                    "attn_tau": func_attn_tau,
                    "timing": False,
                    "progress": False,
                    "rebuild": False,
                    "use_cache": True,
                },
            )
            warmup_query_ms = (time.perf_counter_ns() - t1) / 1_000_000.0
            prep_ms = max(0.0, prep_with_query_ms - warmup_query_ms)
        one_time_ms += prep_ms
        warmup_query_ms_total += warmup_query_ms

        coll_attempted = 0
        coll_retrieval_ms = 0.0
        if exes:
            for comp in golds.keys():
                prompt = prompt_map.get(comp)
                if not prompt:
                    continue
                t1 = time.perf_counter_ns()
                qf_out = api.retrieve(
                    "query_function",
                    exes,
                    {
                        "query": prompt,
                        "top_k": top_k_funcs,
                        "return_file_embeddings": True,
                        "file_agg": func_file_agg,
                        "attn_tau": func_attn_tau,
                        "timing": False,
                        "progress": False,
                        "rebuild": False,
                        "use_cache": True,
                    },
                )
                # Keep behavior aligned with function baseline path.
                ranked_files = _rank_files_from_qf_file_scores(
                    qf_out,
                    top_k_files=top_k_files,
                    min_score=func_similarity_threshold,
                )
                if not ranked_files:
                    ranked_files = _aggregate_functions_to_files(
                        qf_out, top_k_files=top_k_files
                    )
                _ = ranked_files
                coll_retrieval_ms += (time.perf_counter_ns() - t1) / 1_000_000.0
                coll_attempted += 1
                attempted += 1

        retrieval_ms += coll_retrieval_ms
        per_collection[colname] = {
            "one_time_ms": f"{prep_ms:.3f}",
            "warmup_query_ms": f"{warmup_query_ms:.3f}",
            "retrieval_ms": f"{coll_retrieval_ms:.3f}",
            "attempted_queries": coll_attempted,
        }

    avg_retrieval_ms = retrieval_ms / max(attempted, 1)
    amortized_ms = (one_time_ms + retrieval_ms) / max(attempted, 1)
    return {
        "toolset": "function_embeddings",
        "top_k_files": top_k_files,
        "top_k_funcs": top_k_funcs,
        "func_file_agg": func_file_agg,
        "func_attn_tau": func_attn_tau,
        "func_similarity_threshold": func_similarity_threshold,
        "attempted_queries": attempted,
        "one_time_processing_ms": f"{one_time_ms:.3f}",
        "warmup_query_ms_total": f"{warmup_query_ms_total:.3f}",
        "retrieval_only_ms_total": f"{retrieval_ms:.3f}",
        "avg_retrieval_ms": f"{avg_retrieval_ms:.3f}",
        "amortized_ms_per_query": f"{amortized_ms:.3f}",
        "per_collection": per_collection,
    }


def _time_breakdown_fuse(
    ground_truth: Dict[str, Dict[str, str]],
    prompt_map: Dict[str, str],
    opts: Dict[str, Any],
) -> Dict[str, Any]:
    top_k_files = int(
        opts.get("top_k_files", DEFAULT_TOP_K_FILES) or DEFAULT_TOP_K_FILES
    )
    paper_opts = _extract_paper_opts(opts)

    one_time_ms = 0.0
    warmup_query_ms_total = 0.0
    retrieval_ms = 0.0
    attempted = 0
    per_collection: Dict[str, Any] = {}

    for cid, golds in ground_truth.items():
        colname = api.get_colname_from_oid(cid)
        prompts = [
            prompt_map.get(comp) for comp in golds.keys() if prompt_map.get(comp)
        ]

        prep_ms = 0.0
        warmup_query_ms = 0.0
        if prompts:
            warm_prompt = prompts[0]
            t0 = time.perf_counter_ns()
            _ = _call_fuse(
                cid,
                warm_prompt,
                top_k=1,
                fuse_opts=paper_opts,
            )
            prep_with_query_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
            t1 = time.perf_counter_ns()
            _ = _call_fuse(
                cid,
                warm_prompt,
                top_k=1,
                fuse_opts=paper_opts,
            )
            warmup_query_ms = (time.perf_counter_ns() - t1) / 1_000_000.0
            prep_ms = max(0.0, prep_with_query_ms - warmup_query_ms)
        one_time_ms += prep_ms
        warmup_query_ms_total += warmup_query_ms

        coll_attempted = 0
        coll_retrieval_ms = 0.0
        for comp in golds.keys():
            prompt = prompt_map.get(comp)
            if not prompt:
                continue
            t1 = time.perf_counter_ns()
            _ = _call_fuse(
                cid,
                prompt,
                top_k=top_k_files,
                fuse_opts=paper_opts,
            )
            coll_retrieval_ms += (time.perf_counter_ns() - t1) / 1_000_000.0
            coll_attempted += 1
            attempted += 1

        retrieval_ms += coll_retrieval_ms
        per_collection[colname] = {
            "one_time_ms": f"{prep_ms:.3f}",
            "warmup_query_ms": f"{warmup_query_ms:.3f}",
            "retrieval_ms": f"{coll_retrieval_ms:.3f}",
            "attempted_queries": coll_attempted,
        }

    avg_retrieval_ms = retrieval_ms / max(attempted, 1)
    amortized_ms = (one_time_ms + retrieval_ms) / max(attempted, 1)
    return {
        "toolset": FUSE_TOOLSET,
        "top_k_files": top_k_files,
        "attempted_queries": attempted,
        "one_time_processing_ms": f"{one_time_ms:.3f}",
        "warmup_query_ms_total": f"{warmup_query_ms_total:.3f}",
        "retrieval_only_ms_total": f"{retrieval_ms:.3f}",
        "avg_retrieval_ms": f"{avg_retrieval_ms:.3f}",
        "amortized_ms_per_query": f"{amortized_ms:.3f}",
        "per_collection": per_collection,
    }


def _bm25_tokens_for_oid(oid: str, *, normalize: bool) -> List[str]:
    raw_strs = api.get_field("strings", oid, oid) or {}
    toks: List[str] = []
    for s in raw_strs.values():
        if not isinstance(s, str):
            continue
        if normalize:
            toks.extend(_bm25_tokens_for_text(s, normalize=True))
        else:
            toks.extend(_bm25_tokens_for_text(s, normalize=False))
    return toks


def _bm25_tokens_for_text(text: str, *, normalize: bool) -> List[str]:
    if not text:
        return []
    if not normalize:
        return [t.lower() for t in RAW_TERM.findall(text)]

    s = text.lower().strip()
    s = UUID_PAT.sub(" uuidtok ", s)
    s = HEX_PAT.sub(" hextok ", s)
    s = NUM_PAT.sub(" numtok ", s)
    s = re.sub(r"\s+", " ", s).strip()
    return [t for t in s.split() if PACK_TERM.fullmatch(t)]


def _aggregate_functions_to_files(
    qf_out: Dict[str, Any], top_k_files: int
) -> List[Dict[str, Any]]:
    funcs: List[Dict[str, Any]] = []
    if isinstance(qf_out, dict):
        res = qf_out.get("results")
        if isinstance(res, dict):
            cands = res.get("candidates")
            if isinstance(cands, list):
                funcs = [c for c in cands if isinstance(c, dict)]

    best_by_oid: Dict[str, Dict[str, Any]] = {}
    for f in funcs:
        oid = f.get("oid")
        score = f.get("score")
        if oid is None or score is None:
            continue
        prev = best_by_oid.get(oid)
        if prev is None or float(score) > float(prev["score"]):
            best_by_oid[oid] = {
                "oid": oid,
                "score": float(score),
                "names": list(api.get_names_from_oid(oid)),
            }

    ranked = sorted(best_by_oid.values(), key=lambda x: x["score"], reverse=True)
    return ranked[:top_k_files] if top_k_files > 0 else ranked


def _rank_files_from_qf_file_scores(
    qf_out: Dict[str, Any],
    *,
    top_k_files: int,
    min_score: float = 0.0,
) -> List[Dict[str, Any]]:
    """
    Build a file ranking from query_function file_scores.

    This mirrors function-search style behavior where each file is represented by
    an aggregate function signal (top1/mean/attn), configured upstream via
    return_file_embeddings + file_agg.
    """
    if not isinstance(qf_out, dict):
        return []
    fs = qf_out.get("file_scores")
    if not isinstance(fs, dict):
        return []

    ranked: List[Dict[str, Any]] = []
    for oid, score in fs.items():
        if score is None:
            continue
        sc = float(score)
        if sc < min_score:
            continue
        ranked.append(
            {
                "oid": oid,
                "score": sc,
                "names": list(api.get_names_from_oid(oid)),
            }
        )

    ranked.sort(key=lambda x: x["score"], reverse=True)
    return ranked[:top_k_files] if top_k_files > 0 else ranked


# ---------------------------------------------------------------------------
# Factorized evaluation (Representation x Retriever)
# ---------------------------------------------------------------------------


def _factorized_doc_tokens(doc_text: str, rep: str) -> List[str]:
    if rep == "r0_raw":
        return _bm25_tokens_for_text(doc_text, normalize=False)
    return _bm25_tokens_for_text(doc_text, normalize=True)


def _factorized_query_tokens(query: str, rep: str) -> List[str]:
    _ = rep
    return _bm25_tokens_for_text(query, normalize=False)


def _factorized_retriever_params(
    retriever: str, rep: str, opts: Dict[str, Any], *, top_k_files: int
) -> Dict[str, Any]:
    base: Dict[str, Any] = {"representation": rep, "top_k_files": top_k_files}
    if retriever == "bm25_rm3":
        base.update(
            {
                "rm3_fb_docs": _as_int_opt(
                    opts, "rm3_fb_docs", DEFAULT_RM3_FB_DOCS, min_value=1
                ),
                "rm3_fb_terms": _as_int_opt(
                    opts, "rm3_fb_terms", DEFAULT_RM3_FB_TERMS, min_value=1
                ),
                "rm3_orig_weight": _as_float_opt(
                    opts,
                    "rm3_orig_weight",
                    DEFAULT_RM3_ORIG_WEIGHT,
                    min_value=0.0,
                    max_value=1.0,
                ),
            }
        )
    elif retriever == "bm25f":
        base.update(
            {
                "bm25f_name_weight": _as_float_opt(
                    opts, "bm25f_name_weight", DEFAULT_BM25F_NAME_WEIGHT, min_value=0.0
                ),
                "bm25f_string_weight": _as_float_opt(
                    opts,
                    "bm25f_string_weight",
                    DEFAULT_BM25F_STRING_WEIGHT,
                    min_value=0.0,
                ),
                "bm25f_k1": _as_float_opt(
                    opts, "bm25f_k1", DEFAULT_BM25F_K1, min_value=0.01
                ),
                "bm25f_b_name": _as_float_opt(
                    opts,
                    "bm25f_b_name",
                    DEFAULT_BM25F_B_NAME,
                    min_value=0.0,
                    max_value=1.0,
                ),
                "bm25f_b_string": _as_float_opt(
                    opts,
                    "bm25f_b_string",
                    DEFAULT_BM25F_B_STRING,
                    min_value=0.0,
                    max_value=1.0,
                ),
            }
        )
    elif retriever == "chargram_bm25":
        base.update(
            {
                "chargram_min_n": _as_int_opt(
                    opts, "chargram_min_n", DEFAULT_CHARGRAM_MIN_N, min_value=1
                ),
                "chargram_max_n": _as_int_opt(
                    opts, "chargram_max_n", DEFAULT_CHARGRAM_MAX_N, min_value=1
                ),
            }
        )
    elif retriever == "dense_chunked":
        base.update(
            {
                "dense_model_id": str(
                    opts.get("dense_model_id", DEFAULT_DENSE_MODEL_ID)
                    or DEFAULT_DENSE_MODEL_ID
                ).strip(),
                "dense_chunk_tokens": _as_int_opt(
                    opts, "dense_chunk_tokens", DEFAULT_DENSE_CHUNK_TOKENS, min_value=8
                ),
                "dense_chunk_overlap": _as_int_opt(
                    opts,
                    "dense_chunk_overlap",
                    DEFAULT_DENSE_CHUNK_OVERLAP,
                    min_value=0,
                ),
                "local_files_only": _as_bool(
                    opts.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY),
                    DEFAULT_LOCAL_FILES_ONLY,
                ),
            }
        )
    elif retriever == "splade":
        base.update(
            {
                "splade_model_id": str(
                    opts.get("splade_model_id", DEFAULT_SPLADE_MODEL_ID)
                    or DEFAULT_SPLADE_MODEL_ID
                ).strip(),
                "splade_max_length": _as_int_opt(
                    opts, "splade_max_length", DEFAULT_SPLADE_MAX_LENGTH, min_value=8
                ),
                "splade_doc_top_terms": _as_int_opt(
                    opts,
                    "splade_doc_top_terms",
                    DEFAULT_SPLADE_DOC_TOP_TERMS,
                    min_value=8,
                ),
                "splade_query_top_terms": _as_int_opt(
                    opts,
                    "splade_query_top_terms",
                    DEFAULT_SPLADE_QUERY_TOP_TERMS,
                    min_value=4,
                ),
                "local_files_only": _as_bool(
                    opts.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY),
                    DEFAULT_LOCAL_FILES_ONLY,
                ),
            }
        )
    elif retriever == "colbert":
        base.update(
            {
                "colbert_model_id": str(
                    opts.get("colbert_model_id", DEFAULT_COLBERT_MODEL_ID)
                    or DEFAULT_COLBERT_MODEL_ID
                ).strip(),
                "colbert_max_length": _as_int_opt(
                    opts, "colbert_max_length", DEFAULT_COLBERT_MAX_LENGTH, min_value=8
                ),
                "colbert_doc_token_cap": _as_int_opt(
                    opts,
                    "colbert_doc_token_cap",
                    DEFAULT_COLBERT_DOC_TOKEN_CAP,
                    min_value=16,
                ),
                "local_files_only": _as_bool(
                    opts.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY),
                    DEFAULT_LOCAL_FILES_ONLY,
                ),
            }
        )
    elif retriever in {"bm25_ce", "dense_ce"}:
        cand_ks = _parse_int_csv(
            str(opts.get("rerank_candidate_ks", DEFAULT_RERANK_CANDIDATE_KS))
        )
        if not cand_ks:
            cand_ks = _parse_int_csv(DEFAULT_RERANK_CANDIDATE_KS)
        eval_k = _as_int_opt(opts, "rerank_eval_k", DEFAULT_RERANK_EVAL_K, min_value=1)
        if eval_k not in cand_ks:
            cand_ks = sorted(set(cand_ks + [eval_k]))
        base.update(
            {
                "rerank_model_id": str(
                    opts.get("rerank_model_id", DEFAULT_RERANK_MODEL_ID)
                    or DEFAULT_RERANK_MODEL_ID
                ).strip(),
                "rerank_candidate_ks": cand_ks,
                "rerank_eval_k": eval_k,
                "local_files_only": _as_bool(
                    opts.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY),
                    DEFAULT_LOCAL_FILES_ONLY,
                ),
                "dense_chunk_tokens": _as_int_opt(
                    opts,
                    "dense_chunk_tokens",
                    DEFAULT_DENSE_CHUNK_TOKENS,
                    min_value=8,
                ),
                "dense_chunk_overlap": _as_int_opt(
                    opts,
                    "dense_chunk_overlap",
                    DEFAULT_DENSE_CHUNK_OVERLAP,
                    min_value=0,
                ),
            }
        )
        if retriever == "dense_ce":
            base.update(
                {
                    "dense_model_id": str(
                        opts.get("dense_model_id", DEFAULT_DENSE_MODEL_ID)
                        or DEFAULT_DENSE_MODEL_ID
                    ).strip(),
                }
            )
    elif retriever == "ce":
        base.update(
            {
                "rerank_model_id": str(
                    opts.get("rerank_model_id", DEFAULT_RERANK_MODEL_ID)
                    or DEFAULT_RERANK_MODEL_ID
                ).strip(),
                "local_files_only": _as_bool(
                    opts.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY),
                    DEFAULT_LOCAL_FILES_ONLY,
                ),
                "dense_chunk_tokens": _as_int_opt(
                    opts,
                    "dense_chunk_tokens",
                    DEFAULT_DENSE_CHUNK_TOKENS,
                    min_value=8,
                ),
                "dense_chunk_overlap": _as_int_opt(
                    opts,
                    "dense_chunk_overlap",
                    DEFAULT_DENSE_CHUNK_OVERLAP,
                    min_value=0,
                ),
            }
        )
    elif retriever in {"rrf_bm25_dense", "rrf_bm25_splade"}:
        base.update(
            {
                "rrf_k": _as_int_opt(opts, "rrf_k", DEFAULT_RRF_K, min_value=1),
                "rrf_depth": _as_int_opt(opts, "rrf_depth", top_k_files, min_value=1),
            }
        )
        if retriever == "rrf_bm25_dense":
            base.update(
                {
                    "dense_model_id": str(
                        opts.get("dense_model_id", DEFAULT_DENSE_MODEL_ID)
                        or DEFAULT_DENSE_MODEL_ID
                    ).strip(),
                    "dense_chunk_tokens": _as_int_opt(
                        opts,
                        "dense_chunk_tokens",
                        DEFAULT_DENSE_CHUNK_TOKENS,
                        min_value=8,
                    ),
                    "dense_chunk_overlap": _as_int_opt(
                        opts,
                        "dense_chunk_overlap",
                        DEFAULT_DENSE_CHUNK_OVERLAP,
                        min_value=0,
                    ),
                    "local_files_only": _as_bool(
                        opts.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY),
                        DEFAULT_LOCAL_FILES_ONLY,
                    ),
                }
            )
        else:
            base.update(
                {
                    "splade_model_id": str(
                        opts.get("splade_model_id", DEFAULT_SPLADE_MODEL_ID)
                        or DEFAULT_SPLADE_MODEL_ID
                    ).strip(),
                    "splade_max_length": _as_int_opt(
                        opts,
                        "splade_max_length",
                        DEFAULT_SPLADE_MAX_LENGTH,
                        min_value=8,
                    ),
                    "splade_doc_top_terms": _as_int_opt(
                        opts,
                        "splade_doc_top_terms",
                        DEFAULT_SPLADE_DOC_TOP_TERMS,
                        min_value=8,
                    ),
                    "splade_query_top_terms": _as_int_opt(
                        opts,
                        "splade_query_top_terms",
                        DEFAULT_SPLADE_QUERY_TOP_TERMS,
                        min_value=4,
                    ),
                    "local_files_only": _as_bool(
                        opts.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY),
                        DEFAULT_LOCAL_FILES_ONLY,
                    ),
                }
            )
    return base


def _factorized_prepare_index(
    cid: str,
    rep: str,
    docs: Dict[str, str],
    retriever: str,
    params: Dict[str, Any],
) -> Dict[str, Any]:
    exes = list(docs.keys())
    idx_key = _cache_key_for_collection(
        method=f"{NAME}_factorized_idx_{retriever}_{rep}",
        cid=cid,
        oids=exes,
        config=params,
    )
    if idx_key in _FACTORIZED_INDEX_MEM_CACHE:
        return {
            "handle": _FACTORIZED_INDEX_MEM_CACHE[idx_key],
            "one_time_index_ms": 0.0,
            "cache_hit": True,
        }

    t0 = time.perf_counter_ns()
    handle: Dict[str, Any] = {
        "cid": cid,
        "representation": rep,
        "retriever": retriever,
        "params": params,
        "oids": exes,
        "docs": docs,
    }

    if retriever in {
        "bm25",
        "bm25_rm3",
        "bm25_ce",
        "rrf_bm25_dense",
        "rrf_bm25_splade",
    }:
        if BM25Okapi is None:
            return {"error": "rank_bm25 is not available; install rank-bm25."}
        corpus: List[List[str]] = []
        for oid in exes:
            corpus.append(_factorized_doc_tokens(docs.get(oid, ""), rep))
        handle["bm25_corpus"] = corpus
        handle["bm25"] = _safe_build_bm25(corpus)

    if retriever == "bm25f":
        docs_meta: List[Dict[str, Any]] = []
        df: Dict[str, int] = defaultdict(int)
        total_name_len = 0.0
        total_doc_len = 0.0
        for oid in exes:
            name_tokens: List[str] = []
            for nm in api.get_names_from_oid(oid):
                if isinstance(nm, str):
                    name_tokens.extend(_factorized_doc_tokens(nm, rep))
            doc_tokens = _factorized_doc_tokens(docs.get(oid, ""), rep)
            name_tf = Counter(name_tokens)
            doc_tf = Counter(doc_tokens)
            total_name_len += len(name_tokens)
            total_doc_len += len(doc_tokens)
            seen_terms = set(name_tf.keys()) | set(doc_tf.keys())
            for t in seen_terms:
                df[t] += 1
            docs_meta.append(
                {
                    "oid": oid,
                    "name_tf": name_tf,
                    "str_tf": doc_tf,
                    "name_len": len(name_tokens),
                    "str_len": len(doc_tokens),
                }
            )
        n_docs = max(1, len(docs_meta))
        idf = {t: math.log((n_docs - d + 0.5) / (d + 0.5) + 1.0) for t, d in df.items()}
        handle.update(
            {
                "bm25f_docs": docs_meta,
                "bm25f_idf": idf,
                "bm25f_avg_name_len": (total_name_len / n_docs),
                "bm25f_avg_str_len": (total_doc_len / n_docs),
            }
        )

    if retriever == "chargram_bm25":
        if BM25Okapi is None:
            return {"error": "rank_bm25 is not available; install rank-bm25."}
        min_n = int(params.get("chargram_min_n", DEFAULT_CHARGRAM_MIN_N))
        max_n = int(params.get("chargram_max_n", DEFAULT_CHARGRAM_MAX_N))
        corpus = [
            _char_ngrams(
                _factorized_doc_tokens(docs.get(oid, ""), rep), min_n=min_n, max_n=max_n
            )
            for oid in exes
        ]
        handle["chargram_corpus"] = corpus
        handle["chargram_bm25"] = _safe_build_bm25(corpus)

    if retriever in {"dense_chunked", "dense_ce", "rrf_bm25_dense"}:
        dep_err = _require_numpy()
        if dep_err:
            return {"error": dep_err}
        try:
            model = _get_sentence_model(
                str(params.get("dense_model_id", DEFAULT_DENSE_MODEL_ID)),
                local_files_only=bool(
                    params.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY)
                ),
            )
        except Exception as e:
            return {"error": f"dense model load failed: {e}"}
        chunk_tokens = int(params.get("dense_chunk_tokens", DEFAULT_DENSE_CHUNK_TOKENS))
        chunk_overlap = int(
            params.get("dense_chunk_overlap", DEFAULT_DENSE_CHUNK_OVERLAP)
        )
        chunk_overlap = max(0, min(chunk_overlap, max(0, chunk_tokens - 1)))
        chunk_texts: List[str] = []
        owners: List[str] = []
        tokenizer = getattr(model, "tokenizer", None)
        for oid in exes:
            doc_text = str(docs.get(oid, "") or "")
            windows = _chunk_text_for_tokenizer(
                doc_text,
                tokenizer=tokenizer,
                chunk_tokens=chunk_tokens,
                chunk_overlap=chunk_overlap,
            )
            if not windows and doc_text.strip():
                windows = [doc_text]
            for w in windows:
                chunk_texts.append(w)
                owners.append(oid)
        doc_chunk_emb: Dict[str, Any] = {oid: None for oid in exes}
        if chunk_texts:
            embs = model.encode(
                chunk_texts,
                batch_size=32,
                show_progress_bar=False,
                normalize_embeddings=True,
            )
            embs = _ensure_np_array(embs)
            grouped: Dict[str, List[Any]] = defaultdict(list)
            for i, oid in enumerate(owners):
                grouped[oid].append(embs[i])
            for oid in exes:
                rows = grouped.get(oid) or []
                if rows:
                    doc_chunk_emb[oid] = _ensure_np_array(rows)
        handle.update({"dense_model": model, "dense_chunk_emb": doc_chunk_emb})

    if retriever in {"splade", "rrf_bm25_splade"}:
        if torch is None or AutoTokenizer is None or AutoModelForMaskedLM is None:
            return {"error": "splade requires torch + transformers."}
        try:
            tokenizer = _get_hf_tokenizer(
                str(params.get("splade_model_id", DEFAULT_SPLADE_MODEL_ID)),
                local_files_only=bool(
                    params.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY)
                ),
            )
            model = _get_hf_model(
                str(params.get("splade_model_id", DEFAULT_SPLADE_MODEL_ID)),
                mode="mlm",
                local_files_only=bool(
                    params.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY)
                ),
            )
        except Exception as e:
            return {"error": f"splade model load failed: {e}"}
        max_len = int(params.get("splade_max_length", DEFAULT_SPLADE_MAX_LENGTH))
        doc_top = int(params.get("splade_doc_top_terms", DEFAULT_SPLADE_DOC_TOP_TERMS))
        sparse = {
            oid: _splade_encode_sparse(
                text=docs.get(oid, ""),
                tokenizer=tokenizer,
                model=model,
                max_length=max_len,
                top_terms=doc_top,
            )
            for oid in exes
        }
        handle.update(
            {
                "splade_tokenizer": tokenizer,
                "splade_model": model,
                "splade_sparse": sparse,
            }
        )

    if retriever == "colbert":
        dep_err = _require_numpy()
        if dep_err:
            return {"error": dep_err}
        if torch is None or AutoTokenizer is None or AutoModel is None:
            return {"error": "colbert requires torch + transformers."}
        try:
            tokenizer = _get_hf_tokenizer(
                str(params.get("colbert_model_id", DEFAULT_COLBERT_MODEL_ID)),
                local_files_only=bool(
                    params.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY)
                ),
            )
            model = _get_hf_model(
                str(params.get("colbert_model_id", DEFAULT_COLBERT_MODEL_ID)),
                mode="base",
                local_files_only=bool(
                    params.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY)
                ),
            )
        except Exception as e:
            return {"error": f"colbert model load failed: {e}"}
        max_len = int(params.get("colbert_max_length", DEFAULT_COLBERT_MAX_LENGTH))
        token_cap = int(
            params.get("colbert_doc_token_cap", DEFAULT_COLBERT_DOC_TOKEN_CAP)
        )
        tok_emb = {
            oid: _colbert_encode_tokens(
                text=docs.get(oid, ""),
                tokenizer=tokenizer,
                model=model,
                max_length=max_len,
                token_cap=token_cap,
            )
            for oid in exes
        }
        handle.update(
            {
                "colbert_tokenizer": tokenizer,
                "colbert_model": model,
                "colbert_tok_emb": tok_emb,
            }
        )

    if retriever in {"bm25_ce", "dense_ce", "ce"}:
        try:
            ce = _get_cross_encoder(
                str(params.get("rerank_model_id", DEFAULT_RERANK_MODEL_ID)),
                local_files_only=bool(
                    params.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY)
                ),
            )
        except Exception as e:
            return {"error": f"reranker model load failed: {e}"}
        ce_chunk_tokens = int(
            params.get("dense_chunk_tokens", DEFAULT_DENSE_CHUNK_TOKENS)
        )
        ce_chunk_overlap = int(
            params.get("dense_chunk_overlap", DEFAULT_DENSE_CHUNK_OVERLAP)
        )
        ce_chunk_overlap = max(0, min(ce_chunk_overlap, max(0, ce_chunk_tokens - 1)))
        tokenizer = getattr(ce, "tokenizer", None)
        ce_passages: Dict[str, List[str]] = {}
        for oid in exes:
            doc_text = str(docs.get(oid, "") or "")
            passages = _chunk_text_for_tokenizer(
                doc_text,
                tokenizer=tokenizer,
                chunk_tokens=ce_chunk_tokens,
                chunk_overlap=ce_chunk_overlap,
            )
            if not passages:
                passages = [doc_text] if doc_text else [""]
            ce_passages[oid] = passages
        handle["cross_encoder"] = ce
        handle["ce_passages"] = ce_passages

    one_time_index_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
    _FACTORIZED_INDEX_MEM_CACHE[idx_key] = handle
    return {
        "handle": handle,
        "one_time_index_ms": float(f"{one_time_index_ms:.3f}"),
        "cache_hit": False,
    }


def _factorized_search(
    handle: Dict[str, Any], query: str, top_k: int
) -> Dict[str, Any]:
    retriever = str(handle.get("retriever", ""))
    rep = str(handle.get("representation", "r0_raw"))
    params = handle.get("params") or {}
    oids = list(handle.get("oids") or [])
    raw_query = str(query or "").strip()
    q_text = raw_query
    if retriever in {"dense_chunked", "dense_ce", "ce"}:
        if not raw_query:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
    elif not q_text:
        return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}

    if retriever == "bm25":
        bm25 = handle.get("bm25")
        if bm25 is None or not oids:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
        q_tokens = _factorized_query_tokens(q_text, rep)
        if not q_tokens:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
        t0 = time.perf_counter_ns()
        scores = bm25.get_scores(q_tokens)
        idxs = sorted(range(len(scores)), key=lambda i: scores[i], reverse=True)[:top_k]
        ranked = [oids[i] for i in idxs]
        ms = (time.perf_counter_ns() - t0) / 1_000_000.0
        return {"ranked": ranked, "query_time_ms": ms, "stage_times_ms": {"bm25": ms}}

    if retriever == "bm25_rm3":
        bm25 = handle.get("bm25")
        corpus = handle.get("bm25_corpus") or []
        if bm25 is None or not oids:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
        q_tokens = _factorized_query_tokens(q_text, rep)
        if not q_tokens:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
        t0 = time.perf_counter_ns()
        s1 = bm25.get_scores(q_tokens)
        q_rm3 = _rm3_expand_query_tokens(
            query_tokens=q_tokens,
            corpus=corpus,
            scores=s1,
            fb_docs=int(params.get("rm3_fb_docs", DEFAULT_RM3_FB_DOCS)),
            fb_terms=int(params.get("rm3_fb_terms", DEFAULT_RM3_FB_TERMS)),
            orig_weight=float(params.get("rm3_orig_weight", DEFAULT_RM3_ORIG_WEIGHT)),
        )
        s2 = bm25.get_scores(q_rm3)
        idxs = sorted(range(len(s2)), key=lambda i: s2[i], reverse=True)[:top_k]
        ranked = [oids[i] for i in idxs]
        ms = (time.perf_counter_ns() - t0) / 1_000_000.0
        return {
            "ranked": ranked,
            "query_time_ms": ms,
            "stage_times_ms": {"bm25_rm3": ms},
        }

    if retriever == "bm25f":
        docs_meta = handle.get("bm25f_docs") or []
        if not docs_meta:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
        q_tokens = _factorized_query_tokens(q_text, rep)
        if not q_tokens:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
        q_tf = Counter(q_tokens)
        t0 = time.perf_counter_ns()
        scored = []
        for doc in docs_meta:
            scored.append(
                (
                    doc["oid"],
                    _score_bm25f_doc(
                        q_tf=q_tf,
                        doc=doc,
                        idf=handle.get("bm25f_idf") or {},
                        k1=float(params.get("bm25f_k1", DEFAULT_BM25F_K1)),
                        b_name=float(params.get("bm25f_b_name", DEFAULT_BM25F_B_NAME)),
                        b_str=float(
                            params.get("bm25f_b_string", DEFAULT_BM25F_B_STRING)
                        ),
                        name_weight=float(
                            params.get("bm25f_name_weight", DEFAULT_BM25F_NAME_WEIGHT)
                        ),
                        string_weight=float(
                            params.get(
                                "bm25f_string_weight", DEFAULT_BM25F_STRING_WEIGHT
                            )
                        ),
                        avg_name_len=float(handle.get("bm25f_avg_name_len") or 0.0),
                        avg_str_len=float(handle.get("bm25f_avg_str_len") or 0.0),
                    ),
                )
            )
        scored.sort(key=lambda x: x[1], reverse=True)
        ranked = [oid for oid, _ in scored[:top_k]]
        ms = (time.perf_counter_ns() - t0) / 1_000_000.0
        return {"ranked": ranked, "query_time_ms": ms, "stage_times_ms": {"bm25f": ms}}

    if retriever == "chargram_bm25":
        bm25 = handle.get("chargram_bm25")
        if bm25 is None or not oids:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
        q_tokens = _factorized_query_tokens(q_text, rep)
        min_n = int(params.get("chargram_min_n", DEFAULT_CHARGRAM_MIN_N))
        max_n = int(params.get("chargram_max_n", DEFAULT_CHARGRAM_MAX_N))
        q_grams = _char_ngrams(q_tokens, min_n=min_n, max_n=max_n)
        if not q_grams:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
        t0 = time.perf_counter_ns()
        scores = bm25.get_scores(q_grams)
        idxs = sorted(range(len(scores)), key=lambda i: scores[i], reverse=True)[:top_k]
        ranked = [oids[i] for i in idxs]
        ms = (time.perf_counter_ns() - t0) / 1_000_000.0
        return {
            "ranked": ranked,
            "query_time_ms": ms,
            "stage_times_ms": {"chargram_bm25": ms},
        }

    if retriever == "dense_chunked":
        model = handle.get("dense_model")
        if model is None or np is None:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
        if not raw_query:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
        t0 = time.perf_counter_ns()
        q_vec = _ensure_np_array(
            model.encode(raw_query, show_progress_bar=False, normalize_embeddings=True)
        )
        scored: List[Tuple[str, float]] = []
        for oid in oids:
            emb = (handle.get("dense_chunk_emb") or {}).get(oid)
            if isinstance(emb, np.ndarray) and emb.size > 0:
                scored.append((oid, float(np.max(emb.dot(q_vec)))))
            else:
                scored.append((oid, -1e9))
        scored.sort(key=lambda x: x[1], reverse=True)
        ranked = [oid for oid, _ in scored[:top_k]]
        ms = (time.perf_counter_ns() - t0) / 1_000_000.0
        return {
            "ranked": ranked,
            "query_time_ms": ms,
            "stage_times_ms": {"dense_chunked": ms},
        }

    if retriever == "splade":
        tokenizer = handle.get("splade_tokenizer")
        model = handle.get("splade_model")
        if tokenizer is None or model is None:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
        t0 = time.perf_counter_ns()
        q_sparse = _splade_encode_sparse(
            text=q_text,
            tokenizer=tokenizer,
            model=model,
            max_length=int(params.get("splade_max_length", DEFAULT_SPLADE_MAX_LENGTH)),
            top_terms=int(
                params.get("splade_query_top_terms", DEFAULT_SPLADE_QUERY_TOP_TERMS)
            ),
        )
        if not q_sparse:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
        scored = [
            (
                oid,
                _sparse_dot(
                    q_sparse, (handle.get("splade_sparse") or {}).get(oid) or {}
                ),
            )
            for oid in oids
        ]
        scored.sort(key=lambda x: x[1], reverse=True)
        ranked = [oid for oid, _ in scored[:top_k]]
        ms = (time.perf_counter_ns() - t0) / 1_000_000.0
        return {"ranked": ranked, "query_time_ms": ms, "stage_times_ms": {"splade": ms}}

    if retriever == "colbert":
        tokenizer = handle.get("colbert_tokenizer")
        model = handle.get("colbert_model")
        if tokenizer is None or model is None:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
        q_emb = _colbert_encode_tokens(
            text=q_text,
            tokenizer=tokenizer,
            model=model,
            max_length=int(
                params.get("colbert_max_length", DEFAULT_COLBERT_MAX_LENGTH)
            ),
            token_cap=0,
        )
        if not isinstance(q_emb, np.ndarray) or q_emb.size == 0:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
        t0 = time.perf_counter_ns()
        scored = [
            (oid, _maxsim_score(q_emb, (handle.get("colbert_tok_emb") or {}).get(oid)))
            for oid in oids
        ]
        scored.sort(key=lambda x: x[1], reverse=True)
        ranked = [oid for oid, _ in scored[:top_k]]
        ms = (time.perf_counter_ns() - t0) / 1_000_000.0
        return {
            "ranked": ranked,
            "query_time_ms": ms,
            "stage_times_ms": {"colbert": ms},
        }

    if retriever in {"bm25_ce", "dense_ce"}:
        stage_times: Dict[str, float] = {}
        max_k = min(
            len(oids),
            max(
                list(
                    params.get("rerank_candidate_ks")
                    or [int(params.get("rerank_eval_k", DEFAULT_RERANK_EVAL_K))]
                )
            ),
        )
        if max_k <= 0:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
        if retriever == "bm25_ce":
            stage1_handle = dict(handle)
            stage1_handle["retriever"] = "bm25"
            out1 = _factorized_search(stage1_handle, q_text, max_k)
            stage_times["stage1_bm25"] = float(out1.get("query_time_ms", 0.0) or 0.0)
        else:
            stage1_handle = dict(handle)
            stage1_handle["retriever"] = "dense_chunked"
            out1 = _factorized_search(stage1_handle, raw_query, max_k)
            stage_times["stage1_dense"] = float(out1.get("query_time_ms", 0.0) or 0.0)
        cands = list(out1.get("ranked") or [])[:max_k]
        if not cands:
            return {
                "ranked": [],
                "query_time_ms": sum(stage_times.values()),
                "stage_times_ms": stage_times,
            }
        t2 = time.perf_counter_ns()
        reranked = _rerank_with_cross_encoder(
            cross_encoder=handle.get("cross_encoder"),
            prompt=raw_query,
            candidate_oids=cands,
            oid_texts=handle.get("docs") or {},
            oid_passages=handle.get("ce_passages") or {},
            chunk_tokens=int(
                params.get("dense_chunk_tokens", DEFAULT_DENSE_CHUNK_TOKENS)
            ),
            chunk_overlap=int(
                params.get("dense_chunk_overlap", DEFAULT_DENSE_CHUNK_OVERLAP)
            ),
        )
        ce_ms = (time.perf_counter_ns() - t2) / 1_000_000.0
        stage_times["stage2_ce"] = ce_ms
        ranked = reranked[:top_k]
        return {
            "ranked": ranked,
            "query_time_ms": sum(stage_times.values()),
            "stage_times_ms": stage_times,
        }

    if retriever == "ce":
        if not oids:
            return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}
        t0 = time.perf_counter_ns()
        reranked = _rerank_with_cross_encoder(
            cross_encoder=handle.get("cross_encoder"),
            prompt=raw_query,
            candidate_oids=oids,
            oid_texts=handle.get("docs") or {},
            oid_passages=handle.get("ce_passages") or {},
            chunk_tokens=int(
                params.get("dense_chunk_tokens", DEFAULT_DENSE_CHUNK_TOKENS)
            ),
            chunk_overlap=int(
                params.get("dense_chunk_overlap", DEFAULT_DENSE_CHUNK_OVERLAP)
            ),
        )
        ce_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
        return {
            "ranked": reranked[:top_k],
            "query_time_ms": ce_ms,
            "stage_times_ms": {"ce": ce_ms},
        }

    if retriever in {"rrf_bm25_dense", "rrf_bm25_splade"}:
        stage_times: Dict[str, float] = {}
        depth = int(params.get("rrf_depth", top_k))
        rrf_k = int(params.get("rrf_k", DEFAULT_RRF_K))

        h_b = dict(handle)
        h_b["retriever"] = "bm25"
        out_b = _factorized_search(h_b, q_text, depth)
        stage_times["bm25"] = float(out_b.get("query_time_ms", 0.0) or 0.0)

        if retriever == "rrf_bm25_dense":
            h_o = dict(handle)
            h_o["retriever"] = "dense_chunked"
            out_o = _factorized_search(h_o, q_text, depth)
            stage_times["dense_chunked"] = float(out_o.get("query_time_ms", 0.0) or 0.0)
        else:
            h_o = dict(handle)
            h_o["retriever"] = "splade"
            out_o = _factorized_search(h_o, q_text, depth)
            stage_times["splade"] = float(out_o.get("query_time_ms", 0.0) or 0.0)

        t2 = time.perf_counter_ns()
        fused = _rrf_fuse(
            [out_b.get("ranked") or [], out_o.get("ranked") or []],
            rrf_k=rrf_k,
            depth=depth,
        )
        fuse_ms = (time.perf_counter_ns() - t2) / 1_000_000.0
        stage_times["rrf_fuse"] = fuse_ms
        return {
            "ranked": fused[:top_k],
            "query_time_ms": sum(stage_times.values()),
            "stage_times_ms": stage_times,
        }

    return {"ranked": [], "query_time_ms": 0.0, "stage_times_ms": {}}


def _run_factorized_func_cell(
    ground_truth: Dict[str, Dict[str, str]],
    prompt_map: Dict[str, str],
    opts: Dict[str, Any],
) -> Dict[str, Any]:
    out = _batch_function_embeddings([], opts)
    if not isinstance(out, dict) or out.get("error"):
        return {
            "representation": "granularity_function",
            "retriever": "func",
            "params": {},
            "error": (
                (out or {}).get("error")
                if isinstance(out, dict)
                else "Function baseline failed."
            ),
        }
    attempted = int(out.get("attempted_queries", 0) or 0)
    avg_ms = float(out.get("avg_retrieval_ms", 0.0) or 0.0)
    return {
        "representation": "granularity_function",
        "retriever": "func",
        "params": {
            "top_k_funcs": int(opts.get("top_k_funcs", 1) or 1),
            "func_file_agg": str(opts.get("func_file_agg", "top1") or "top1"),
        },
        "top_k_files": int(
            opts.get("top_k_files", DEFAULT_TOP_K_FILES) or DEFAULT_TOP_K_FILES
        ),
        "attempted_queries": attempted,
        "global_metrics": dict(out.get("global_metrics") or {}),
        "timing": {
            "one_time_doc_ms": 0.0,
            "one_time_index_ms": 0.0,
            "query_time_ms_total": float(f"{(avg_ms * max(attempted, 0)):.3f}"),
            "query_time_ms_avg": float(f"{avg_ms:.3f}"),
            "stage_times_ms": {},
        },
        "per_collection": dict(out.get("per_collection") or {}),
        "granularity": "function",
    }


def _run_factorized_cell(
    *,
    ground_truth: Dict[str, Dict[str, str]],
    prompt_map: Dict[str, str],
    rep: str,
    retriever: str,
    opts: Dict[str, Any],
) -> Dict[str, Any]:
    top_k_files = _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
    params = _factorized_retriever_params(retriever, rep, opts, top_k_files=top_k_files)

    per_collection: Dict[str, Any] = {}
    attempted = 0
    sum_p1 = 0
    sum_h2 = 0
    sum_h5 = 0
    sum_mrr = 0.0
    sum_rank_effort = 0.0
    one_time_doc_ms_total = 0.0
    one_time_index_ms_total = 0.0
    query_time_ms_total = 0.0
    stage_totals: Dict[str, float] = defaultdict(float)

    for cid, golds in ground_truth.items():
        docs, doc_meta, doc_err = _build_docs_for_collection_with_timing(cid, rep, opts)
        if doc_err:
            per_collection[api.get_colname_from_oid(cid)] = {"error": doc_err}
            continue
        if docs is None or doc_meta is None:
            per_collection[api.get_colname_from_oid(cid)] = {
                "error": "Failed to build docs."
            }
            continue
        prep = _factorized_prepare_index(cid, rep, docs, retriever, params)
        if prep.get("error"):
            per_collection[api.get_colname_from_oid(cid)] = {"error": prep.get("error")}
            continue
        handle = prep.get("handle")
        if not isinstance(handle, dict):
            per_collection[api.get_colname_from_oid(cid)] = {
                "error": "Invalid index handle."
            }
            continue

        doc_ms = float(doc_meta.get("one_time_doc_ms", 0.0) or 0.0)
        idx_ms = float(prep.get("one_time_index_ms", 0.0) or 0.0)
        if bool(doc_meta.get("cache_hit", False)):
            doc_ms = 0.0
        if bool(prep.get("cache_hit", False)):
            idx_ms = 0.0
        one_time_doc_ms_total += doc_ms
        one_time_index_ms_total += idx_ms

        colname = api.get_colname_from_oid(cid)
        ranks_by_component: Dict[str, Optional[int]] = {}
        attempted_here = 0
        col_query_total = 0.0
        col_stage_totals: Dict[str, float] = defaultdict(float)
        for comp, gold_oid in golds.items():
            prompt = prompt_map.get(comp)
            if not prompt:
                ranks_by_component[comp] = None
                continue
            out = _factorized_search(handle, prompt, top_k_files)
            oid_list = out.get("ranked") or []
            if not isinstance(oid_list, list):
                oid_list = []
            q_ms = float(out.get("query_time_ms", 0.0) or 0.0)
            col_query_total += q_ms
            query_time_ms_total += q_ms
            for stage, v in (out.get("stage_times_ms") or {}).items():
                try:
                    stage_v = float(v)
                except Exception:
                    continue
                stage_totals[stage] += stage_v
                col_stage_totals[stage] += stage_v

            attempted += 1
            attempted_here += 1
            rank = _rank_from_oid_list(oid_list, gold_oid)
            ranks_by_component[comp] = rank
            if rank is not None:
                sum_p1 += int(rank == 1)
                sum_h2 += int(rank <= 2)
                sum_h5 += int(rank <= 5)
                sum_mrr += 1.0 / rank
                sum_rank_effort += rank
            else:
                sum_rank_effort += top_k_files + 1

        metrics = {}
        if attempted_here > 0:
            metrics = {
                "P@1": sum(1 for r in ranks_by_component.values() if r == 1)
                / attempted_here,
                "Hit@2": sum(
                    1 for r in ranks_by_component.values() if r is not None and r <= 2
                )
                / attempted_here,
                "Hit@5": sum(
                    1 for r in ranks_by_component.values() if r is not None and r <= 5
                )
                / attempted_here,
                "MRR": sum(
                    (1.0 / r) for r in ranks_by_component.values() if r is not None
                )
                / attempted_here,
                "mean_rank": sum(
                    (r if r is not None else (top_k_files + 1))
                    for r in ranks_by_component.values()
                )
                / attempted_here,
            }
        per_collection[colname] = {
            "metrics": metrics,
            "ranks_by_prompt": ranks_by_component,
            "timing": {
                "one_time_doc_ms": float(f"{doc_ms:.3f}"),
                "one_time_index_ms": float(f"{idx_ms:.3f}"),
                "query_time_ms_total": float(f"{col_query_total:.3f}"),
                "query_time_ms_avg": float(
                    f"{(col_query_total / max(attempted_here, 1)):.3f}"
                ),
                "stage_times_ms": {
                    k: float(f"{v:.3f}") for k, v in col_stage_totals.items()
                },
            },
        }

    if attempted == 0:
        return {
            "representation": rep,
            "retriever": retriever,
            "params": params,
            "top_k_files": top_k_files,
            "error": f"No prompts evaluated for cell ({rep}, {retriever}).",
            "per_collection": per_collection,
        }

    return {
        "representation": rep,
        "retriever": retriever,
        "params": params,
        "top_k_files": top_k_files,
        "attempted_queries": attempted,
        "global_metrics": {
            "P@1": sum_p1 / attempted,
            "Hit@2": sum_h2 / attempted,
            "Hit@5": sum_h5 / attempted,
            "MRR": sum_mrr / attempted,
            "Mean": sum_rank_effort / attempted,
        },
        "timing": {
            "one_time_doc_ms": float(f"{one_time_doc_ms_total:.3f}"),
            "one_time_index_ms": float(f"{one_time_index_ms_total:.3f}"),
            "query_time_ms_total": float(f"{query_time_ms_total:.3f}"),
            "query_time_ms_avg": float(
                f"{(query_time_ms_total / max(attempted, 1)):.3f}"
            ),
            "stage_times_ms": {k: float(f"{v:.3f}") for k, v in stage_totals.items()},
            "total_ms": float(
                f"{(one_time_doc_ms_total + one_time_index_ms_total + query_time_ms_total):.3f}"
            ),
        },
        "per_collection": per_collection,
    }


def _factorized_retriever_comparison(cells: List[Dict[str, Any]]) -> Dict[str, Any]:
    rows = []
    for c in cells:
        if not isinstance(c, dict):
            continue
        if c.get("retriever") == "func":
            continue
        rows.append(
            {
                "representation": c.get("representation"),
                "retriever": c.get("retriever"),
                "attempted_queries": c.get("attempted_queries"),
                "global_metrics": c.get("global_metrics"),
                "timing": c.get("timing"),
                "error": c.get("error"),
            }
        )
    return {
        "rows": rows,
        "standard_representations": ["r0_raw", "r1_norm", "r2_packed"],
    }


def _factorized_representation_comparison(
    cells: List[Dict[str, Any]],
) -> Dict[str, Any]:
    required = {"bm25", "dense_chunked"}
    optional = {"splade", "colbert"}
    want = required | optional
    grouped: Dict[str, Dict[str, Any]] = defaultdict(dict)
    for c in cells:
        if not isinstance(c, dict):
            continue
        ret = c.get("retriever")
        rep = c.get("representation")
        if ret not in want:
            continue
        grouped[str(ret)][str(rep)] = {
            "global_metrics": c.get("global_metrics"),
            "timing": c.get("timing"),
            "error": c.get("error"),
        }
    return {"retrievers": grouped}


def _factorized_r2_deltas(cells: List[Dict[str, Any]]) -> Dict[str, Any]:
    by_ret_rep: Dict[str, Dict[str, Dict[str, Any]]] = defaultdict(dict)
    for c in cells:
        if not isinstance(c, dict):
            continue
        ret = str(c.get("retriever") or "")
        rep = str(c.get("representation") or "")
        if ret == "func":
            continue
        by_ret_rep[ret][rep] = c

    rows: List[Dict[str, Any]] = []
    for ret, rep_map in by_ret_rep.items():
        r2 = rep_map.get("r2_packed")
        if not isinstance(r2, dict) or r2.get("error"):
            continue
        gm2 = r2.get("global_metrics") or {}
        t2 = r2.get("timing") or {}
        base_row = {"retriever": ret}
        for base_rep, label in (
            ("r0_raw", "delta_r2_minus_r0"),
            ("r1_norm", "delta_r2_minus_r1"),
        ):
            b = rep_map.get(base_rep)
            if not isinstance(b, dict) or b.get("error"):
                base_row[label] = None
                continue
            gmb = b.get("global_metrics") or {}
            tb = b.get("timing") or {}
            base_row[label] = {
                "MRR": _metric_delta(
                    _safe_float(gm2.get("MRR")), _safe_float(gmb.get("MRR"))
                ),
                "P@1": _metric_delta(
                    _safe_float(gm2.get("P@1")), _safe_float(gmb.get("P@1"))
                ),
                "Hit@2": _metric_delta(
                    _safe_float(gm2.get("Hit@2")), _safe_float(gmb.get("Hit@2"))
                ),
                "Hit@5": _metric_delta(
                    _safe_float(gm2.get("Hit@5")), _safe_float(gmb.get("Hit@5"))
                ),
                "Mean": _metric_delta(
                    _safe_float(gm2.get("Mean")), _safe_float(gmb.get("Mean"))
                ),
                "query_time_ms_avg": _metric_delta(
                    _safe_float(t2.get("query_time_ms_avg")),
                    _safe_float(tb.get("query_time_ms_avg")),
                ),
            }
        rows.append(base_row)
    return {"rows": rows}


def agent_factorized_eval_all(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    return {
        "error": (
            "agent_factorized_eval_all is deprecated. "
            "Use agent_eval_all (or agent_eval_e2 for representation matrix only)."
        )
    }

    """
    Run factorized matrix evaluation: method = (representation, retriever).

    Outputs:
      - factorized_cells.json
      - factorized_retriever_comparison.json
      - factorized_representation_comparison.json
      - factorized_r2_delta_summary.json
      - factorized_eval_all.json
    """
    ground_truth, prompt_map, load_err = _load_eval_inputs(opts)
    if load_err:
        return {"error": load_err}
    if ground_truth is None or prompt_map is None:
        return {"error": "Failed loading evaluation inputs."}

    reps, rep_err = _parse_representation_ids_opt(opts)
    if rep_err:
        return {"error": rep_err}
    retrievers, ret_err = _parse_factorized_retriever_ids_opt(opts)
    if ret_err:
        return {"error": ret_err}

    started_ns = time.time_ns()
    top_k_files = _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
    cells: List[Dict[str, Any]] = []

    for rep in reps or []:
        for ret in retrievers or []:
            if ret == "func":
                continue
            cell = _run_factorized_cell(
                ground_truth=ground_truth,
                prompt_map=prompt_map,
                rep=rep,
                retriever=ret,
                opts=opts,
            )
            cells.append(cell)

    if "func" in (retrievers or []):
        cells.append(_run_factorized_func_cell(ground_truth, prompt_map, opts))

    retriever_comparison = _factorized_retriever_comparison(cells)
    representation_comparison = _factorized_representation_comparison(cells)
    r2_delta_summary = _factorized_r2_deltas(cells)

    payload = {
        "toolset": FUSE_TOOLSET,
        "mode": "factorized",
        "candidate_filter": "executables_only_excluding_.so_and_.ko",
        "representations": reps,
        "retrievers": retrievers,
        "top_k_files": top_k_files,
        "started_unix_ns": started_ns,
        "elapsed_ms": float(f"{(time.time_ns() - started_ns) / 1_000_000.0:.3f}"),
        "cells": cells,
        "retriever_comparison": retriever_comparison,
        "representation_comparison": representation_comparison,
        "r2_delta_summary": r2_delta_summary,
    }

    outdir = (opts.get("outdir") or "").strip()
    artifacts: Dict[str, str] = {}
    if outdir:
        try:
            outpath = Path(outdir).expanduser()
            outpath.mkdir(parents=True, exist_ok=True)
            artifacts["cells"] = _write_json(
                outpath, "factorized_cells.json", {"cells": cells}
            )
            artifacts["retriever_comparison"] = _write_json(
                outpath, "factorized_retriever_comparison.json", retriever_comparison
            )
            artifacts["representation_comparison"] = _write_json(
                outpath,
                "factorized_representation_comparison.json",
                representation_comparison,
            )
            artifacts["r2_delta_summary"] = _write_json(
                outpath, "factorized_r2_delta_summary.json", r2_delta_summary
            )
            artifacts["all"] = _write_json(outpath, "factorized_eval_all.json", payload)
        except Exception as e:
            payload["artifact_error"] = f"Failed writing outdir artifacts: {e}"
    if artifacts:
        payload["artifacts"] = artifacts
    return payload


def _parse_named_ids_opt(
    opts: Dict[str, Any],
    *,
    key: str,
    default_ids: Sequence[str],
    allowed_ids: Sequence[str],
    aliases: Optional[Dict[str, str]] = None,
) -> Tuple[Optional[List[str]], Optional[str]]:
    aliases = aliases or {}
    raw = str(opts.get(key, "") or "").strip().lower()
    if not raw:
        return list(default_ids), None

    expanded: List[str] = []
    for tok in [t.strip() for t in raw.split(",") if t.strip()]:
        if tok == "all":
            expanded.extend(list(allowed_ids))
            continue
        expanded.append(aliases.get(tok, tok))

    out: List[str] = []
    seen: Set[str] = set()
    for m in expanded:
        if m in seen:
            continue
        seen.add(m)
        out.append(m)

    unknown = [m for m in out if m not in set(allowed_ids)]
    if unknown:
        return (
            None,
            f"Unknown values for {key}: {','.join(unknown)}. "
            f"Allowed: {','.join(allowed_ids)}.",
        )
    return out, None


def _build_eval_tasks(
    ground_truth: Dict[str, Dict[str, str]],
    prompt_map: Dict[str, str],
) -> List[Dict[str, Any]]:
    tasks: List[Dict[str, Any]] = []
    for cid in sorted(ground_truth.keys(), key=lambda c: api.get_colname_from_oid(c)):
        colname = api.get_colname_from_oid(cid)
        for component, gold_oid in sorted(
            ground_truth[cid].items(), key=lambda kv: kv[0]
        ):
            prompt = str(prompt_map.get(component, "") or "").strip()
            if not prompt:
                continue
            tasks.append(
                {
                    "task_id": f"{cid}:{component}",
                    "cid": cid,
                    "collection": colname,
                    "component": component,
                    "prompt": prompt,
                    "gold_oid": gold_oid,
                }
            )
    return tasks


def _percentile(values: Sequence[float], p: float) -> Optional[float]:
    if not values:
        return None
    arr = sorted(float(v) for v in values)
    idx = int(round(max(0.0, min(1.0, p)) * (len(arr) - 1)))
    return float(arr[idx])


def _bootstrap_ci_from_ranks(
    ranks: Sequence[int],
    opts: Dict[str, Any],
) -> Dict[str, Dict[str, float]]:
    if not _as_bool(opts.get("bootstrap_ci", True), True):
        return {}
    n = len(ranks)
    if n <= 0:
        return {}

    samples = _as_int_opt(opts, "bootstrap_samples", 1000, min_value=100)
    seed = _as_int_opt(opts, "bootstrap_seed", 1337)
    rng = random.Random(seed)
    metric_samples: Dict[str, List[float]] = {
        "P@1": [],
        "Hit@2": [],
        "Hit@5": [],
        "MRR": [],
        "Mean": [],
    }
    rank_list = list(ranks)
    for _ in range(samples):
        s = [rank_list[rng.randrange(n)] for _ in range(n)]
        m = _metrics_from_rank_values(s)
        for k in metric_samples.keys():
            metric_samples[k].append(float(m.get(k, 0.0)))

    out: Dict[str, Dict[str, float]] = {}
    for k, vals in metric_samples.items():
        lo = _percentile(vals, 0.025)
        hi = _percentile(vals, 0.975)
        if lo is None or hi is None:
            continue
        out[k] = {"low": float(f"{lo:.6f}"), "high": float(f"{hi:.6f}")}
    return out


def _finalize_method_result(
    *,
    method: str,
    representation: Optional[str],
    retriever: Optional[str],
    params: Dict[str, Any],
    top_k_files: int,
    per_query: List[Dict[str, Any]],
    one_time_doc_ms: float,
    one_time_index_ms: float,
    stage_times: Dict[str, float],
    ci_opts: Dict[str, Any],
) -> Dict[str, Any]:
    attempted = len(per_query)
    if attempted <= 0:
        return {
            "method": method,
            "representation": representation,
            "retriever": retriever,
            "params": params,
            "top_k_files": top_k_files,
            "error": f"No prompts evaluated for method '{method}'.",
        }

    ranks = [int(q.get("rank", top_k_files + 1)) for q in per_query]
    metrics = _metrics_from_rank_values(ranks)
    query_time_ms_total = float(
        sum(float(q.get("runtime_ms", 0.0) or 0.0) for q in per_query)
    )
    per_collection_ranks: Dict[str, List[int]] = defaultdict(list)
    for q in per_query:
        per_collection_ranks[str(q.get("collection", ""))].append(
            int(q.get("rank", top_k_files + 1))
        )

    per_collection: Dict[str, Any] = {}
    for colname, col_ranks in per_collection_ranks.items():
        per_collection[colname] = {
            "attempted_queries": len(col_ranks),
            "metrics": _metrics_from_rank_values(col_ranks),
        }

    return {
        "method": method,
        "representation": representation,
        "retriever": retriever,
        "params": params,
        "top_k_files": top_k_files,
        "attempted_queries": attempted,
        "global_metrics": metrics,
        "ci95": _bootstrap_ci_from_ranks(ranks, ci_opts),
        "timing": {
            "one_time_doc_ms": float(f"{one_time_doc_ms:.3f}"),
            "one_time_index_ms": float(f"{one_time_index_ms:.3f}"),
            "query_time_ms_total": float(f"{query_time_ms_total:.3f}"),
            "query_time_ms_avg": float(
                f"{(query_time_ms_total / max(attempted, 1)):.3f}"
            ),
            "stage_times_ms": {k: float(f"{v:.3f}") for k, v in stage_times.items()},
            "total_ms": float(
                f"{(one_time_doc_ms + one_time_index_ms + query_time_ms_total):.3f}"
            ),
        },
        "per_collection": per_collection,
        "per_query": per_query,
    }


def _run_doc_tool_method(
    *,
    method: str,
    representation: str,
    retriever: str,
    tasks: List[Dict[str, Any]],
    opts: Dict[str, Any],
) -> Dict[str, Any]:
    top_k_files = _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
    params = _factorized_retriever_params(
        retriever, representation, opts, top_k_files=top_k_files
    )
    per_query: List[Dict[str, Any]] = []
    one_time_doc_ms = 0.0
    one_time_index_ms = 0.0
    stage_times: Dict[str, float] = defaultdict(float)

    by_cid: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    for t in tasks:
        by_cid[str(t["cid"])].append(t)

    for cid, cid_tasks in by_cid.items():
        docs, doc_meta, doc_err = _build_docs_for_collection_with_timing(
            cid, representation, opts
        )
        if doc_err or docs is None or doc_meta is None:
            return {"method": method, "error": doc_err or "Failed to build docs."}

        prep = _factorized_prepare_index(cid, representation, docs, retriever, params)
        if prep.get("error"):
            return {"method": method, "error": str(prep.get("error"))}
        handle = prep.get("handle")
        if not isinstance(handle, dict):
            return {"method": method, "error": "Invalid index handle."}

        doc_ms = float(doc_meta.get("one_time_doc_ms", 0.0) or 0.0)
        idx_ms = float(prep.get("one_time_index_ms", 0.0) or 0.0)
        if bool(doc_meta.get("cache_hit", False)):
            doc_ms = 0.0
        if bool(prep.get("cache_hit", False)):
            idx_ms = 0.0
        one_time_doc_ms += doc_ms
        one_time_index_ms += idx_ms

        for task in cid_tasks:
            out = _factorized_search(handle, str(task.get("prompt", "")), top_k_files)
            ranked = list(out.get("ranked") or [])[:top_k_files]
            rank = _rank_from_oid_list(ranked, str(task.get("gold_oid", "")))
            if rank is None:
                rank = top_k_files + 1
            q_ms = float(out.get("query_time_ms", 0.0) or 0.0)
            for stage, v in (out.get("stage_times_ms") or {}).items():
                stage_times[str(stage)] += float(v)
            per_query.append(
                {
                    "task_id": task.get("task_id"),
                    "pair_id": task.get("pair_id"),
                    "variant_id": task.get("variant_id"),
                    "cid": cid,
                    "collection": task.get("collection"),
                    "component": task.get("component"),
                    "query": task.get("prompt"),
                    "gold_oid": task.get("gold_oid"),
                    "rank": rank,
                    "top_k_oids": ranked,
                    "runtime_ms": float(f"{q_ms:.3f}"),
                }
            )

    return _finalize_method_result(
        method=method,
        representation=representation,
        retriever=retriever,
        params=params,
        top_k_files=top_k_files,
        per_query=per_query,
        one_time_doc_ms=one_time_doc_ms,
        one_time_index_ms=one_time_index_ms,
        stage_times=stage_times,
        ci_opts=opts,
    )


def _run_func_tool_method(
    tasks: List[Dict[str, Any]], opts: Dict[str, Any]
) -> Dict[str, Any]:
    top_k_files = _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
    top_k_funcs = _as_int_opt(opts, "top_k_funcs", 1, min_value=1)
    func_file_agg = str(opts.get("func_file_agg", "top1") or "top1").strip().lower()
    if func_file_agg not in {"top1", "mean", "attn"}:
        func_file_agg = "top1"
    func_attn_tau = _as_float_opt(opts, "func_attn_tau", 0.07, min_value=1e-6)
    func_similarity_threshold = _as_float_opt(
        opts, "func_similarity_threshold", 0.0, min_value=0.0
    )

    by_cid_exes: Dict[str, List[str]] = {}
    for cid in sorted({str(t["cid"]) for t in tasks}):
        by_cid_exes[cid] = filter_executables(api.expand_oids(cid))

    per_query: List[Dict[str, Any]] = []
    stage_times: Dict[str, float] = defaultdict(float)
    for task in tasks:
        cid = str(task["cid"])
        exes = by_cid_exes.get(cid) or []
        t0 = time.perf_counter_ns()
        qf_out = api.retrieve(
            "query_function",
            exes,
            {
                "query": str(task.get("prompt", "")),
                "top_k": top_k_funcs,
                "return_file_embeddings": True,
                "file_agg": func_file_agg,
                "attn_tau": func_attn_tau,
                "timing": False,
                "progress": False,
            },
        )
        ranked_files = _rank_files_from_qf_file_scores(
            qf_out,
            top_k_files=top_k_files,
            min_score=func_similarity_threshold,
        )
        if not ranked_files:
            ranked_files = _aggregate_functions_to_files(
                qf_out, top_k_files=top_k_files
            )
        q_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
        stage_times["query_function"] += q_ms
        ranked = [r.get("oid") for r in ranked_files if isinstance(r, dict)]
        rank = _rank_from_oid_list(ranked, str(task.get("gold_oid", "")))
        if rank is None:
            rank = top_k_files + 1
        per_query.append(
            {
                "task_id": task.get("task_id"),
                "pair_id": task.get("pair_id"),
                "variant_id": task.get("variant_id"),
                "cid": cid,
                "collection": task.get("collection"),
                "component": task.get("component"),
                "query": task.get("prompt"),
                "gold_oid": task.get("gold_oid"),
                "rank": rank,
                "top_k_oids": ranked[:top_k_files],
                "runtime_ms": float(f"{q_ms:.3f}"),
            }
        )

    return _finalize_method_result(
        method="func_emb_tool",
        representation=None,
        retriever="func",
        params={
            "top_k_files": top_k_files,
            "top_k_funcs": top_k_funcs,
            "func_file_agg": func_file_agg,
            "func_attn_tau": func_attn_tau,
            "func_similarity_threshold": func_similarity_threshold,
        },
        top_k_files=top_k_files,
        per_query=per_query,
        one_time_doc_ms=0.0,
        one_time_index_ms=0.0,
        stage_times=stage_times,
        ci_opts=opts,
    )


def _run_fuse_e_tool_method(
    tasks: List[Dict[str, Any]], opts: Dict[str, Any]
) -> Dict[str, Any]:
    # Ablation: enforce the same dense mechanism used by `dense_tool`, but over R2 packed docs.
    return _run_doc_tool_method(
        method="fuse_e_tool",
        representation="r2_packed",
        retriever="dense_chunked",
        tasks=tasks,
        opts=opts,
    )


def _run_fuse_ablate_tool_method(
    tasks: List[Dict[str, Any]], opts: Dict[str, Any]
) -> Dict[str, Any]:
    # Backwards compatibility (renamed to fuse_e_tool).
    return _run_fuse_e_tool_method(tasks, opts)


def _run_fuse_tool_method(
    tasks: List[Dict[str, Any]], opts: Dict[str, Any]
) -> Dict[str, Any]:
    """
    Run the core fuse analyzer with BM25-confidence gating enabled.
    This is the default "FUSE" tool-level method.
    """
    top_k_files = _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
    fuse_opts = _extract_paper_opts(opts)
    # Enforce canonical FUSE behavior (confidence gate enabled).
    # This method is not an ablation; ablations should use different methods/flags.
    fuse_opts["ablate_no_gate"] = False
    fuse_opts["ablate_bm25_only"] = False

    per_query: List[Dict[str, Any]] = []
    stage_times: Dict[str, float] = defaultdict(float)

    for task in tasks:
        cid = str(task.get("cid", "") or "")
        prompt = str(task.get("prompt", "") or "")
        if not cid or not prompt:
            continue

        t0 = time.perf_counter_ns()
        out = _call_fuse(
            cid=cid,
            query=prompt,
            top_k=top_k_files,
            fuse_opts=fuse_opts,
        )
        q_ms = (time.perf_counter_ns() - t0) / 1_000_000.0
        # Keep legacy key for older analysis scripts.
        stage_times["fuse_hybrid"] += q_ms
        stage_times["fuse_confidence_gate"] += q_ms

        if isinstance(out, dict) and out.get("error"):
            return {"method": "fuse_tool", "error": str(out.get("error"))}

        ranked_files = _extract_file_candidates_from_fuse(out, top_k=top_k_files)
        ranked = [r.get("oid") for r in ranked_files if isinstance(r, dict)]

        rank = _rank_from_oid_list(ranked, str(task.get("gold_oid", "")))
        if rank is None:
            rank = top_k_files + 1

        per_query.append(
            {
                "task_id": task.get("task_id"),
                "pair_id": task.get("pair_id"),
                "variant_id": task.get("variant_id"),
                "cid": cid,
                "collection": task.get("collection"),
                "component": task.get("component"),
                "query": prompt,
                "gold_oid": task.get("gold_oid"),
                "rank": rank,
                "top_k_oids": ranked[:top_k_files],
                "runtime_ms": float(f"{q_ms:.3f}"),
            }
        )

    return _finalize_method_result(
        method="fuse_tool",
        representation="r2_packed",
        retriever="dense_chunked+bm25_gate",
        params={
            "top_k_files": top_k_files,
            "confidence_gate_enabled": True,
            "ablate_no_gate": False,
            "ablate_bm25_only": False,
            # Legacy fields (keep stable for existing result parsers).
            "hybrid_enable": True,
            "hybrid_selector": "confidence_race",
        },
        top_k_files=top_k_files,
        per_query=per_query,
        one_time_doc_ms=0.0,
        one_time_index_ms=0.0,
        stage_times=stage_times,
        ci_opts=opts,
    )


def _run_eval_method(
    method: str,
    tasks: List[Dict[str, Any]],
    opts: Dict[str, Any],
) -> Dict[str, Any]:
    if method == "bm25_tool":
        return _run_doc_tool_method(
            method=method,
            representation="r0_raw",
            retriever="bm25",
            tasks=tasks,
            opts=opts,
        )
    if method == "dense_tool":
        return _run_doc_tool_method(
            method=method,
            representation="r0_raw",
            retriever="dense_chunked",
            tasks=tasks,
            opts=opts,
        )
    if method == "bm25_ce_tool":
        ce_opts = dict(opts)
        if "rerank_candidate_ks" not in ce_opts:
            k = _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
            ce_opts["rerank_candidate_ks"] = str(min(50, k))
        if "rerank_eval_k" not in ce_opts:
            k = _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
            ce_opts["rerank_eval_k"] = int(min(50, k))
        return _run_doc_tool_method(
            method=method,
            representation="r0_raw",
            retriever="bm25_ce",
            tasks=tasks,
            opts=ce_opts,
        )
    if method == "func_emb_tool":
        return _run_func_tool_method(tasks, opts)
    if method == "fuse_tool":
        return _run_fuse_tool_method(tasks, opts)
    if method == "fuse_e_tool":
        return _run_fuse_e_tool_method(tasks, opts)
    # Backwards compatibility (renamed to fuse_tool).
    if method == "fuse_bm25_gate_tool":
        return _run_fuse_tool_method(tasks, opts)
    # Backwards compatibility (renamed to fuse_e_tool).
    if method == "fuse_ablate_tool":
        return _run_fuse_e_tool_method(tasks, opts)
    return {"method": method, "error": f"Unknown method '{method}'."}


def _merge_e1_per_query(
    tasks: List[Dict[str, Any]],
    method_results: Dict[str, Dict[str, Any]],
) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    by_method: Dict[str, Dict[str, Dict[str, Any]]] = {}
    for method, result in method_results.items():
        per_query = result.get("per_query") if isinstance(result, dict) else None
        if not isinstance(per_query, list):
            continue
        by_method[method] = {
            str(r.get("task_id")): r
            for r in per_query
            if isinstance(r, dict) and r.get("task_id")
        }

    for task in tasks:
        task_id = str(task.get("task_id"))
        row = {
            "task_id": task_id,
            "cid": task.get("cid"),
            "collection": task.get("collection"),
            "component": task.get("component"),
            "query": task.get("prompt"),
            "gold_oid": task.get("gold_oid"),
            "results": {},
        }
        for method in method_results.keys():
            q = (by_method.get(method) or {}).get(task_id)
            if q is None:
                continue
            row["results"][method] = {
                "rank": q.get("rank"),
                "top_k_oids": q.get("top_k_oids"),
                "runtime_ms": q.get("runtime_ms"),
            }
        out.append(row)
    return out


def _compute_rep_doc_stats(
    ground_truth: Dict[str, Dict[str, str]],
    rep: str,
    opts: Dict[str, Any],
) -> Dict[str, Any]:
    token_lens: List[int] = []
    empty_docs = 0
    total_docs = 0
    errors: List[str] = []
    for cid in sorted(ground_truth.keys(), key=lambda c: api.get_colname_from_oid(c)):
        docs, _, err = _build_docs_for_collection_with_timing(cid, rep, opts)
        if err or docs is None:
            errors.append(f"{api.get_colname_from_oid(cid)}: {err or 'failed'}")
            continue
        for text in docs.values():
            toks = _factorized_doc_tokens(str(text or ""), rep)
            total_docs += 1
            token_lens.append(len(toks))
            if len(toks) == 0:
                empty_docs += 1

    if total_docs <= 0:
        return {
            "representation": rep,
            "error": "; ".join(errors) if errors else "No docs.",
        }

    token_lens_sorted = sorted(token_lens)
    return {
        "representation": rep,
        "doc_count": total_docs,
        "empty_doc_count": empty_docs,
        "avg_tokens_per_doc": float(f"{(sum(token_lens) / max(total_docs, 1)):.3f}"),
        "median_tokens_per_doc": float(f"{statistics.median(token_lens_sorted):.3f}"),
        "p90_tokens_per_doc": float(
            f"{_percentile(token_lens_sorted, 0.9) or 0.0:.3f}"
        ),
    }


def _compute_r2_deltas_from_cells(cells: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    by_ret_rep: Dict[str, Dict[str, Dict[str, Any]]] = defaultdict(dict)
    for c in cells:
        if not isinstance(c, dict):
            continue
        ret = str(c.get("retriever") or "")
        rep = str(c.get("representation") or "")
        if not ret or not rep:
            continue
        by_ret_rep[ret][rep] = c

    rows: List[Dict[str, Any]] = []
    for ret, rep_map in sorted(by_ret_rep.items(), key=lambda kv: kv[0]):
        r2 = rep_map.get("r2_packed")
        if not isinstance(r2, dict) or r2.get("error"):
            continue
        gm2 = r2.get("global_metrics") or {}
        t2 = r2.get("timing") or {}
        row: Dict[str, Any] = {"retriever": ret}
        for base_rep, label in (
            ("r0_raw", "delta_r2_minus_r0"),
            ("r1_norm", "delta_r2_minus_r1"),
        ):
            b = rep_map.get(base_rep)
            if not isinstance(b, dict) or b.get("error"):
                row[label] = None
                continue
            gmb = b.get("global_metrics") or {}
            tb = b.get("timing") or {}
            row[label] = {
                "MRR": _metric_delta(
                    _safe_float(gm2.get("MRR")), _safe_float(gmb.get("MRR"))
                ),
                "P@1": _metric_delta(
                    _safe_float(gm2.get("P@1")), _safe_float(gmb.get("P@1"))
                ),
                "Hit@2": _metric_delta(
                    _safe_float(gm2.get("Hit@2")), _safe_float(gmb.get("Hit@2"))
                ),
                "Hit@5": _metric_delta(
                    _safe_float(gm2.get("Hit@5")), _safe_float(gmb.get("Hit@5"))
                ),
                "Mean": _metric_delta(
                    _safe_float(gm2.get("Mean")), _safe_float(gmb.get("Mean"))
                ),
                "query_time_ms_avg": _metric_delta(
                    _safe_float(t2.get("query_time_ms_avg")),
                    _safe_float(tb.get("query_time_ms_avg")),
                ),
            }
        rows.append(row)
    return rows


def _write_artifact(
    outdir: str, filename: str, payload: Dict[str, Any]
) -> Optional[str]:
    if not outdir:
        return None
    try:
        outpath = Path(outdir).expanduser()
        outpath.mkdir(parents=True, exist_ok=True)
        return _write_json(outpath, filename, payload)
    except Exception:
        return None


def agent_eval_e1(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    E1: End-to-End Effectiveness (tool-level comparison).

    Methods:
      - bm25_tool   (BM25 over R0 raw strings)
      - dense_tool  (chunked bi-encoder retrieval over R0 raw strings)
      - bm25_ce_tool (BM25->CrossEncoder rerank over R0 raw strings)
      - func_emb_tool (function embeddings aggregated to files)
      - fuse_tool   (FUSE primitive: fuse analyzer + BM25-confidence gating)
    Defaults to bm25_tool,dense_tool,bm25_ce_tool,func_emb_tool,fuse_tool.
    """
    ground_truth, prompt_map, err = _load_eval_inputs(opts)
    if err:
        return {"error": err}
    if ground_truth is None or prompt_map is None:
        return {"error": "Failed loading evaluation inputs."}

    methods, method_err = _parse_named_ids_opt(
        opts,
        key="methods",
        default_ids=E1_METHODS,
        allowed_ids=TOOL_METHOD_IDS,
        aliases=E1_METHOD_ALIASES,
    )
    if method_err:
        return {"error": method_err}
    tasks = _build_eval_tasks(ground_truth, prompt_map)

    results: Dict[str, Dict[str, Any]] = {}
    for method in methods or []:
        results[method] = _run_eval_method(method, tasks, opts)

    payload = {
        "experiment": "E1",
        "candidate_filter": "executables_only_excluding_.so_and_.ko",
        "task_count": len(tasks),
        "methods": methods,
        "top_k_files": _as_int_opt(
            opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1
        ),
        "per_method": results,
        "per_query": _merge_e1_per_query(tasks, results),
    }
    artifact = _write_artifact(
        str(opts.get("outdir", "") or "").strip(), "e1_results.json", payload
    )
    if artifact:
        payload["artifact"] = artifact
    return payload


def agent_eval_e2(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    E2: Gate ablation (BM25 vs FUSE vs FUSE-E).

    Methods:
      - bm25_tool   (BM25 over R0 raw strings)
      - fuse_tool   (FUSE primitive: fuse analyzer + BM25-confidence gating)
      - fuse_e_tool (FUSE-E: packed-surrogate dense retrieval only; gate disabled)
    Defaults to bm25_tool,fuse_tool,fuse_e_tool.
    """
    ground_truth, prompt_map, err = _load_eval_inputs(opts)
    if err:
        return {"error": err}
    if ground_truth is None or prompt_map is None:
        return {"error": "Failed loading evaluation inputs."}

    methods, method_err = _parse_named_ids_opt(
        opts,
        key="methods",
        default_ids=E2_METHODS,
        allowed_ids=TOOL_METHOD_IDS,
        aliases=E1_METHOD_ALIASES,
    )
    if method_err:
        return {"error": method_err}
    tasks = _build_eval_tasks(ground_truth, prompt_map)

    results: Dict[str, Dict[str, Any]] = {}
    for method in methods or []:
        results[method] = _run_eval_method(method, tasks, opts)

    payload = {
        "experiment": "E2",
        "candidate_filter": "executables_only_excluding_.so_and_.ko",
        "task_count": len(tasks),
        "methods": methods,
        "top_k_files": _as_int_opt(
            opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1
        ),
        "per_method": results,
        "per_query": _merge_e1_per_query(tasks, results),
    }
    artifact = _write_artifact(
        str(opts.get("outdir", "") or "").strip(), "e2_gate_ablation.json", payload
    )
    if artifact:
        payload["artifact"] = artifact
    return payload


def agent_eval_e3(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    E3: Factorized representation controls (R0/R1/R2 under fixed retrievers).
    """
    ground_truth, prompt_map, err = _load_eval_inputs(opts)
    if err:
        return {"error": err}
    if ground_truth is None or prompt_map is None:
        return {"error": "Failed loading evaluation inputs."}

    reps, rep_err = _parse_representation_ids_opt(opts)
    if rep_err:
        return {"error": rep_err}
    retrievers, ret_err = _parse_named_ids_opt(
        opts,
        key="retrievers",
        default_ids=E2_RETRIEVERS,
        allowed_ids=E2_RETRIEVERS,
        aliases=E2_RETRIEVER_ALIASES,
    )
    if ret_err:
        return {"error": ret_err}

    tasks = _build_eval_tasks(ground_truth, prompt_map)
    doc_stats = {
        rep: _compute_rep_doc_stats(ground_truth, rep, opts) for rep in reps or []
    }
    cells: List[Dict[str, Any]] = []
    for retriever_public in retrievers or []:
        retriever_internal = E2_RETRIEVER_INTERNAL[retriever_public]
        for rep in reps or []:
            cell = _run_doc_tool_method(
                method=f"{retriever_public}@{rep}",
                representation=rep,
                retriever=retriever_internal,
                tasks=tasks,
                opts=opts,
            )
            if isinstance(cell, dict):
                cell["retriever"] = retriever_public
                cell["internal_retriever"] = retriever_internal
                cell["representation"] = rep
                cell["doc_stats"] = doc_stats.get(rep, {})
            cells.append(cell)

    payload = {
        "experiment": "E3",
        "candidate_filter": "executables_only_excluding_.so_and_.ko",
        "task_count": len(tasks),
        "representations": reps,
        "retrievers": retrievers,
        "cells": cells,
        "r2_deltas": _compute_r2_deltas_from_cells(cells),
    }
    artifact = _write_artifact(
        str(opts.get("outdir", "") or "").strip(), "e3_rep_matrix.json", payload
    )
    if artifact:
        payload["artifact"] = artifact
    return payload


def _hit_curve_from_ranks(ranks: Sequence[int], ks: Sequence[int]) -> Dict[str, float]:
    n = len(ranks)
    if n <= 0:
        return {str(k): 0.0 for k in ks}
    return {str(k): (sum(1 for r in ranks if r <= k) / n) for k in ks}


def _parse_hit_ks(opts: Dict[str, Any]) -> List[int]:
    raw = str(opts.get("hit_ks", ",".join(str(x) for x in E3_HIT_K_DEFAULT)) or "")
    ks = _parse_int_csv(raw)
    return ks if ks else list(E3_HIT_K_DEFAULT)


def agent_eval_e4(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    E4: Agent-centric tradeoff (Hit@K vs warm query latency).
    Defaults to bm25_tool,bm25_ce_tool,func_emb_tool,fuse_tool.
    """
    ground_truth, prompt_map, err = _load_eval_inputs(opts)
    if err:
        return {"error": err}
    if ground_truth is None or prompt_map is None:
        return {"error": "Failed loading evaluation inputs."}
    methods, method_err = _parse_named_ids_opt(
        opts,
        key="methods",
        default_ids=E4_METHODS,
        allowed_ids=TOOL_METHOD_IDS,
        aliases=E1_METHOD_ALIASES,
    )
    if method_err:
        return {"error": method_err}
    tasks = _build_eval_tasks(ground_truth, prompt_map)
    ks = _parse_hit_ks(opts)
    repeats = _as_int_opt(opts, "latency_repeats", 1, min_value=1)

    per_method: Dict[str, Any] = {}
    for method in methods or []:
        _ = _run_eval_method(method, tasks, opts)
        run_result = _run_eval_method(method, tasks, opts)
        if run_result.get("error"):
            per_method[method] = run_result
            continue
        pq = run_result.get("per_query") or []
        if not isinstance(pq, list):
            per_method[method] = {
                "error": f"Invalid per_query output for method '{method}'."
            }
            continue

        # Optional repeat sampling for latency-only refinement.
        if repeats > 1:
            by_task: Dict[str, Dict[str, Any]] = {
                str(r.get("task_id")): dict(r) for r in pq if isinstance(r, dict)
            }
            latency_samples: Dict[str, List[float]] = {
                k: [float(v.get("runtime_ms", 0.0) or 0.0)] for k, v in by_task.items()
            }
            for _rep in range(repeats - 1):
                nxt = _run_eval_method(method, tasks, opts)
                for r in nxt.get("per_query") or []:
                    if not isinstance(r, dict):
                        continue
                    tid = str(r.get("task_id"))
                    if tid in latency_samples:
                        latency_samples[tid].append(
                            float(r.get("runtime_ms", 0.0) or 0.0)
                        )
            for tid, samples in latency_samples.items():
                by_task[tid]["runtime_ms"] = float(f"{statistics.median(samples):.3f}")
            pq = [
                by_task[str(t.get("task_id"))]
                for t in tasks
                if str(t.get("task_id")) in by_task
            ]

        ranks = [
            int(
                r.get(
                    "rank",
                    _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
                    + 1,
                )
            )
            for r in pq
        ]
        latencies = [float(r.get("runtime_ms", 0.0) or 0.0) for r in pq]
        per_method[method] = {
            "method": method,
            "attempted_queries": len(ranks),
            "hit_at_k": _hit_curve_from_ranks(ranks, ks),
            "latency_ms": {
                "mean": float(f"{(sum(latencies) / max(len(latencies), 1)):.3f}"),
                "median": float(
                    f"{statistics.median(latencies) if latencies else 0.0:.3f}"
                ),
            },
            "expected_expansions": float(f"{(sum(ranks) / max(len(ranks), 1)):.3f}"),
            "global_metrics": _metrics_from_rank_values(ranks),
            "ci95": _bootstrap_ci_from_ranks(ranks, opts),
        }

    payload = {
        "experiment": "E4",
        "candidate_filter": "executables_only_excluding_.so_and_.ko",
        "task_count": len(tasks),
        "hit_ks": ks,
        "latency_repeats": repeats,
        "methods": methods,
        "per_method": per_method,
    }
    artifact = _write_artifact(
        str(opts.get("outdir", "") or "").strip(), "e4_tradeoff.json", payload
    )
    if artifact:
        payload["artifact"] = artifact
    return payload


def _load_prompt_variants(
    path: str,
) -> Tuple[Optional[Dict[str, List[str]]], Optional[str]]:
    try:
        raw = json.loads(Path(path).read_text())
    except Exception as e:
        return None, f"Failed to load prompt_variants_path JSON: {e}"
    if not isinstance(raw, dict):
        return None, "prompt_variants_path must map component -> [variants]."
    out: Dict[str, List[str]] = {}
    for comp, vals in raw.items():
        if not isinstance(comp, str):
            continue
        if isinstance(vals, str):
            vals = [vals]
        if not isinstance(vals, list):
            continue
        norm = [str(v).strip() for v in vals if isinstance(v, str) and str(v).strip()]
        if norm:
            out[comp] = norm
    if not out:
        return None, "No usable variants in prompt_variants_path."
    return out, None


def agent_eval_e5(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    E5: Query variation robustness using provided prompt_variants JSON.
    Defaults to bm25_tool,bm25_ce_tool,func_emb_tool,fuse_tool.
    """
    ground_truth, prompt_map, err = _load_eval_inputs(opts)
    if err:
        return {"error": err}
    if ground_truth is None or prompt_map is None:
        return {"error": "Failed loading evaluation inputs."}

    variants_path = str(
        (opts.get("prompt_variants_path") or opts.get("variants_path") or "").strip()
    )
    if not variants_path:
        return {"error": "Provide prompt_variants_path."}
    variants_map, var_err = _load_prompt_variants(variants_path)
    if var_err:
        return {"error": var_err}
    if variants_map is None:
        return {"error": "Failed loading prompt variants."}

    methods, method_err = _parse_named_ids_opt(
        opts,
        key="methods",
        default_ids=E5_METHODS,
        allowed_ids=TOOL_METHOD_IDS,
        aliases=E1_METHOD_ALIASES,
    )
    if method_err:
        return {"error": method_err}
    stable_k = _as_int_opt(opts, "stable_k", 5, min_value=1)

    tasks: List[Dict[str, Any]] = []
    for cid in sorted(ground_truth.keys(), key=lambda c: api.get_colname_from_oid(c)):
        colname = api.get_colname_from_oid(cid)
        for component, gold_oid in sorted(
            ground_truth[cid].items(), key=lambda kv: kv[0]
        ):
            variants = variants_map.get(component) or []
            for idx, variant_prompt in enumerate(variants):
                tasks.append(
                    {
                        "task_id": f"{cid}:{component}:v{idx}",
                        "pair_id": f"{cid}:{component}",
                        "variant_id": idx,
                        "cid": cid,
                        "collection": colname,
                        "component": component,
                        "prompt": variant_prompt,
                        "gold_oid": gold_oid,
                    }
                )

    per_method: Dict[str, Any] = {}
    for method in methods or []:
        result = _run_eval_method(method, tasks, opts)
        if result.get("error"):
            per_method[method] = result
            continue
        pq = result.get("per_query") or []
        pair_ranks: Dict[str, List[int]] = defaultdict(list)
        per_component: Dict[str, Dict[str, Any]] = defaultdict(
            lambda: {"ranks": [], "pairs": 0}
        )
        for row in pq:
            if not isinstance(row, dict):
                continue
            pair_id = str(row.get("pair_id") or "")
            component = str(row.get("component") or "")
            rank = int(
                row.get(
                    "rank",
                    _as_int_opt(opts, "top_k_files", DEFAULT_TOP_K_FILES, min_value=1)
                    + 1,
                )
            )
            if pair_id:
                pair_ranks[pair_id].append(rank)
            if component:
                per_component[component]["ranks"].append(rank)

        pair_count = len(pair_ranks)
        all_ok = sum(
            1 for rs in pair_ranks.values() if rs and all(r <= stable_k for r in rs)
        )
        any_ok = sum(
            1 for rs in pair_ranks.values() if rs and any(r <= stable_k for r in rs)
        )
        for comp in per_component.keys():
            per_component[comp]["pairs"] = sum(
                1 for pid in pair_ranks.keys() if pid.split(":", 1)[1] == comp
            )
            per_component[comp]["rank_distribution"] = per_component[comp].pop("ranks")

        result["stability"] = {
            "stable_k": stable_k,
            "pairs": pair_count,
            f"all_variants_hit@{stable_k}": (
                (all_ok / pair_count) if pair_count else 0.0
            ),
            f"any_variant_hit@{stable_k}": (any_ok / pair_count) if pair_count else 0.0,
        }
        result["per_component"] = per_component
        per_method[method] = result

    payload = {
        "experiment": "E5",
        "candidate_filter": "executables_only_excluding_.so_and_.ko",
        "prompt_variants_path": variants_path,
        "stable_k": stable_k,
        "methods": methods,
        "task_count": len(tasks),
        "per_method": per_method,
    }
    artifact = _write_artifact(
        str(opts.get("outdir", "") or "").strip(), "e5_query_variation.json", payload
    )
    if artifact:
        payload["artifact"] = artifact
    return payload


def agent_eval_all(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Run E1/E2/E3/E4/E5 and write all evaluation artifacts.
    Uses the same per-experiment default method lists unless an explicit methods list is provided.
    """
    started_ns = time.time_ns()
    run_opts = dict(opts)
    run_opts.pop("outdir", None)

    e1_opts = dict(run_opts)
    e2_opts = dict(run_opts)
    e3_opts = dict(run_opts)
    e4_opts = dict(run_opts)
    e5_opts = dict(run_opts)

    e1 = agent_eval_e1(args, e1_opts)
    e2 = agent_eval_e2(args, e2_opts)
    e3 = agent_eval_e3(args, e3_opts)
    e4 = agent_eval_e4(args, e4_opts)
    e5 = agent_eval_e5(args, e5_opts)

    payload = {
        "suite": "fuse_eval_all",
        "toolset": FUSE_TOOLSET,
        "started_unix_ns": started_ns,
        "elapsed_ms": float(f"{(time.time_ns() - started_ns) / 1_000_000.0:.3f}"),
        "results": {
            "e1": e1,
            "e2": e2,
            "e3": e3,
            "e4": e4,
            "e5": e5,
        },
    }

    outdir = str(opts.get("outdir", "") or "").strip()
    artifacts: Dict[str, str] = {}
    if outdir:
        mapping = [
            ("e1", "e1_results.json", e1),
            ("e2", "e2_gate_ablation.json", e2),
            ("e3", "e3_rep_matrix.json", e3),
            ("e4", "e4_tradeoff.json", e4),
            ("e5", "e5_query_variation.json", e5),
            ("all", "eval_all.json", payload),
        ]
        for k, fname, obj in mapping:
            p = _write_artifact(
                outdir, fname, obj if isinstance(obj, dict) else {"value": obj}
            )
            if p:
                artifacts[k] = p
    if artifacts:
        payload["artifacts"] = artifacts
    return payload


# Public plugin entrypoints (legacy paper_* orchestration intentionally omitted).
exports = [
    agent_eval_e1,
    agent_eval_e2,
    agent_eval_e3,
    agent_eval_e4,
    agent_eval_e5,
    agent_eval_all,
]
