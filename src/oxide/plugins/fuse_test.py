import json
import time
import logging
import re
import hashlib
import math
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
    "ablate_noise_filter",
    "ablate_redundancy",
    "ablate_idf",
    "pack_budget_tokens",
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
DEFAULT_RERANK_CANDIDATE_KS = "20,50,100"
DEFAULT_RERANK_EVAL_K = 50

DEFAULT_RRF_K = 60

_SENTENCE_MODEL_CACHE: Dict[Tuple[str, bool], Any] = {}
_CROSS_ENCODER_CACHE: Dict[Tuple[str, bool], Any] = {}
_HF_TOKENIZER_CACHE: Dict[Tuple[str, bool], Any] = {}
_HF_MODEL_CACHE: Dict[Tuple[str, str, bool], Any] = {}


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
    text_mode = str(opts.get("text_mode", DEFAULT_TEXT_MODE) or DEFAULT_TEXT_MODE).strip().lower()
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


def _load_eval_inputs(
    opts: Dict[str, Any],
) -> Tuple[Optional[Dict[str, Dict[str, str]]], Optional[Dict[str, str]], Optional[str]]:
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
    ref_ms = _safe_float((ref or {}).get("avg_retrieval_ms")) if isinstance(ref, dict) else None

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
        speedup = (ref_ms / ms) if (ref_ms is not None and ms is not None and ms > 0.0) else None

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
                sum((r if r is not None else (top_k_files + 1)) for r in ranks_by_component.values())
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
            per_collection[colname] = {"metrics": {}, "ranks_by_prompt": ranks_by_component}

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
        raise RuntimeError("sentence_transformers is not available; install sentence-transformers.")
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
        raise RuntimeError("sentence_transformers CrossEncoder is not available; install sentence-transformers.")
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
        raise RuntimeError("transformers tokenizer is not available; install transformers.")
    tok = AutoTokenizer.from_pretrained(model_id, local_files_only=bool(local_files_only))
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
            raise RuntimeError("transformers AutoModelForMaskedLM is not available; install transformers.")
        model = AutoModelForMaskedLM.from_pretrained(
            model_id, local_files_only=bool(local_files_only)
        )
    else:
        if AutoModel is None:
            raise RuntimeError("transformers AutoModel is not available; install transformers.")
        model = AutoModel.from_pretrained(model_id, local_files_only=bool(local_files_only))
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


def agent_paper_compare(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Compare paper implementation against selected baseline methods.

    opts:
      - comp_path, prompt_path (required)
      - methods (optional): comma-separated method IDs or aliases; use "all" for all methods
        default: paper_idf_pack_auto,bm25_raw,bm25_norm,function_embeddings
        aliases: fuse->paper_idf_pack_auto, splade->splade_style,
                 dense->dense_chunked, colbert->colbert_style
      - top_k_files (default 50)
      - top_k_funcs (default 1) for function baseline
      - text_mode in {raw,norm} (default: norm) for new text baselines
      - local_files_only (default true): do not download missing HF model assets
      - function baseline options:
          func_file_agg in {top1, mean, attn} (default: top1)
          func_attn_tau (default: 0.07)
          func_similarity_threshold (default: 0.0)
      - rm3 options:
          rm3_fb_docs, rm3_fb_terms, rm3_orig_weight
      - bm25f options:
          bm25f_name_weight, bm25f_string_weight, bm25f_k1, bm25f_b_name, bm25f_b_string
      - chargram options:
          chargram_min_n, chargram_max_n
      - splade options:
          splade_model_id, splade_max_length, splade_doc_top_terms, splade_query_top_terms
      - dense chunk options:
          dense_model_id, dense_chunk_tokens, dense_chunk_overlap
      - colbert options:
          colbert_model_id, colbert_max_length, colbert_doc_token_cap
      - reranker options:
          rerank_model_id, rerank_candidate_ks, rerank_eval_k
      - rrf options:
          rrf_k, rrf_depth
      - paper mode options:
          string_emb_batch_size, debug_select,
          ablate_noise_filter, ablate_redundancy, ablate_idf, pack_budget_tokens
      - outdir (optional): write JSON artifact
    """
    comp_path = opts.get("comp_path")
    prompt_path = opts.get("prompt_path")
    if not comp_path or not prompt_path:
        return {"error": "Provide comp_path and prompt_path."}

    top_k_files = int(
        opts.get("top_k_files", DEFAULT_TOP_K_FILES) or DEFAULT_TOP_K_FILES
    )
    top_k_funcs = int(opts.get("top_k_funcs", 1) or 1)
    methods, method_err = _parse_methods_opt(
        opts,
        default_methods=DEFAULT_COMPARE_METHODS,
        allowed_methods=ALL_COMPARE_METHODS,
    )
    if method_err:
        return {"error": method_err}
    text_mode, text_mode_err = _parse_text_mode(opts)
    if text_mode_err:
        return {"error": text_mode_err}

    paper_opts = dict(opts)
    paper_opts["toolset"] = FUSE_TOOLSET

    results: Dict[str, Any] = {}
    for method in methods or []:
        if method == "paper_idf_pack_auto":
            results[method] = agent_batch(args, paper_opts)
        elif method == "bm25_raw":
            results[method] = _batch_bm25(args, opts, normalize=False)
        elif method == "bm25_norm":
            results[method] = _batch_bm25(args, opts, normalize=True)
        elif method == "function_embeddings":
            results[method] = _batch_function_embeddings(args, opts)
        elif method == "bm25_rm3":
            results[method] = _batch_bm25_rm3(args, opts)
        elif method == "bm25f":
            results[method] = _batch_bm25f(args, opts)
        elif method == "chargram_bm25":
            results[method] = _batch_chargram_bm25(args, opts)
        elif method == "splade_style":
            results[method] = _batch_splade_style(args, opts)
        elif method == "dense_chunked":
            results[method] = _batch_dense_chunked(args, opts)
        elif method == "colbert_style":
            results[method] = _batch_colbert_style(args, opts)
        elif method == "bm25_rerank_ce":
            results[method] = _batch_bm25_rerank_ce(args, opts)
        elif method == "dense_rerank_ce":
            results[method] = _batch_dense_rerank_ce(args, opts)
        elif method == "bm25_dense_rrf":
            results[method] = _batch_bm25_dense_rrf(args, opts)
        elif method == "bm25_splade_rrf":
            results[method] = _batch_bm25_splade_rrf(args, opts)
        else:
            results[method] = {"error": f"Method '{method}' is not implemented."}

    payload = {
        "toolset": FUSE_TOOLSET,
        "use_tags": False,
        "top_k_files": top_k_files,
        "top_k_funcs": top_k_funcs,
        "text_mode": text_mode,
        "methods": methods,
        "results": results,
        "comparison_table": _build_compare_table(
            results,
            reference_method="paper_idf_pack_auto",
        ),
    }
    _write_json_if_requested(opts, "paper_compare.json", payload)
    return payload


def agent_paper_ablation_compare(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Run paper-focused ablations on the fuse implementation only.

    Variants:
      - full_auto: default idf_pack_auto behavior
      - no_idf: replace IDF weighting with uniform term weights
      - no_noise_filter: disable junk/noise filtering
      - no_redundancy: disable near-duplicate suppression

    opts:
      - comp_path, prompt_path (required)
      - top_k_files (default 50)
      - string_emb_batch_size, debug_select
      - pack_budget_tokens (optional)
      - outdir (optional): write JSON artifact
    """
    comp_path = opts.get("comp_path")
    prompt_path = opts.get("prompt_path")
    if not comp_path or not prompt_path:
        return {"error": "Provide comp_path and prompt_path."}

    top_k_files = int(
        opts.get("top_k_files", DEFAULT_TOP_K_FILES) or DEFAULT_TOP_K_FILES
    )

    base_opts = dict(opts)
    base_opts["toolset"] = FUSE_TOOLSET
    base_opts["ablate_noise_filter"] = False
    base_opts["ablate_redundancy"] = False
    base_opts["ablate_idf"] = False

    variants: Dict[str, Dict[str, Any]] = {
        "full_auto": {},
        "no_idf": {"ablate_idf": True},
        "no_noise_filter": {"ablate_noise_filter": True},
        "no_redundancy": {"ablate_redundancy": True},
    }

    results: Dict[str, Any] = {}
    for name, overrides in variants.items():
        run_opts = dict(base_opts)
        run_opts.update(overrides)
        out = agent_batch(args, run_opts)
        if isinstance(out, dict):
            out["ablation_opts"] = {
                "ablate_noise_filter": bool(run_opts.get("ablate_noise_filter", False)),
                "ablate_redundancy": bool(run_opts.get("ablate_redundancy", False)),
                "ablate_idf": bool(run_opts.get("ablate_idf", False)),
                "pack_budget_tokens": int(run_opts.get("pack_budget_tokens", 0) or 0),
            }
        results[name] = out

    # Add per-variant deltas vs full_auto for quick attribution.
    full = results.get("full_auto") if isinstance(results.get("full_auto"), dict) else {}
    full_metrics = (full.get("global_metrics") or {}) if isinstance(full, dict) else {}
    full_avg_ms = float(full.get("avg_retrieval_ms", 0.0) or 0.0) if isinstance(full, dict) else 0.0

    def _metric_delta(v: Any, b: Any) -> Optional[float]:
        try:
            return float(v) - float(b)
        except Exception:
            return None

    for name, out in results.items():
        if not isinstance(out, dict):
            continue
        m = out.get("global_metrics") or {}
        if not isinstance(m, dict):
            continue
        deltas = {
            "MRR": _metric_delta(m.get("MRR"), full_metrics.get("MRR")),
            "P@1": _metric_delta(m.get("P@1"), full_metrics.get("P@1")),
            "Hit@2": _metric_delta(m.get("Hit@2"), full_metrics.get("Hit@2")),
            "Hit@5": _metric_delta(m.get("Hit@5"), full_metrics.get("Hit@5")),
            "Mean": _metric_delta(m.get("Mean"), full_metrics.get("Mean")),
            "avg_retrieval_ms": _metric_delta(out.get("avg_retrieval_ms"), full_avg_ms),
        }
        out["delta_vs_full_auto"] = deltas

    payload = {
        "toolset": FUSE_TOOLSET,
        "use_tags": False,
        "top_k_files": top_k_files,
        "results": results,
    }
    _write_json_if_requested(opts, "paper_ablations.json", payload)
    return payload


def agent_paper_budget_sweep(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Sweep packing budget for the paper implementation.

    opts:
      - comp_path, prompt_path (required)
      - top_k_files
      - budgets: comma-separated ints (default: "64,96,128,192,256")
      - string_emb_batch_size, debug_select
      - outdir (optional): write JSON artifact
    """
    comp_path = opts.get("comp_path")
    prompt_path = opts.get("prompt_path")
    if not comp_path or not prompt_path:
        return {"error": "Provide comp_path and prompt_path."}

    top_k_files = int(
        opts.get("top_k_files", DEFAULT_TOP_K_FILES) or DEFAULT_TOP_K_FILES
    )

    budget_str = str(opts.get("budgets", "64,96,128,192,256"))
    budgets: List[int] = []
    for tok in budget_str.split(","):
        tok = tok.strip()
        if not tok:
            continue
        try:
            b = int(tok)
        except ValueError:
            continue
        if b > 0:
            budgets.append(b)
    budgets = sorted(set(budgets))
    if not budgets:
        return {"error": "No valid positive budgets provided."}

    base_opts = dict(opts)
    base_opts["toolset"] = FUSE_TOOLSET
    base_opts["ablate_noise_filter"] = False
    base_opts["ablate_redundancy"] = False

    results: Dict[str, Any] = {}
    for b in budgets:
        run_opts = dict(base_opts)
        run_opts["pack_budget_tokens"] = b
        out = agent_batch(args, run_opts)
        if isinstance(out, dict):
            out["budget_tokens"] = b
        results[f"budget_{b}"] = out

    payload = {
        "toolset": FUSE_TOOLSET,
        "use_tags": False,
        "top_k_files": top_k_files,
        "budgets": budgets,
        "results": results,
    }
    _write_json_if_requested(opts, "paper_budget_sweep.json", payload)
    return payload


def agent_paper_query_variation(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Evaluate robustness to query rephrasing by running multiple prompt variants per component.

    opts:
      - comp_path (required): json mapping collection_name -> { component -> path(s) }
      - prompt_variants_path (required): json mapping component -> [prompt variants]
      - methods (optional): comma-separated subset of
          fuse,bm25_raw,bm25_norm,function_embeddings
        default: "fuse,bm25_raw,bm25_norm"
      - components (optional): comma-separated subset of components to evaluate
      - max_variants_per_component (optional): cap number of variants per component (>=1)
      - top_k_files (default 50)
      - stable_k (default 5): stability threshold for "all variants in top-k"
      - top_k_funcs (default 1) + function baseline options (if function_embeddings enabled):
          func_file_agg, func_attn_tau, func_similarity_threshold
      - outdir (optional): write JSON artifact
    """
    comp_path = opts.get("comp_path")
    prompt_variants_path = (
        (opts.get("prompt_variants_path") or opts.get("variants_path") or "").strip()
    )
    if not comp_path or not prompt_variants_path:
        return {"error": "Provide comp_path and prompt_variants_path."}

    top_k_files = int(
        opts.get("top_k_files", opts.get("top_k", DEFAULT_TOP_K_FILES))
        or DEFAULT_TOP_K_FILES
    )
    stable_k = int(opts.get("stable_k", 5) or 5)
    if stable_k <= 0:
        stable_k = 5

    methods_raw = str(opts.get("methods", "fuse,bm25_raw,bm25_norm"))
    methods = [m.strip().lower() for m in methods_raw.split(",") if m.strip()]
    if not methods:
        methods = ["fuse", "bm25_raw", "bm25_norm"]

    try:
        variants_map = json.loads(Path(prompt_variants_path).read_text())
    except Exception as e:
        return {"error": f"Failed to load prompt_variants_path JSON: {e}"}
    if not isinstance(variants_map, dict):
        return {"error": "prompt_variants_path must be a JSON object mapping component -> [variants]."}

    # Normalize variant map: keep only non-empty string prompts.
    cleaned_variants: Dict[str, List[str]] = {}
    for comp, prompts in variants_map.items():
        if not isinstance(comp, str):
            continue
        if isinstance(prompts, str):
            prompts = [prompts]
        if not isinstance(prompts, list):
            continue
        norm = [p.strip() for p in prompts if isinstance(p, str) and p.strip()]
        if norm:
            cleaned_variants[comp] = norm

    if not cleaned_variants:
        return {"error": "No usable prompt variants found (expected component -> [non-empty strings])."}

    components_str = (opts.get("components") or "").strip()
    if components_str:
        want = {c.strip() for c in components_str.split(",") if c.strip()}
        cleaned_variants = {c: v for c, v in cleaned_variants.items() if c in want}
        if not cleaned_variants:
            return {"error": "No components left after applying components filter."}

    max_variants = int(opts.get("max_variants_per_component", 0) or 0)
    if max_variants > 0:
        cleaned_variants = {c: v[:max_variants] for c, v in cleaned_variants.items()}

    ground_truth = create_ground_truth(comp_path)
    if not ground_truth:
        return {"error": "No ground truth collections loaded (check comp_path)."}

    # Metric helpers
    def _metrics_from_ranks(ranks: List[int]) -> Dict[str, Any]:
        n = len(ranks)
        if n <= 0:
            return {"attempted": 0, "P@1": 0.0, "Hit@2": 0.0, "Hit@5": 0.0, "MRR": 0.0, "Mean": 0.0}
        p1 = sum(1 for r in ranks if r == 1) / n
        h2 = sum(1 for r in ranks if r <= 2) / n
        h5 = sum(1 for r in ranks if r <= 5) / n
        mrr = sum((1.0 / r) for r in ranks) / n
        mean = sum(ranks) / n
        return {"attempted": n, "P@1": p1, "Hit@2": h2, "Hit@5": h5, "MRR": mrr, "Mean": mean}

    def _worst_rank(ranks: List[int]) -> int:
        return max(ranks) if ranks else top_k_files + 1

    def _best_rank(ranks: List[int]) -> int:
        return min(ranks) if ranks else top_k_files + 1

    # ------------------------------------------------------------------
    # Method implementations
    # ------------------------------------------------------------------
    results: Dict[str, Any] = {}

    # ------------------ FUSE ------------------
    if "fuse" in methods or "paper_idf_pack_auto" in methods:
        paper_opts = _extract_paper_opts(opts)
        per_component: Dict[str, Any] = {}
        total_ms = 0.0
        attempted = 0

        global_ranks: List[int] = []
        stable_pairs = 0
        stable_all = 0
        stable_any = 0
        worst_sum = 0.0

        for comp, prompts in cleaned_variants.items():
            per_prompt_ranks: Dict[str, List[int]] = {p: [] for p in prompts}
            ranks_by_collection: Dict[str, Dict[str, int]] = {}
            pairs = 0
            comp_stable_all = 0
            comp_stable_any = 0
            comp_worst_sum = 0.0

            for cid, golds in ground_truth.items():
                gold_oid = golds.get(comp)
                if not gold_oid:
                    continue
                colname = api.get_colname_from_oid(cid)
                ranks_this_pair: List[int] = []
                ranks_by_collection.setdefault(colname, {})

                for p in prompts:
                    t0 = time.perf_counter_ns()
                    out = _call_fuse(cid, p, top_k=top_k_files, fuse_opts=paper_opts)
                    total_ms += (time.perf_counter_ns() - t0) / 1_000_000.0
                    ranked_files = _extract_file_candidates_from_fuse(out, top_k=top_k_files)
                    oid_list = [c.get("oid") for c in ranked_files if isinstance(c, dict)]
                    try:
                        rank = oid_list.index(gold_oid) + 1
                    except ValueError:
                        rank = top_k_files + 1

                    per_prompt_ranks[p].append(rank)
                    ranks_by_collection[colname][p] = rank
                    ranks_this_pair.append(rank)

                    global_ranks.append(rank)
                    attempted += 1

                pairs += 1
                stable_pairs += 1
                if ranks_this_pair:
                    worst = _worst_rank(ranks_this_pair)
                    comp_worst_sum += float(worst)
                    worst_sum += float(worst)
                    all_ok = all(r <= stable_k for r in ranks_this_pair)
                    any_ok = any(r <= stable_k for r in ranks_this_pair)
                    comp_stable_all += int(all_ok)
                    comp_stable_any += int(any_ok)
                    stable_all += int(all_ok)
                    stable_any += int(any_ok)

            per_prompt_metrics = {p: _metrics_from_ranks(r) for p, r in per_prompt_ranks.items()}
            per_component[comp] = {
                "num_variants": len(prompts),
                "prompt_metrics": per_prompt_metrics,
                "stability": {
                    "pairs": pairs,
                    f"all_variants_hit@{stable_k}": (comp_stable_all / pairs) if pairs else 0.0,
                    f"any_variant_hit@{stable_k}": (comp_stable_any / pairs) if pairs else 0.0,
                    "mean_worst_rank": (comp_worst_sum / pairs) if pairs else float(top_k_files + 1),
                },
                "ranks_by_collection": ranks_by_collection,
            }

        results["paper_idf_pack_auto"] = {
            "toolset": FUSE_TOOLSET,
            "top_k_files": top_k_files,
            "stable_k": stable_k,
            "attempted_queries": attempted,
            "avg_retrieval_ms": float(f"{(total_ms / max(attempted, 1)):.3f}"),
            "global_metrics": _metrics_from_ranks(global_ranks),
            "stability": {
                "pairs": stable_pairs,
                f"all_variants_hit@{stable_k}": (stable_all / stable_pairs) if stable_pairs else 0.0,
                f"any_variant_hit@{stable_k}": (stable_any / stable_pairs) if stable_pairs else 0.0,
                "mean_worst_rank": (worst_sum / stable_pairs) if stable_pairs else float(top_k_files + 1),
            },
            "per_component": per_component,
        }

    # ------------------ BM25 baselines ------------------
    def _run_bm25_variants(*, normalize: bool) -> Dict[str, Any]:
        if BM25Okapi is None:
            return {"error": "rank_bm25 is not available; install rank-bm25."}

        per_component: Dict[str, Any] = {}
        total_ms = 0.0
        attempted = 0
        global_ranks: List[int] = []
        stable_pairs = 0
        stable_all = 0
        stable_any = 0
        worst_sum = 0.0

        # Pre-build BM25 per collection for efficiency.
        bm25_by_cid: Dict[str, Any] = {}
        exes_by_cid: Dict[str, List[str]] = {}

        for cid in ground_truth.keys():
            exes = filter_executables(api.expand_oids(cid))
            exe_oids: List[str] = []
            corpus: List[List[str]] = []
            for oid in exes:
                toks = _bm25_tokens_for_oid(oid, normalize=normalize)
                if toks:
                    exe_oids.append(oid)
                    corpus.append(toks)
            bm25 = BM25Okapi(corpus) if corpus else None
            bm25_by_cid[cid] = (bm25, exe_oids)
            exes_by_cid[cid] = exes

        for comp, prompts in cleaned_variants.items():
            per_prompt_ranks: Dict[str, List[int]] = {p: [] for p in prompts}
            ranks_by_collection: Dict[str, Dict[str, int]] = {}
            pairs = 0
            comp_stable_all = 0
            comp_stable_any = 0
            comp_worst_sum = 0.0

            for cid, golds in ground_truth.items():
                gold_oid = golds.get(comp)
                if not gold_oid:
                    continue
                colname = api.get_colname_from_oid(cid)
                ranks_this_pair: List[int] = []
                ranks_by_collection.setdefault(colname, {})

                bm25, exe_oids = bm25_by_cid.get(cid, (None, []))
                max_rank = top_k_files + 1

                for p in prompts:
                    if bm25 is None or not exe_oids:
                        rank = max_rank
                    else:
                        q_tokens = _bm25_tokens_for_text(p, normalize=normalize)
                        if not q_tokens:
                            rank = max_rank
                        else:
                            t0 = time.perf_counter_ns()
                            scores = bm25.get_scores(q_tokens)
                            idxs = sorted(range(len(scores)), key=lambda i: scores[i], reverse=True)
                            ranked_oids = [exe_oids[i] for i in idxs[:top_k_files]]
                            total_ms += (time.perf_counter_ns() - t0) / 1_000_000.0
                            try:
                                rank = ranked_oids.index(gold_oid) + 1
                            except ValueError:
                                rank = top_k_files + 1

                    per_prompt_ranks[p].append(rank)
                    ranks_by_collection[colname][p] = rank
                    ranks_this_pair.append(rank)
                    global_ranks.append(rank)
                    attempted += 1

                pairs += 1
                stable_pairs += 1
                if ranks_this_pair:
                    worst = _worst_rank(ranks_this_pair)
                    comp_worst_sum += float(worst)
                    worst_sum += float(worst)
                    all_ok = all(r <= stable_k for r in ranks_this_pair)
                    any_ok = any(r <= stable_k for r in ranks_this_pair)
                    comp_stable_all += int(all_ok)
                    comp_stable_any += int(any_ok)
                    stable_all += int(all_ok)
                    stable_any += int(any_ok)

            per_prompt_metrics = {p: _metrics_from_ranks(r) for p, r in per_prompt_ranks.items()}
            per_component[comp] = {
                "num_variants": len(prompts),
                "prompt_metrics": per_prompt_metrics,
                "stability": {
                    "pairs": pairs,
                    f"all_variants_hit@{stable_k}": (comp_stable_all / pairs) if pairs else 0.0,
                    f"any_variant_hit@{stable_k}": (comp_stable_any / pairs) if pairs else 0.0,
                    "mean_worst_rank": (comp_worst_sum / pairs) if pairs else float(top_k_files + 1),
                },
                "ranks_by_collection": ranks_by_collection,
            }

        return {
            "toolset": "bm25_norm" if normalize else "bm25_raw",
            "top_k_files": top_k_files,
            "stable_k": stable_k,
            "attempted_queries": attempted,
            "avg_retrieval_ms": float(f"{(total_ms / max(attempted, 1)):.3f}"),
            "global_metrics": _metrics_from_ranks(global_ranks),
            "stability": {
                "pairs": stable_pairs,
                f"all_variants_hit@{stable_k}": (stable_all / stable_pairs) if stable_pairs else 0.0,
                f"any_variant_hit@{stable_k}": (stable_any / stable_pairs) if stable_pairs else 0.0,
                "mean_worst_rank": (worst_sum / stable_pairs) if stable_pairs else float(top_k_files + 1),
            },
            "per_component": per_component,
        }

    if "bm25_raw" in methods:
        results["bm25_raw"] = _run_bm25_variants(normalize=False)
    if "bm25_norm" in methods:
        results["bm25_norm"] = _run_bm25_variants(normalize=True)

    # ------------------ function_embeddings baseline (optional) ------------------
    if "function_embeddings" in methods:
        per_component: Dict[str, Any] = {}
        total_ms = 0.0
        attempted = 0
        global_ranks: List[int] = []
        stable_pairs = 0
        stable_all = 0
        stable_any = 0
        worst_sum = 0.0

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
            func_similarity_threshold = float(opts.get("func_similarity_threshold", 0.0) or 0.0)
        except Exception:
            func_similarity_threshold = 0.0
        if func_similarity_threshold < 0:
            func_similarity_threshold = 0.0

        exes_by_cid: Dict[str, List[str]] = {
            cid: filter_executables(api.expand_oids(cid)) for cid in ground_truth.keys()
        }

        for comp, prompts in cleaned_variants.items():
            per_prompt_ranks: Dict[str, List[int]] = {p: [] for p in prompts}
            ranks_by_collection: Dict[str, Dict[str, int]] = {}
            pairs = 0
            comp_stable_all = 0
            comp_stable_any = 0
            comp_worst_sum = 0.0

            for cid, golds in ground_truth.items():
                gold_oid = golds.get(comp)
                if not gold_oid:
                    continue
                colname = api.get_colname_from_oid(cid)
                ranks_this_pair: List[int] = []
                ranks_by_collection.setdefault(colname, {})

                exes = exes_by_cid.get(cid) or []
                if not exes:
                    # No functions to search against.
                    for p in prompts:
                        rank = top_k_files + 1
                        per_prompt_ranks[p].append(rank)
                        ranks_by_collection[colname][p] = rank
                        ranks_this_pair.append(rank)
                        global_ranks.append(rank)
                        attempted += 1
                    pairs += 1
                    stable_pairs += 1
                    continue

                for p in prompts:
                    t0 = time.perf_counter_ns()
                    qf_out = api.retrieve(
                        "query_function",
                        exes,
                        {
                            "query": p,
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
                    total_ms += (time.perf_counter_ns() - t0) / 1_000_000.0

                    oid_list = [r.get("oid") for r in ranked_files if isinstance(r, dict)]
                    try:
                        rank = oid_list.index(gold_oid) + 1
                    except ValueError:
                        rank = top_k_files + 1

                    per_prompt_ranks[p].append(rank)
                    ranks_by_collection[colname][p] = rank
                    ranks_this_pair.append(rank)
                    global_ranks.append(rank)
                    attempted += 1

                pairs += 1
                stable_pairs += 1
                if ranks_this_pair:
                    worst = _worst_rank(ranks_this_pair)
                    comp_worst_sum += float(worst)
                    worst_sum += float(worst)
                    all_ok = all(r <= stable_k for r in ranks_this_pair)
                    any_ok = any(r <= stable_k for r in ranks_this_pair)
                    comp_stable_all += int(all_ok)
                    comp_stable_any += int(any_ok)
                    stable_all += int(all_ok)
                    stable_any += int(any_ok)

            per_prompt_metrics = {p: _metrics_from_ranks(r) for p, r in per_prompt_ranks.items()}
            per_component[comp] = {
                "num_variants": len(prompts),
                "prompt_metrics": per_prompt_metrics,
                "stability": {
                    "pairs": pairs,
                    f"all_variants_hit@{stable_k}": (comp_stable_all / pairs) if pairs else 0.0,
                    f"any_variant_hit@{stable_k}": (comp_stable_any / pairs) if pairs else 0.0,
                    "mean_worst_rank": (comp_worst_sum / pairs) if pairs else float(top_k_files + 1),
                },
                "ranks_by_collection": ranks_by_collection,
            }

        results["function_embeddings"] = {
            "toolset": "function_embeddings",
            "top_k_files": top_k_files,
            "top_k_funcs": top_k_funcs,
            "stable_k": stable_k,
            "func_file_agg": func_file_agg,
            "func_attn_tau": func_attn_tau,
            "func_similarity_threshold": func_similarity_threshold,
            "attempted_queries": attempted,
            "avg_retrieval_ms": float(f"{(total_ms / max(attempted, 1)):.3f}"),
            "global_metrics": _metrics_from_ranks(global_ranks),
            "stability": {
                "pairs": stable_pairs,
                f"all_variants_hit@{stable_k}": (stable_all / stable_pairs) if stable_pairs else 0.0,
                f"any_variant_hit@{stable_k}": (stable_any / stable_pairs) if stable_pairs else 0.0,
                "mean_worst_rank": (worst_sum / stable_pairs) if stable_pairs else float(top_k_files + 1),
            },
            "per_component": per_component,
        }

    payload = {
        "toolset": FUSE_TOOLSET,
        "use_tags": False,
        "top_k_files": top_k_files,
        "stable_k": stable_k,
        "prompt_variants_path": prompt_variants_path,
        "components": sorted(cleaned_variants.keys()),
        "methods": methods,
        "results": results,
    }
    _write_json_if_requested(opts, "paper_query_variation.json", payload)
    return payload


def agent_paper_eval_all(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Run the complete paper evaluation suite in one command:
      1) main baseline comparison
      2) ablation comparison
      3) budget sensitivity sweep
      4) one-time vs warm retrieval time breakdown

    opts:
      - comp_path, prompt_path (required)
      - methods (optional): compare/timing method selector (same semantics as agent_paper_compare)
      - top_k_files, top_k_funcs
      - function baseline options:
          func_file_agg in {top1, mean, attn}
          func_attn_tau
          func_similarity_threshold
      - budgets (for budget sweep)
      - paper mode options:
          string_emb_batch_size, debug_select,
          ablate_noise_filter, ablate_redundancy, ablate_idf, pack_budget_tokens
      - prompt_variants_path (optional): if set, also run query-variation robustness
      - outdir (optional): directory for JSON artifacts
    """
    comp_path = opts.get("comp_path")
    prompt_path = opts.get("prompt_path")
    if not comp_path or not prompt_path:
        return {"error": "Provide comp_path and prompt_path."}

    started_ns = time.time_ns()

    run_opts = dict(opts)
    run_opts.pop("outdir", None)

    compare = agent_paper_compare(args, run_opts)
    ablations = agent_paper_ablation_compare(args, run_opts)
    budget = agent_paper_budget_sweep(args, run_opts)
    time_breakdown = agent_paper_time_breakdown(args, run_opts)
    query_variation = None
    if (opts.get("prompt_variants_path") or opts.get("variants_path")):
        query_variation = agent_paper_query_variation(args, run_opts)

    payload = {
        "toolset": FUSE_TOOLSET,
        "use_tags": False,
        "methods": opts.get("methods", ",".join(DEFAULT_COMPARE_METHODS)),
        "started_unix_ns": started_ns,
        "elapsed_ms": float(f"{(time.time_ns() - started_ns) / 1_000_000.0:.3f}"),
        "results": {
            "compare": compare,
            "ablations": ablations,
            "budget_sweep": budget,
            "time_breakdown": time_breakdown,
            "query_variation": query_variation,
        },
    }

    outdir = (opts.get("outdir") or "").strip()
    artifacts: Dict[str, str] = {}
    if outdir:
        try:
            outpath = Path(outdir).expanduser()
            outpath.mkdir(parents=True, exist_ok=True)
            artifacts["compare"] = _write_json(outpath, "paper_compare.json", compare)
            artifacts["ablations"] = _write_json(
                outpath, "paper_ablations.json", ablations
            )
            artifacts["budget_sweep"] = _write_json(
                outpath, "paper_budget_sweep.json", budget
            )
            artifacts["time_breakdown"] = _write_json(
                outpath, "paper_time_breakdown.json", time_breakdown
            )
            if query_variation is not None:
                artifacts["query_variation"] = _write_json(
                    outpath, "paper_query_variation.json", query_variation
                )
            artifacts["all"] = _write_json(outpath, "paper_eval_all.json", payload)
        except Exception as e:
            payload["artifact_error"] = f"Failed writing outdir artifacts: {e}"
    if artifacts:
        payload["artifacts"] = artifacts

    return payload


def agent_paper_time_breakdown(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Break down timing into:
      - one-time processing cost (index/build/precompute)
      - warm retrieval cost (query-time ranking after precompute)

    Methods:
      - paper_idf_pack_auto (fuse)
      - bm25_raw
      - bm25_norm
      - function_embeddings

    opts:
      - comp_path, prompt_path (required)
      - methods (optional): method selector; default stays backward-compatible
      - top_k_files (default 50)
      - top_k_funcs (default 1)
      - text_mode in {raw,norm} (default: norm) for new text baselines
      - local_files_only (default true): do not download missing HF model assets
      - function baseline options:
          func_file_agg in {top1, mean, attn}
          func_attn_tau
          func_similarity_threshold
      - paper mode options:
          string_emb_batch_size, debug_select,
          ablate_noise_filter, ablate_redundancy, ablate_idf, pack_budget_tokens
      - reset_caches (default true): clear local caches before measuring
      - outdir (optional): write JSON artifact
    """
    methods, method_err = _parse_methods_opt(
        opts,
        default_methods=DEFAULT_COMPARE_METHODS,
        allowed_methods=ALL_COMPARE_METHODS,
    )
    if method_err:
        return {"error": method_err}
    text_mode, text_mode_err = _parse_text_mode(opts)
    if text_mode_err:
        return {"error": text_mode_err}

    ground_truth, prompt_map, load_err = _load_eval_inputs(opts)
    if load_err:
        return {"error": load_err}
    if ground_truth is None or prompt_map is None:
        return {"error": "Failed loading evaluation inputs."}

    reset_caches = _as_bool(opts.get("reset_caches", True), True)
    top_k_files = int(
        opts.get("top_k_files", DEFAULT_TOP_K_FILES) or DEFAULT_TOP_K_FILES
    )

    if reset_caches:
        # Best effort cache reset to ensure cold-start one-time measurements.
        for plugin_name in (
            FUSE_TOOLSET,
            "query_function",
            f"{NAME}_splade_style",
            f"{NAME}_dense_chunked",
            f"{NAME}_colbert_style",
        ):
            try:
                api.local_delete_function_data(plugin_name)
            except Exception:
                pass

    results: Dict[str, Any] = {}
    for method in methods or []:
        if method == "paper_idf_pack_auto":
            results[method] = _time_breakdown_fuse(ground_truth, prompt_map, opts)
        elif method == "bm25_raw":
            results[method] = _time_breakdown_bm25(
                ground_truth, prompt_map, opts, normalize=False
            )
        elif method == "bm25_norm":
            results[method] = _time_breakdown_bm25(
                ground_truth, prompt_map, opts, normalize=True
            )
        elif method == "function_embeddings":
            results[method] = _time_breakdown_function_embeddings(
                ground_truth, prompt_map, opts
            )
        elif method == "bm25_rm3":
            results[method] = _time_breakdown_from_batch_output(
                "bm25_rm3", _batch_bm25_rm3(args, opts), top_k_files=top_k_files
            )
        elif method == "bm25f":
            results[method] = _time_breakdown_from_batch_output(
                "bm25f", _batch_bm25f(args, opts), top_k_files=top_k_files
            )
        elif method == "chargram_bm25":
            results[method] = _time_breakdown_from_batch_output(
                "chargram_bm25", _batch_chargram_bm25(args, opts), top_k_files=top_k_files
            )
        elif method == "splade_style":
            results[method] = _time_breakdown_from_batch_output(
                "splade_style", _batch_splade_style(args, opts), top_k_files=top_k_files
            )
        elif method == "dense_chunked":
            results[method] = _time_breakdown_from_batch_output(
                "dense_chunked", _batch_dense_chunked(args, opts), top_k_files=top_k_files
            )
        elif method == "colbert_style":
            results[method] = _time_breakdown_from_batch_output(
                "colbert_style", _batch_colbert_style(args, opts), top_k_files=top_k_files
            )
        elif method == "bm25_rerank_ce":
            results[method] = _time_breakdown_from_batch_output(
                "bm25_rerank_ce", _batch_bm25_rerank_ce(args, opts), top_k_files=top_k_files
            )
        elif method == "dense_rerank_ce":
            results[method] = _time_breakdown_from_batch_output(
                "dense_rerank_ce", _batch_dense_rerank_ce(args, opts), top_k_files=top_k_files
            )
        elif method == "bm25_dense_rrf":
            results[method] = _time_breakdown_from_batch_output(
                "bm25_dense_rrf", _batch_bm25_dense_rrf(args, opts), top_k_files=top_k_files
            )
        elif method == "bm25_splade_rrf":
            results[method] = _time_breakdown_from_batch_output(
                "bm25_splade_rrf", _batch_bm25_splade_rrf(args, opts), top_k_files=top_k_files
            )
        else:
            results[method] = {"error": f"Unknown method '{method}'."}

    payload = {
        "toolset": FUSE_TOOLSET,
        "use_tags": False,
        "top_k_files": top_k_files,
        "text_mode": text_mode,
        "methods": methods,
        "reset_caches": reset_caches,
        "results": results,
    }
    _write_json_if_requested(opts, "paper_time_breakdown.json", payload)
    return payload


exports = [
    agent_search,
    agent_batch,
    agent_paper_compare,
    agent_paper_ablation_compare,
    agent_paper_budget_sweep,
    agent_paper_query_variation,
    agent_paper_time_breakdown,
    agent_paper_eval_all,
]


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


def _write_json_if_requested(opts: Dict[str, Any], filename: str, payload: Dict[str, Any]) -> None:
    outdir = (opts.get("outdir") or "").strip()
    if not outdir:
        return
    try:
        outpath = Path(outdir).expanduser()
        outpath.mkdir(parents=True, exist_ok=True)
        _write_json(outpath, filename, payload)
    except Exception:
        # Keep plugin responses stable even if artifact write fails.
        return


def _validate_toolset(opts: Dict[str, Any]) -> Optional[str]:
    toolset = (opts.get("toolset") or FUSE_TOOLSET).strip().lower()
    if toolset != FUSE_TOOLSET:
        return f"This plugin is fixed to fuse. Use toolset='{FUSE_TOOLSET}' (got '{toolset}')."
    return None


def _batch_bm25(
    args: List[str], opts: Dict[str, Any], *, normalize: bool
) -> Dict[str, Any]:
    if BM25Okapi is None:
        return {"error": "rank_bm25 is not available; install rank-bm25."}

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
        exes = filter_executables(api.expand_oids(cid))

        exe_oids: List[str] = []
        corpus: List[List[str]] = []
        for oid in exes:
            toks = _bm25_tokens_for_oid(oid, normalize=normalize)
            if toks:
                exe_oids.append(oid)
                corpus.append(toks)

        bm25 = BM25Okapi(corpus) if corpus else None

        ranks_by_component: Dict[str, Optional[int]] = {}
        attempted_here = 0

        for comp, gold_oid in golds.items():
            prompt = prompt_map.get(comp)
            if not prompt:
                ranks_by_component[comp] = None
                continue
            if bm25 is None:
                ranks_by_component[comp] = None
                continue

            q_tokens = _bm25_tokens_for_text(prompt, normalize=normalize)
            if not q_tokens:
                ranks_by_component[comp] = None
                continue

            t0 = time.perf_counter_ns()
            scores = bm25.get_scores(q_tokens)
            idxs = sorted(range(len(scores)), key=lambda i: scores[i], reverse=True)
            ranked_oids = [exe_oids[i] for i in idxs[:top_k_files]]
            elapsed_ms = (time.perf_counter_ns() - t0) / 1_000_000.0

            attempted += 1
            attempted_here += 1
            total_ms += elapsed_ms
            total_tool_calls += 1.0

            try:
                rank = ranked_oids.index(gold_oid) + 1
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
        return {"error": "No prompts evaluated (BM25 corpus/query tokens may be empty)."}

    avg_ms = total_ms / max(attempted, 1)
    avg_calls = total_tool_calls / max(attempted, 1)
    return {
        "toolset": "bm25_norm" if normalize else "bm25_raw",
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


def _build_bm25_index_for_text_mode(
    cid: str, *, text_mode: str
) -> Dict[str, Any]:
    exes = filter_executables(api.expand_oids(cid))
    exe_oids: List[str] = []
    corpus: List[List[str]] = []
    for oid in exes:
        toks = _tokens_for_oid_text_mode(oid, text_mode)
        if toks:
            exe_oids.append(oid)
            corpus.append(toks)
    bm25 = BM25Okapi(corpus) if (BM25Okapi and corpus) else None
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

    idxs = sorted(range(len(scores)), key=lambda i: scores[i], reverse=True)[: max(1, fb_docs)]
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
        return {"evaluated": True, "oid_list": ranked, "elapsed_ms": elapsed_ms, "tool_calls": 1.0}

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
    b_name = _as_float_opt(opts, "bm25f_b_name", DEFAULT_BM25F_B_NAME, min_value=0.0, max_value=1.0)
    b_str = _as_float_opt(opts, "bm25f_b_string", DEFAULT_BM25F_B_STRING, min_value=0.0, max_value=1.0)

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
        return {"evaluated": True, "oid_list": ranked, "elapsed_ms": elapsed_ms, "tool_calls": 1.0}

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
        bm25 = BM25Okapi(corpus) if corpus else None
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
        return {"evaluated": True, "oid_list": ranked, "elapsed_ms": elapsed_ms, "tool_calls": 1.0}

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


def _rrf_fuse(rank_lists: Sequence[Sequence[str]], *, rrf_k: int, depth: int) -> List[str]:
    scores: Dict[str, float] = defaultdict(float)
    for rank_list in rank_lists:
        for idx, oid in enumerate(list(rank_list)[: max(1, depth)], start=1):
            scores[oid] += 1.0 / float(max(1, rrf_k) + idx)
    return [oid for oid, _ in sorted(scores.items(), key=lambda x: (-x[1], x[0]))]


def _chunk_token_windows(tokens: Sequence[str], chunk_size: int, overlap: int) -> List[List[str]]:
    if chunk_size <= 0:
        chunk_size = DEFAULT_DENSE_CHUNK_TOKENS
    overlap = max(0, min(overlap, chunk_size - 1))
    step = max(1, chunk_size - overlap)
    out: List[List[str]] = []
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
    model_id = str(opts.get("dense_model_id", DEFAULT_DENSE_MODEL_ID) or DEFAULT_DENSE_MODEL_ID).strip()
    local_files_only = _as_bool(opts.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY), DEFAULT_LOCAL_FILES_ONLY)
    chunk_tokens = _as_int_opt(opts, "dense_chunk_tokens", DEFAULT_DENSE_CHUNK_TOKENS, min_value=8)
    chunk_overlap = _as_int_opt(opts, "dense_chunk_overlap", DEFAULT_DENSE_CHUNK_OVERLAP, min_value=0)
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
        key = _cache_key_for_collection(method="dense_chunked", cid=cid, oids=exes, config=cfg)
        cached = api.local_retrieve(cache_plugin, key) if api.local_exists(cache_plugin, key) else None
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
                    oid_chunks[oid] = _ensure_np_array(np.zeros((0, embs.shape[1]), dtype=np.float32))
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
    return {"evaluated": True, "oid_list": ranked, "elapsed_ms": elapsed_ms, "tool_calls": 1.0}


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
    model_id = str(opts.get("splade_model_id", DEFAULT_SPLADE_MODEL_ID) or DEFAULT_SPLADE_MODEL_ID).strip()
    max_length = _as_int_opt(opts, "splade_max_length", DEFAULT_SPLADE_MAX_LENGTH, min_value=8)
    doc_top_terms = _as_int_opt(opts, "splade_doc_top_terms", DEFAULT_SPLADE_DOC_TOP_TERMS, min_value=8)
    query_top_terms = _as_int_opt(opts, "splade_query_top_terms", DEFAULT_SPLADE_QUERY_TOP_TERMS, min_value=4)
    local_files_only = _as_bool(opts.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY), DEFAULT_LOCAL_FILES_ONLY)
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
        key = _cache_key_for_collection(method="splade_style", cid=cid, oids=exes, config=cfg)
        cached = api.local_retrieve(cache_plugin, key) if api.local_exists(cache_plugin, key) else None
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
    return {"evaluated": True, "oid_list": ranked, "elapsed_ms": elapsed_ms, "tool_calls": 1.0}


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
            dim = int(tok.shape[1]) if len(tok.shape) > 1 else int(getattr(model.config, "hidden_size", 384))
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
    model_id = str(opts.get("colbert_model_id", DEFAULT_COLBERT_MODEL_ID) or DEFAULT_COLBERT_MODEL_ID).strip()
    max_length = _as_int_opt(opts, "colbert_max_length", DEFAULT_COLBERT_MAX_LENGTH, min_value=8)
    doc_token_cap = _as_int_opt(opts, "colbert_doc_token_cap", DEFAULT_COLBERT_DOC_TOKEN_CAP, min_value=16)
    local_files_only = _as_bool(opts.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY), DEFAULT_LOCAL_FILES_ONLY)
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
        key = _cache_key_for_collection(method="colbert_style", cid=cid, oids=exes, config=cfg)
        cached = api.local_retrieve(cache_plugin, key) if api.local_exists(cache_plugin, key) else None
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
    return {"evaluated": True, "oid_list": ranked, "elapsed_ms": elapsed_ms, "tool_calls": 1.0}


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
    by_cid, meta, build_err = _build_dense_engine(list(ground_truth.keys()), opts, text_mode=text_mode)
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
    by_cid, meta, build_err = _build_splade_engine(list(ground_truth.keys()), opts, text_mode=text_mode)
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
        extra_payload={k: v for k, v in meta.items() if k not in {"tokenizer", "model"}},
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
    by_cid, meta, build_err = _build_colbert_engine(list(ground_truth.keys()), opts, text_mode=text_mode)
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
        extra_payload={k: v for k, v in meta.items() if k not in {"tokenizer", "model"}},
    )


def _rerank_with_cross_encoder(
    *,
    cross_encoder: Any,
    prompt: str,
    candidate_oids: Sequence[str],
    oid_texts: Dict[str, str],
) -> List[str]:
    if not candidate_oids:
        return []
    pairs = [(prompt, oid_texts.get(oid, "")) for oid in candidate_oids]
    scores = cross_encoder.predict(pairs, batch_size=32, show_progress_bar=False)
    scored = list(zip(candidate_oids, [float(s) for s in scores]))
    scored.sort(key=lambda x: x[1], reverse=True)
    return [oid for oid, _ in scored]


def _build_rerank_stage1_bm25(
    cids: Sequence[str], *, text_mode: str
) -> Dict[str, Any]:
    return {cid: _build_bm25_index_for_text_mode(cid, text_mode=text_mode) for cid in cids}


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
    rerank_model_id = str(opts.get("rerank_model_id", DEFAULT_RERANK_MODEL_ID) or DEFAULT_RERANK_MODEL_ID).strip()
    local_files_only = _as_bool(opts.get("local_files_only", DEFAULT_LOCAL_FILES_ONLY), DEFAULT_LOCAL_FILES_ONLY)
    candidate_ks = _parse_int_csv(str(opts.get("rerank_candidate_ks", DEFAULT_RERANK_CANDIDATE_KS)))
    if not candidate_ks:
        candidate_ks = _parse_int_csv(DEFAULT_RERANK_CANDIDATE_KS)
    rerank_eval_k = _as_int_opt(opts, "rerank_eval_k", DEFAULT_RERANK_EVAL_K, min_value=1)
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
        stage1_by_cid = _build_rerank_stage1_bm25(list(ground_truth.keys()), text_mode=text_mode)
        for cid in ground_truth.keys():
            exes = (stage1_by_cid.get(cid) or {}).get("exe_oids") or []
            oid_texts_by_cid[cid] = {oid: _document_text_for_oid(oid, text_mode) for oid in exes}
    else:
        dense_by_cid, dense_meta, dense_err = _build_dense_engine(list(ground_truth.keys()), opts, text_mode=text_mode)
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
                sum((r if r is not None else (top_k_files + 1)) for r in ranks_by_component.values())
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
            per_collection[colname] = {"metrics": {}, "ranks_by_prompt": ranks_by_component}

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
    bm25_by_cid = {cid: _build_bm25_index_for_text_mode(cid, text_mode=text_mode) for cid in ground_truth.keys()}
    dense_by_cid, dense_meta, dense_err = _build_dense_engine(list(ground_truth.keys()), opts, text_mode=text_mode)
    if dense_err:
        return {"error": dense_err}
    if dense_by_cid is None or dense_meta is None:
        return {"error": "Failed building dense engine."}
    model = dense_meta["model"]

    def ranker(cid: str, prompt: str, top_k: int) -> Dict[str, Any]:
        bm25_state = bm25_by_cid.get(cid) or {}
        dense_state = dense_by_cid.get(cid) or {}
        out_b = _stage1_bm25_rank(state=bm25_state, prompt=prompt, top_k=rrf_depth, text_mode=text_mode)
        out_d = _dense_rank(state=dense_state, prompt=prompt, top_k_files=rrf_depth, model=model, text_mode=text_mode)
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
        return {"evaluated": True, "oid_list": fused[:top_k], "elapsed_ms": elapsed_ms, "tool_calls": 1.0}

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
    bm25_by_cid = {cid: _build_bm25_index_for_text_mode(cid, text_mode=text_mode) for cid in ground_truth.keys()}
    splade_by_cid, splade_meta, splade_err = _build_splade_engine(list(ground_truth.keys()), opts, text_mode=text_mode)
    if splade_err:
        return {"error": splade_err}
    if splade_by_cid is None or splade_meta is None:
        return {"error": "Failed building splade engine."}

    def ranker(cid: str, prompt: str, top_k: int) -> Dict[str, Any]:
        bm25_state = bm25_by_cid.get(cid) or {}
        spl_state = splade_by_cid.get(cid) or {}
        out_b = _stage1_bm25_rank(state=bm25_state, prompt=prompt, top_k=rrf_depth, text_mode=text_mode)
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
        return {"evaluated": True, "oid_list": fused[:top_k], "elapsed_ms": elapsed_ms, "tool_calls": 1.0}

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
        ranks = ((col or {}).get("ranks_by_prompt") or {})
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
        bm25 = BM25Okapi(corpus) if corpus else None
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
        prompts = [prompt_map.get(comp) for comp in golds.keys() if prompt_map.get(comp)]

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
        prompts = [prompt_map.get(comp) for comp in golds.keys() if prompt_map.get(comp)]

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
