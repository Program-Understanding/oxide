DESC = "Strings-only file retrieval using BM25 lexical overlap with optional per-binary string ranking"
NAME = "bm25"

import json
import logging
import re
from typing import Any, Dict, List, Optional, Sequence, Tuple

from oxide.core import api

try:
    from rank_bm25 import BM25Okapi
except Exception:
    BM25Okapi = None

logger = logging.getLogger(NAME)

opts_doc = {
    "prompt": {"type": str, "mangle": False, "default": ""},
    "prompt_path": {"type": str, "mangle": False, "default": ""},
    "top_k": {"type": int, "mangle": False, "default": 0},
    "oids": {"type": list, "mangle": False, "default": []},
    "include_string_rankings": {"type": bool, "mangle": False, "default": True},
    "strings_for_top_n_oids": {"type": int, "mangle": False, "default": 0},
    "top_k_strings_per_oid": {"type": int, "mangle": False, "default": 0},
}

RAW_TERM = re.compile(r"[A-Za-z]{3,}")


def documentation() -> Dict[str, Any]:
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": True,
        "set": False,
        "atomic": True,
    }


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
    include_string_rankings = bool(opts.get("include_string_rankings", True))
    strings_for_top_n_oids = int(opts.get("strings_for_top_n_oids", 0) or 0)
    try:
        top_k_strings_per_oid = int(opts.get("top_k_strings_per_oid", 0))
    except Exception:
        top_k_strings_per_oid = 0
    requested_oids = _normalize_oids_opt(opts.get("oids", []))

    return search_prompt(
        oids=oid_list,
        prompt=prompt,
        top_k=top_k,
        requested_oids=requested_oids,
        include_string_rankings=include_string_rankings,
        strings_for_top_n_oids=strings_for_top_n_oids,
        top_k_strings_per_oid=top_k_strings_per_oid,
    )


def search_prompt(
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
                cand["string_matches"] = _rank_strings_for_oid(
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

    out: List[Dict[str, Any]] = []
    for oid, score in rows:
        out.append({"oid": oid, "names": get_names(oid), "score": float(score)})
    return out


def _rank_strings_for_oid(oid: str, prompt: str, *, top_k: int = 0) -> List[Dict[str, Any]]:
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
    if k > 0:
        return rows[:k]
    return rows


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
