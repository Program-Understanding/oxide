import json
import time
import logging
import re
from pathlib import Path
from typing import Any, Dict, List, Optional

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
    "ablate_capability_reserve",
    "ablate_span_canonicalization",
    "ablate_idf",
    "pack_budget_tokens",
)

try:
    from rank_bm25 import BM25Okapi
except Exception:
    BM25Okapi = None

RAW_TERM = re.compile(r"[A-Za-z]{3,}")
PACK_TERM = re.compile(r"[a-z][a-z0-9]{2,}", re.IGNORECASE)
UUID_PAT = re.compile(
    r"\b[0-9a-f]{8}-[0-9a-f]{4}-[1-5][0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}\b",
    re.IGNORECASE,
)
HEX_PAT = re.compile(r"\b(?:0x)?[0-9a-f]{8,}\b", re.IGNORECASE)
NUM_PAT = re.compile(r"\b\d{4,}\b")


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
    Compare paper implementation against three non-paper baselines:
      1) bm25_raw
      2) bm25_norm
      3) function_embeddings

    opts:
      - comp_path, prompt_path (required)
      - top_k_files (default 50)
      - top_k_funcs (default 1) for function baseline
      - function baseline options:
          func_file_agg in {top1, mean, attn} (default: top1)
          func_attn_tau (default: 0.07)
          func_similarity_threshold (default: 0.0)
      - paper mode options:
          string_emb_batch_size, debug_select,
          ablate_noise_filter, ablate_redundancy, ablate_capability_reserve,
          ablate_span_canonicalization, ablate_idf, pack_budget_tokens
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

    paper_opts = dict(opts)
    paper_opts["toolset"] = FUSE_TOOLSET

    results = {
        "paper_idf_pack_auto": agent_batch(args, paper_opts),
        "bm25_raw": _batch_bm25(args, opts, normalize=False),
        "bm25_norm": _batch_bm25(args, opts, normalize=True),
        "function_embeddings": _batch_function_embeddings(args, opts),
    }

    payload = {
        "toolset": FUSE_TOOLSET,
        "use_tags": False,
        "top_k_files": top_k_files,
        "top_k_funcs": top_k_funcs,
        "results": results,
    }
    _write_json_if_requested(opts, "paper_compare.json", payload)
    return payload


def agent_paper_ablation_compare(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Run paper-focused ablations on the fuse implementation only.

    Variants:
      - full_auto: default idf_pack_auto behavior
      - no_span_canonicalization: disable uuidtok/hextok/numtok canonicalization
      - no_idf: replace IDF weighting with uniform term weights
      - no_noise_filter: disable junk/noise filtering
      - no_redundancy: disable near-duplicate suppression
      - no_capability_reserve: disable reserved capability budget

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
    base_opts["ablate_capability_reserve"] = False
    base_opts["ablate_span_canonicalization"] = False
    base_opts["ablate_idf"] = False

    variants: Dict[str, Dict[str, Any]] = {
        "full_auto": {},
        "no_span_canonicalization": {"ablate_span_canonicalization": True},
        "no_idf": {"ablate_idf": True},
        "no_noise_filter": {"ablate_noise_filter": True},
        "no_redundancy": {"ablate_redundancy": True},
        "no_capability_reserve": {"ablate_capability_reserve": True},
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
                "ablate_capability_reserve": bool(
                    run_opts.get("ablate_capability_reserve", False)
                ),
                "ablate_span_canonicalization": bool(
                    run_opts.get("ablate_span_canonicalization", False)
                ),
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
    base_opts["ablate_capability_reserve"] = False

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
      - top_k_files, top_k_funcs
      - function baseline options:
          func_file_agg in {top1, mean, attn}
          func_attn_tau
          func_similarity_threshold
      - budgets (for budget sweep)
      - paper mode options:
          string_emb_batch_size, debug_select,
          ablate_noise_filter, ablate_redundancy, ablate_capability_reserve,
          ablate_span_canonicalization, ablate_idf, pack_budget_tokens
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
      - top_k_files (default 50)
      - top_k_funcs (default 1)
      - function baseline options:
          func_file_agg in {top1, mean, attn}
          func_attn_tau
          func_similarity_threshold
      - paper mode options:
          string_emb_batch_size, debug_select,
          ablate_noise_filter, ablate_redundancy, ablate_capability_reserve,
          ablate_span_canonicalization, ablate_idf, pack_budget_tokens
      - reset_caches (default true): clear local caches before measuring
      - outdir (optional): write JSON artifact
    """
    comp_path = opts.get("comp_path")
    prompt_path = opts.get("prompt_path")
    if not comp_path or not prompt_path:
        return {"error": "Provide comp_path and prompt_path."}

    ground_truth = create_ground_truth(comp_path)
    try:
        prompt_map = json.loads(Path(prompt_path).read_text())
    except Exception as e:
        return {"error": f"Failed to load prompt_path JSON: {e}"}

    reset_caches = bool(opts.get("reset_caches", True))
    top_k_files = int(
        opts.get("top_k_files", DEFAULT_TOP_K_FILES) or DEFAULT_TOP_K_FILES
    )

    if reset_caches:
        # Best effort cache reset to ensure cold-start one-time measurements.
        try:
            api.local_delete_function_data(FUSE_TOOLSET)
        except Exception:
            pass
        try:
            api.local_delete_function_data("query_function")
        except Exception:
            pass

    results = {
        "paper_idf_pack_auto": _time_breakdown_fuse(ground_truth, prompt_map, opts),
        "bm25_raw": _time_breakdown_bm25(
            ground_truth, prompt_map, opts, normalize=False
        ),
        "bm25_norm": _time_breakdown_bm25(
            ground_truth, prompt_map, opts, normalize=True
        ),
        "function_embeddings": _time_breakdown_function_embeddings(
            ground_truth, prompt_map, opts
        ),
    }

    payload = {
        "toolset": FUSE_TOOLSET,
        "use_tags": False,
        "top_k_files": top_k_files,
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
