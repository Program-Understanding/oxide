import json
from oxide.core import api
from rapidfuzz import fuzz
import re
from typing import List, Dict, Tuple, Any
import math
from collections import Counter
import numpy as np
from sentence_transformers import SentenceTransformer
from transformers import AutoTokenizer
import tlsh

# Configuration
MODEL_ID = "sentence-transformers/all-MiniLM-L6-v2"
tokenizer = AutoTokenizer.from_pretrained(MODEL_ID)
MAX_LEN = tokenizer.model_max_length
_model = SentenceTransformer(MODEL_ID)
ALNUM = re.compile(r"[A-Za-z]{3,}")

# ---------------------------------------------------------------------------
# Entry points
# ---------------------------------------------------------------------------
def fuse_nl(args, opts) -> Dict[str, Any]:
    """
    Search for a single prompt (loaded from a .txt file) and return top‑5 matches.
    """
    # 1) Load prompt text
    prompt_path = opts.get("prompt")
    if not prompt_path:
        return {"error": "Please provide a .txt file via the 'prompt' option."}
    try:
        with open(prompt_path, 'r') as fp:
            prompt = fp.read().strip()
    except OSError as e:
        return {"error": f"Could not read prompt file: {e}"}

    # 2) Collect executables
    valid, _ = api.valid_oids(args)
    exes, _  = _separate_oids(api.expand_oids(valid))

    # 3) Delegate to the core search helper
    return _search_by_prompt(exes, [prompt], opts, gold_map=None)


def fuse_nl_batch(args, opts) -> Dict[str, Any]:
    """
    Run batch search per collection and return both per-collection and aggregate metrics.
    """
    # 1) load your nested JSON: { collection_cid: { query, gold_map:{build_id:oid,…} }, … }    
    data_path = opts.get("data_path")
    if not data_path:
        return {"error": "use the data_path arg to pass in a path to your JSON file"}
    try:
        comp_map = json.load(open(data_path))
    except Exception as e:
        return {"error": f"Failed to load JSON: {e}"}

    per_collection = {}
    total_tests = 0
    sum_p1 = sum_h2 = sum_h5 = sum_mrr = 0.0

    # 2) iterate each top‑level component
    for sample, golds in comp_map.items():
        # run one search per build inside that component
        comp_results = {}
        if len(args) > 0:
            if sample in args:
                sample_oids, _ = api.valid_oids([sample])
                exes, _ = _separate_oids(api.expand_oids(sample_oids))
                prompts = list(golds.keys())
                out = _search_by_prompt(exes, prompts, opts, gold_map=golds)
            else:
                continue
        else:
            sample_oids, _ = api.valid_oids([sample])
            exes, _ = _separate_oids(api.expand_oids(sample_oids))
            prompts = list(golds.keys())
            out = _search_by_prompt(exes, prompts, opts, gold_map=golds)

        # stash full detail under the build’s name
        build_name = api.get_colname_from_oid(sample)
        comp_results[build_name] = out

        # accumulate for globals
        m = out.get("metrics", {})
        sum_p1  += m.get("P@1",  0)
        sum_h2  += m.get("Hit@2", 0)
        sum_h5  += m.get("Hit@5", 0)
        sum_mrr += m.get("MRR",   0)
        total_tests += 1

        if len(args) > 0:
            per_collection[build_name] = out
        else:
            # store all build‐level outputs under this component’s name
            per_collection[build_name] = m

    if total_tests == 0:
        return {"error": "No tests executed. Check your JSON structure."}

    # 3) compute global averages
    global_metrics = {
        "P@1":   sum_p1  / total_tests,
        "Hit@2": sum_h2  / total_tests,
        "Hit@5": sum_h5  / total_tests,
        "MRR":   sum_mrr / total_tests
    }

    return {
        "per_collection": per_collection,
        "global_metrics": global_metrics
    }    

def fuse_nl_batch_by_size(args, opts) -> Dict[str, Any]:
    """
    Run batch search across all samples, then report metrics broken down
    by function-count buckets (based on the gold OID).
    """
    data_path = opts.get("data_path")
    if not data_path:
        return {"error": "Please provide 'data_path' to your JSON file."}
    try:
        comp_map = json.load(open(data_path))
    except Exception as e:
        return {"error": f"Could not load JSON: {e}"}

    # define size buckets
    bucket_defs = {
        "small":  lambda n: n <=  50,
        "medium": lambda n: 50 < n <= 200,
        "large":  lambda n: n >  200,
    }
    # initialize accumulators
    stats = {b: {"P@1":0.0, "Hit@2":0.0, "Hit@5":0.0, "MRR":0.0, "count":0} for b in bucket_defs}

    # iterate each sample & prompt
    for sample, golds in comp_map.items():
        valid, _ = api.valid_oids([sample])
        exes, _ = _separate_oids(api.expand_oids(valid))
        for prompt, expected_oid in golds.items():
            out = _search_by_prompt(exes, [prompt], opts, gold_map={prompt: expected_oid})
            metrics = out.get("metrics", {})
            funcs = api.retrieve("tag_all_functions", expected_oid) or {}
            num_funcs = len(funcs)
            # assign to bucket
            for bname, fn in bucket_defs.items():
                if fn(num_funcs):
                    stats[bname]["P@1"]  += metrics.get("P@1",  0.0)
                    stats[bname]["Hit@2"] += metrics.get("Hit@2", 0.0)
                    stats[bname]["Hit@5"] += metrics.get("Hit@5", 0.0)
                    stats[bname]["MRR"]   += metrics.get("MRR",   0.0)
                    stats[bname]["count"] += 1
                    break

    # finalize averages
    bucketed_metrics = {}
    for b, acc in stats.items():
        cnt = acc["count"]
        if cnt:
            bucketed_metrics[b] = {
                "P@1":   acc["P@1"]/cnt,
                "Hit@2": acc["Hit@2"]/cnt,
                "Hit@5": acc["Hit@5"]/cnt,
                "MRR":   acc["MRR"]/cnt,
                "count": cnt,
            }
        else:
            bucketed_metrics[b] = {"P@1":0.0, "Hit@2":0.0, "Hit@5":0.0, "MRR":0.0, "count":0}

    return {"bucketed_metrics": bucketed_metrics}

def fuse_ex(args, opts):
    """
    Given a component OID and a firmware image collection, return the most semantically similar firmware executables
    by comparing influential function tags (using tag_context) and strings via embedding fusion.

    Usage:
        search_component <component_oid> <firmware_image_collection>
    """
    valid, _ = api.valid_oids(args)
    if len(valid) < 2:
        raise ValueError("Usage: search_component <component_oid> <firmware_image_collection>")
    
    component_oid = valid[0]
    firmware_collection = valid[1]

    # Expand and filter firmware OIDs
    fw_exes, _ = _separate_oids(api.expand_oids(firmware_collection))
    if not fw_exes:
        return {"error": f"No valid firmware executables found in {firmware_collection}"}

    # Run semantic embedding-based search
    return _search_by_example(component_oid, fw_exes, opts)

def fuse_ex_batch_test(args, opts) -> Dict:
    """
    Run search_component over either:
      • a single (known, unknown) pair (if two collection IDs are passed in `args`), or
      • all ordered pairs of collections (if fewer than two IDs are passed).

    Returns:
      - If a single pair was provided: { "metrics": {...}, "categories": {...} }
      - Otherwise: {
            "results": {
                "colA→colB": {
                    "metrics": {...},
                    "categories": {...}
                },
                "colA→colC": { ... },
                ...
            }
        }
    """
    valid, _ = api.valid_oids(args)

    # Determine which (known, unknown) pairs to test
    if len(valid) >= 2:
        # User explicitly provided at least two IDs: only test that first pair
        pair_list = [(valid[0], valid[1])]
    else:
        # Fewer than two provided: iterate over all ordered pairs of collections
        all_cols = api.collection_cids()
        # e.g. [("colA","colB"), ("colA","colC"), ("colB","colA"), ...]
        pair_list = [
            (known, unknown)
            for known in all_cols
            for unknown in all_cols
            if known != unknown
        ]

    # Helper to run the existing logic on a single (known, unknown) pair:
    def _test_one_pair(known_cid, unknown_cid):
        # Build maps of executable OIDs → filename for each collection
        known_oids = list(_separate_oids(api.expand_oids(known_cid))[0])
        unknown_oids = list(_separate_oids(api.expand_oids(unknown_cid))[0])

        known_map = _get_all_file_names(known_oids)
        unknown_map = _get_all_file_names(unknown_oids)
        pairs = _pair_exes(known_map, unknown_map)

        if not pairs:
            return {"error": "No valid executable pairs to compare"}

        prec1 = hit2 = hit5 = 0
        mrr_sum = 0.0
        total = len(pairs)

        cat_at1 = []
        cat_at2 = []
        cat_at5 = []
        cat_missed = []

        for a_oid, b_oid in pairs:
            res = fuse_ex([a_oid, unknown_cid], opts)
            ranked_oids = [cand["oid"] for cand in res["results"]["candidates"]]

            try:
                rank = next(i + 1 for i, oid in enumerate(ranked_oids) if oid == b_oid)
            except StopIteration:
                rank = None

            # Accumulate @1, @2, @5 counts and category lists
            if rank == 1:
                prec1 += 1
                cat_at1.append((_get_file_names(a_oid), _get_file_names(ranked_oids[0])))
            elif rank == 2:
                hit2 += 1
                cat_at2.append((_get_file_names(a_oid), _get_file_names(ranked_oids[0])))
            elif rank and rank <= 5:
                hit5 += 1
                cat_at5.append((_get_file_names(a_oid), _get_file_names(ranked_oids[0])))
            else:
                cat_missed.append((_get_file_names(a_oid), _get_file_names(ranked_oids[0])))

            if rank:
                mrr_sum += 1.0 / rank

        return {
            "metrics": {
                "P@1": prec1 / total if total else 0.0,
                "Hit@2": (prec1 + hit2) / total if total else 0.0,
                "Hit@5": (prec1 + hit2 + hit5) / total if total else 0.0,
                "MRR": mrr_sum / total if total else 0.0,
                "total": total,
            },
            "categories": {
                "@1": cat_at1,
                "@2": cat_at2,
                "@5": cat_at5,
                "missed": cat_missed,
            },
        }

    # If exactly one pair was requested, just return its result
    if len(pair_list) == 1:
        known_cid, unknown_cid = pair_list[0]
        return _test_one_pair(known_cid, unknown_cid)

    # Otherwise, accumulate results for all pairs in a dictionary
    all_results = {}
    for known_cid, unknown_cid in pair_list:
        key = f"{known_cid}→{unknown_cid}"
        all_results[key] = _test_one_pair(known_cid, unknown_cid)

    return {"results": all_results}


def baseline_tlsh_batch_test(args, opts) -> Dict:
    """
    Run search_component over a test pair; report @1, @2, @5 accuracy, MRR,
    and list which component matches fall into each category.
    """
    valid, _ = api.valid_oids(args)
    if len(valid) < 2:
        raise ValueError("Usage: batch_test <firmware_cid_pair>")
    known, unknown = valid[:2]
    known_map = _get_all_file_names(list(_separate_oids(api.expand_oids(known))[0]))
    unknown_map = _get_all_file_names(list(_separate_oids(api.expand_oids(unknown))[0]))
    pairs = _pair_exes(known_map, unknown_map)
    if not pairs:
        return {"error": "No valid executable pairs to compare"}

    prec1 = hit2 = hit5 = 0
    mrr_sum = 0.0
    total = len(pairs)

    # Category tracking
    cat_at1 = []
    cat_at2 = []
    cat_at5 = []
    cat_missed = []

    for a, b in pairs:
        ranked_oids = _tlsh_rank_matches(a, list(unknown_map.keys()))
        
        try:
            rank = next(i + 1 for i, oid in enumerate(ranked_oids) if oid == b)
        except StopIteration:
            rank = None

        if rank == 1:
            prec1 += 1
            cat_at1.append((_get_file_names(a), _get_file_names(ranked_oids[0])))
        elif rank == 2:
            hit2 += 1
            cat_at2.append((_get_file_names(a), _get_file_names(ranked_oids[0])))
        elif rank and rank <= 5:
            hit5 += 1
            cat_at5.append((_get_file_names(a), _get_file_names(ranked_oids[0])))
        else:
            cat_missed.append((_get_file_names(a), _get_file_names(ranked_oids[0])))

        if rank:
            mrr_sum += 1.0 / rank

    return {
        "metrics": {
            "P@1": prec1 / total if total else 0.0,
            "Hit@2": (prec1 + hit2) / total if total else 0.0,
            "Hit@5": (prec1 + hit2 + hit5) / total if total else 0.0,
            "MRR": mrr_sum / total if total else 0.0,
            "total": total
        },
        "categories": {
            "@1": cat_at1,
            "@2": cat_at2,
            "@5": cat_at5,
            "missed": cat_missed
        }
    }

# Should run fuse with a single prompt that we pass in via a text file
def old_fuse_batch(args, opts) -> Dict:
    # options
    USE_TAGS = opts.get("use_tags", True)
    eps      = 1e-8

    # 1) collect component tokens
    valid, _ = api.valid_oids(args)
    exes, _  = _separate_oids(api.expand_oids(valid))

    components = {}
    for oid in exes:
        if any((".so" in n) or (".ko" in n) for n in _get_file_names(oid)):
            continue

        # strings
        raw     = api.get_field("strings", oid, oid) or {}
        strings = [s.lower() for s in raw.values()
                   if ALNUM.search(s) and len(s) < 60]

        # tags
        tags = []
        if USE_TAGS:
            inf = api.retrieve("tag_all_functions", oid) or {}
            if inf != "FAILED":
                for e in inf.values():
                    text = e.get("tag")
                    if isinstance(e, dict) and text:
                        tags.append(_normalize_tag(text))

        if strings or (USE_TAGS and tags):
            components[oid] = {"str": strings, "tag": tags}

    if not components:
        return {"error": "No tokens extracted from firmware!"}

    # 2) build IDF maps
    str_docs = {oid: comp["str"] for oid, comp in components.items()}
    idf_str  = _compute_idf(str_docs)

    if USE_TAGS:
        tag_docs = {oid: comp["tag"] for oid, comp in components.items()}
        idf_tag  = _compute_idf(tag_docs)

    # 3) select highest‑IDF strings (full budget) per component
    selected_tags = {}
    selected_strs = {}
    for oid, comp in components.items():
        if USE_TAGS:
            selected_tags[oid] = _select_until(comp["tag"], idf_tag, MAX_LEN)
            selected_strs[oid] = _select_until(comp["str"], idf_str, MAX_LEN)
        else:
            # all tokens go to strings
            selected_tags[oid] = []
            selected_strs[oid] = _select_until(comp["str"], idf_str, MAX_LEN)

    # 4) embed strings and tags
    oids = list(components)
    str_docs = [" ".join(selected_strs[oid]) for oid in oids]
    str_embs  = _model.encode(str_docs, normalize_embeddings=True, truncation=False)

    if USE_TAGS:
        tag_docs = [" ".join(selected_tags[o]) for o in oids]
        tag_embs  = _model.encode(tag_docs, normalize_embeddings=True, truncation=False)

    # 5) fuse vectors with dynamic weighting based on token counts
    fused_rows = []
    for i, oid in enumerate(oids):
        se = str_embs[i]
        if USE_TAGS:
            te = tag_embs[i]
            tok = tokenizer.encode
            n_s = sum(len(tok(s, add_special_tokens=False)) for s in selected_strs[oid])
            n_t = sum(len(tok(t, add_special_tokens=False)) for t in selected_tags[oid])
            alpha = n_t / (n_s + n_t + eps)
            se /= np.linalg.norm(se)
            te /= np.linalg.norm(te)
            v_adapt = (1 - alpha) * se + alpha * te
        else:
            v_adapt = se
        fused_rows.append(v_adapt / (np.linalg.norm(v_adapt) + 1e-8))

    emb_mat = np.vstack(fused_rows).astype("float32")

    # 6) retrieval & metrics (unchanged)
    prompts = list(prompts2oids.keys())
    batch   = []
    prec1 = hit2 = hit5 = 0
    mrr_sum = 0.0

    for prompt in prompts:
        qvec = _model.encode([prompt], normalize_embeddings=True).astype("float32")
        sims = emb_mat.dot(qvec.T).squeeze()
        idxs = np.argsort(-sims)

        def fmt(oid):
            return {
                "oid": oid,
                "names": _get_file_names(oid),
                "num functions": len(api.retrieve("tag_all_functions", oid) or {})
            }

        gold = prompts2oids[prompt]
        rank = next((i+1 for i in range(len(oids)) if oids[idxs[i]] == gold), None)

        prec1 += int(rank == 1)
        hit2  += int(rank and rank <= 2)
        hit5  += int(rank and rank <= 5)
        if rank:
            mrr_sum += 1.0 / rank

        batch.append({
            "prompt":  prompt,
            "results": {
                "best_match": fmt(oids[idxs[0]]),
                "candidates": [fmt(oids[i]) for i in idxs[:5]]
            },
            "rank":    rank,
            "gold":    fmt(gold)
        })

    n = len(prompts) or 1
    return {
        "batch": batch,
        "metrics": {
            "P@1":   prec1 / n,
            "Hit@2": hit2 / n,
            "Hit@5": hit5 / n,
            "MRR":    mrr_sum / n
        }
    }

exports = [fuse_nl, fuse_nl_batch, old_fuse_batch, fuse_nl_batch_by_size, fuse_ex, fuse_ex_batch_test, baseline_tlsh_batch_test]

# ---------------------------------------------------------------------------
# Core search helpers
# ---------------------------------------------------------------------------
def _search_by_prompt(exes, prompts: List[str], opts: Dict = {}, gold_map: Dict[str, str] = None) -> Dict[str, Any]:
    USE_TAGS = opts.get("use_tags", True)
    SHOW_DOCS = opts.get("show_docs", False)
    TAGS_CONTEXT = opts.get("tags_context", True)

    # 1) collect and filter components
    
    components = {}
    for oid in exes:
        if any((".so" in n) or (".ko" in n) for n in _get_file_names(oid)):
            continue

        # strings
        raw     = api.get_field("strings", oid, oid) or {}
        strings = [s.lower() for s in raw.values()
                   if ALNUM.search(s) and len(s) < 60]

        # tags
        tags = []
        if USE_TAGS:
            if TAGS_CONTEXT:
                inf = api.retrieve("tag_all_functions", oid) or {}
                if inf != "FAILED":
                    for e in inf.values():
                        text = e.get("tag_context")
                        if isinstance(e, dict) and text:
                            tags.append(_normalize_tag(text))
            else:
                inf = api.retrieve("tag_all_functions", oid) or {}
                if inf != "FAILED":
                    for e in inf.values():
                        text = e.get("tag")
                        if isinstance(e, dict) and text:
                            tags.append(_normalize_tag(text))

        if strings or (USE_TAGS and tags):
            components[oid] = {"str": strings, "tag": tags}

    if not components:
        return {"error": "No tokens extracted from firmware!"}

    # 2) compute IDF scores
    str_idf = _compute_idf({k: v['str'] for k, v in components.items()})
    tag_idf = _compute_idf({k: v['tag'] for k, v in components.items()}) if USE_TAGS else {}

    # 3) select highest-IDF tokens within budget
    selected_str = {oid: _select_until(comp['str'], str_idf, MAX_LEN) for oid, comp in components.items()}
    selected_tag = {oid: _select_until(comp['tag'], tag_idf, MAX_LEN) if USE_TAGS else [] for oid, comp in components.items()}

    if SHOW_DOCS == True:
        for oid in components:
            print(f"\nNames: {_get_file_names(oid)}" )
            print(f"Strings: {selected_str[oid]}")
            print(f"Tags: {selected_tag [oid]}")

    # 4) build embeddings
    oids = list(components)
    str_embs = _model.encode([" ".join(selected_str[o]) for o in oids],
                              normalize_embeddings=True, truncation=False)
    tag_embs = (_model.encode([" ".join(selected_tag[o]) for o in oids],
                        normalize_embeddings=True, truncation=False)
                if USE_TAGS else None)

    # 5) fuse embeddings
    fused = []
    eps = 1e-8
    for i, oid in enumerate(oids):
        se = str_embs[i] / (np.linalg.norm(str_embs[i]) + eps)
        if USE_TAGS:
            te = tag_embs[i] / (np.linalg.norm(tag_embs[i]) + eps)
            n_s = sum(len(tokenizer.tokenize(s)) for s in selected_str[oid])
            n_t = sum(len(tokenizer.tokenize(t)) for t in selected_tag[oid])
            alpha = n_t / (n_s + n_t + eps)
            vec = (1 - alpha) * se + alpha * te
        else:
            vec = se
        fused.append(vec / (np.linalg.norm(vec) + eps))
    emb_mat = np.vstack(fused).astype("float32")

    # 6) retrieval and optional metrics
    batch = []
    prec1 = hit2 = hit5 = 0
    mrr_sum = 0.0
    for prompt in prompts:
        qvec = _model.encode([prompt], normalize_embeddings=True).astype("float32")
        sims = emb_mat.dot(qvec.T).squeeze()
        idxs = np.argsort(-sims)
        # helper to format result
        def _fmt(idx): return {
            "oid": oids[idx],
            "names": api.get_names_from_oid(oids[idx]),
            "score": float(sims[idx])
        }
        res = {
            "prompt": prompt,
            "results": {
                "best_match": _fmt(idxs[0]),
                "candidates": [_fmt(i) for i in idxs[:5]]
            }
        }
        if gold_map and prompt in gold_map:
            gold = gold_map[prompt]
            gold_info = {"oid": gold_map[prompt], "names": _get_file_names(gold_map[prompt])}
            rank = next((i+1 for i in range(len(idxs)) if oids[idxs[i]] == gold), None)
            res.update({"rank": rank, "gold": gold_info})
            prec1 += int(rank == 1)
            hit2 += int(rank and rank <= 2)
            hit5 += int(rank and rank <= 5)
            if rank: mrr_sum += 1.0 / rank
        batch.append(res)

    out = {"batch": batch}
    if gold_map:
        n = len(prompts)
        out["metrics"] = {
            "P@1": prec1 / n,
            "Hit@2": hit2 / n,
            "Hit@5": hit5 / n,
            "MRR": mrr_sum / n
        }
    return out

def _search_by_example(component_oid: str, firmware_oids: List[str], opts: Dict = {}) -> Dict[str, Any]:
    USE_TAGS = opts.get("use_tags", True)
    TAGS_CONTEXT = opts.get("tags_context", True)

    # 1) Get reference component tags + strings
    def extract_tokens(oid):
        # strings
        raw = api.get_field("strings", oid, oid) or {}
        strings = [s.lower() for s in raw.values()
                   if ALNUM.search(s) and len(s) < 60]

        # tags (using tag_context if enabled)
        tags = []
        if USE_TAGS:
            inf = api.retrieve("tag_all_functions", oid) or {}
            if inf != "FAILED":
                for e in inf.values():
                    text = e.get("tag_context") if TAGS_CONTEXT else e.get("tag")
                    if isinstance(e, dict) and text:
                        tags.append(_normalize_tag(text))
        return {"str": strings, "tag": tags}

    comp_tokens = extract_tokens(component_oid)
    if not comp_tokens["str"] and not comp_tokens["tag"]:
        return {"error": f"No usable tokens found in component {component_oid}"}

    # 2) Build candidate token maps
    components = {}
    for oid in firmware_oids:
        # if any((".so" in n) or (".ko" in n) for n in _get_file_names(oid)):
        #     continue
        toks = extract_tokens(oid)
        if toks["str"] or toks["tag"]:
            components[oid] = toks

    if not components:
        return {"error": "No usable tokens found in candidate firmware."}

    # 3) IDF computation
    str_idf = _compute_idf({k: v['str'] for k, v in components.items()})
    tag_idf = _compute_idf({k: v['tag'] for k, v in components.items()}) if USE_TAGS else {}

    # 4) Select top tokens for fusion
    selected_str = _select_until(comp_tokens["str"], str_idf, MAX_LEN)
    selected_tag = _select_until(comp_tokens["tag"], tag_idf, MAX_LEN) if USE_TAGS else []

    comp_doc = " ".join(selected_str)
    comp_tag = " ".join(selected_tag)
    comp_str_emb = _model.encode([comp_doc], normalize_embeddings=True)[0]
    comp_tag_emb = _model.encode([comp_tag], normalize_embeddings=True)[0] if USE_TAGS else None

    # Fusion
    eps = 1e-8
    n_s = sum(len(tokenizer.tokenize(s)) for s in selected_str)
    n_t = sum(len(tokenizer.tokenize(t)) for t in selected_tag)
    alpha = n_t / (n_s + n_t + eps)
    comp_vec = (1 - alpha) * comp_str_emb + alpha * comp_tag_emb if USE_TAGS else comp_str_emb
    comp_vec = comp_vec / (np.linalg.norm(comp_vec) + eps)

    # 5) Encode candidates
    oids = list(components)
    str_docs = [" ".join(_select_until(components[o]['str'], str_idf, MAX_LEN)) for o in oids]
    tag_docs = [" ".join(_select_until(components[o]['tag'], tag_idf, MAX_LEN)) for o in oids] if USE_TAGS else None

    str_embs = _model.encode(str_docs, normalize_embeddings=True)
    tag_embs = _model.encode(tag_docs, normalize_embeddings=True) if USE_TAGS else None

    fused = []
    for i, oid in enumerate(oids):
        se = str_embs[i] / (np.linalg.norm(str_embs[i]) + eps)
        if USE_TAGS:
            te = tag_embs[i] / (np.linalg.norm(tag_embs[i]) + eps)
            n_s = sum(len(tokenizer.tokenize(s)) for s in _select_until(components[oid]['str'], str_idf, MAX_LEN))
            n_t = sum(len(tokenizer.tokenize(t)) for t in _select_until(components[oid]['tag'], tag_idf, MAX_LEN))
            alpha = n_t / (n_s + n_t + eps)
            vec = (1 - alpha) * se + alpha * te
        else:
            vec = se
        fused.append(vec / (np.linalg.norm(vec) + eps))

    emb_mat = np.vstack(fused).astype("float32")

    # 6) Search
    sims = emb_mat.dot(comp_vec)
    idxs = np.argsort(-sims)
    def _fmt(idx):
        oid = oids[idx]
        return {
            "oid": oid,
            "names": _get_file_names(oid),
            "score": float(sims[idx]),
        }

    return {
        "component": {"oid": component_oid, "names": _get_file_names(component_oid)},
        "results": {
            "best_match": _fmt(idxs[0]),
            "candidates": [_fmt(i) for i in idxs[:5]]
        }
    }

def _tlsh_rank_matches(target_oid, baseline_oids):
    """
    Ranks a single target executable against a list of baseline executables
    by TLSH distance (lower = more similar). Excludes any file where
    DISASM == 'FAIL' or missing/invalid TLSH.

    Returns:
      A list of baseline_oids sorted by increasing TLSH distance (most
      similar first). Returns an empty list if the target fails or
      no valid baselines remain.
    """
    # 1) Verify target disassembly
    disasm = api.retrieve('ghidra_disasm', target_oid)
    if not disasm or disasm.get("original_blocks", {}) == {}:
        return []

    # 2) Retrieve target TLSH
    target_hash = api.get_field("tlshash", target_oid, "hash")
    if not target_hash or target_hash == "TNULL":
        return []

    # 3) Score all valid baselines
    scored = []
    for baseline_oid in baseline_oids:
        # Skip if disassembly failed
        disasm_b = api.retrieve('ghidra_disasm', baseline_oid)
        if not disasm_b or disasm_b.get("original_blocks", {}) == {}:
            continue

        # Skip if no valid TLSH
        hash_b = api.get_field("tlshash", baseline_oid, "hash")
        if not hash_b or hash_b == "TNULL":
            continue

        # Compute distance and record
        dist = tlsh.diff(target_hash, hash_b)
        scored.append((baseline_oid, dist))

    # 4) Sort by distance and return only the oids
    scored.sort(key=lambda x: x[1])
    return [oid for oid, _ in scored]

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _normalize_tag(tag: str) -> str:
    try:
        from unicodedata import normalize as u_norm
        tag = u_norm('NFC', tag)
    except ImportError:
        pass
    tag = tag.replace('_', ' ')
    tag = re.sub(r"[^\w\s]", ' ', tag)
    return re.sub(r"\s+", ' ', tag).strip().lower()

def _compute_idf(docs):
    df = Counter()
    N  = len(docs)
    for toks in docs.values():
        for t in set(toks):
            df[t] += 1
    # standard smoothing to avoid zero/∞
    return {t: math.log((N+1)/(df_t+1)) + 1
            for t, df_t in df.items()}

def _select_until(tokens, idf_map, budget):
    chosen, used = [], 0
    for t in sorted(tokens, key=lambda x: idf_map.get(x,0), reverse=True):
        toklen = len(tokenizer.tokenize(t))
        if used + toklen > budget:
            continue
        chosen.append(t)
        used += toklen
        if used >= budget:
            break
    return chosen

def _separate_oids(oids: List[str]) -> Tuple[set, set]:
    """Split OIDs into executables and others"""
    exes, others = set(), set()
    for oid in oids:
        cat = api.get_field('categorize', oid, oid)
        (exes if cat == 'executable' else others).add(oid)
    return exes, others

def _get_file_names(oid: str) -> List[str]:
    """Return all recorded file names for an OID"""
    return list(api.get_names_from_oid(oid))

def _get_all_file_names(oids: List[str]) -> Dict[str, List[str]]:
    """Map OIDs to their file names"""
    return {oid: _get_file_names(oid) for oid in oids}

def _normalize_tag(tag: str) -> str:
    """Normalize tag text for comparison"""
    try:
        from unicodedata import normalize as u_norm
        tag = u_norm('NFC', tag)
    except ImportError:
        pass
    tag = tag.replace('_', ' ')
    tag = re.sub(r"[^\w\s]", ' ', tag)
    return re.sub(r"\s+", ' ', tag).strip().lower()

def _pair_exes(map1: Dict[str,List[str]], map2: Dict[str,List[str]]) -> List[Tuple[str,str]]:
    """Match OIDs by shared file names"""
    pairs = []
    for a, na in map1.items():
        for b, nb in map2.items():
            if set(na) & set(nb):
                pairs.append((a, b))
    return pairs

# ---------------------------------------------------------------------------
#  ground_truth_semantic.py
#  Mapping: <semantic prompt>  →  [expected OID(s)]
# ---------------------------------------------------------------------------

prompts2oids = {
    # 1  BusyBox ─ basic shell & core utilities
    "Component providing basic shell and file management functionality: directory listing, file read/write, permission changes, and command execution.": 
        "598cd0a2dfb5d69f561413cb823e9543f7ba143e",

    # 2  Dropbear ─ SSH server / client / key-gen
    "Component that establishes encrypted remote shell sessions (SSH) and transfers files securely over a network channel.": 
        "93073b5d2844d703f9b1e00061a6dcd7dd90b915",

    # 3  Dnsmasq ─ DNS & DHCPv4
    "Component performing hostname-to-IP resolution and dynamic IPv4 address assignment via DNS queries and DHCP leases.": 
        "a5ce6fe192eb83e7ff73ebebcf0702fb383ac849",

    # 4  odhcpd ─ DHCPv6 server
    "Component acting as a DHCPv6 server: allocating and renewing IPv6 addresses for LAN clients.": 
        "a1a70b2921458e230db618426c0d6127df2873c3",

    # 5  odhcp6c ─ DHCPv6 client
    "Component acting as a DHCPv6 client: sending solicit/advertise messages, processing replies, and configuring IPv6 network interfaces.": 
        "3e6ffe5a37d67d3440bba0553e00bae19aca74c0",

    # 6  procd (+ init)
    "Component that initializes and supervises system services at startup, handles dependencies, and restarts failed processes.": 
        "cddc3a80206f059be2928a899bb8affff52e7391",

    # 7  opkg
    "Component managing software packages: downloading, installing, removing, and verifying package integrity.": 
        "1f3c7713942119dc2111ac1f2547a98e20037cb8",

    # 8  rpcd
    "Component exposing firmware control APIs over HTTP, handling request parsing and routing for remote management.": 
        "f97d7a0e1408efe9a65caa8de07879d3ac4af37c",

    # 9  uHTTPd
    "Component serving HTTP requests for a web UI: parsing requests, routing URLs, and invoking backend modules via CGI or equivalent.": 
        "c34b9f27e2f885f647cff0e5af27b6ab48976480",

    # 10 ubusd (daemon)
    "Component providing IPC on a system bus: accepting connections, dispatching messages, and coordinating inter-process calls.": 
        "d77c79c48c48df4eaecf99bb4b73084d7c358396",

    # 11 ubus CLI
    "Command‑line tool for sending and receiving messages over the system bus IPC interface.": 
        "083884f9b8e76298d539feb87956aa8b733a73cf",

    # 12 UCI
    "Component that reads, validates, updates, and distributes central configuration data to other firmware modules.": 
        "e0c64b9ab68a2c3128cd2fa28357b55381fb97ba",

    # 14 usign
    "Component that verifies digital signatures on firmware packages to ensure authenticity before installation.": 
        "f0b324580131e53d0a1d4419c539e9b3b36414f6",

    # 15 fwtool
    "Component inspecting and editing embedded firmware metadata: reading headers, modifying fields, and saving updates.": 
        "fccbe365c35aa4e1289677e9541e136875a026e5",

    # 16 uclient-fetch
    "Component that fetches files from HTTP or FTP servers: connecting, downloading payloads, and handling retries and redirects.": 
        "b7c21e6332a8641008ced7518c211837ddc04fc2",

    # 17 urngd
    "Component gathering entropy from hardware sources and feeding it into the kernel's pseudo-random number generator.": 
        "f35975fad43e4a6167e136734edefc57b9a307ff",

    # 18 cgi-io
    "Component handling file uploads and downloads over HTTP: parsing multipart streams, writing to storage, and sending responses.": 
        "4a38ddb2f9ffde8a939059e1a09852f8904e870e",

    # 19 mtd utility
    "Component that programs raw device partitions with firmware images: erasing, writing sectors, and verifying integrity.": 
        "139c1b29cf332ffb9da94a44d6d5c024b343d836",

    # 20 pppd (PPPoE)
    "Component establishing and managing PPPoE sessions: discovery, session negotiation, authentication, and maintenance.": 
        "520849dbcad715c659217fba5011590f54d09f26",

    # 21 nftables
    "Component filtering network packets by IP, port, and protocol rules to enforce firewall and NAT policies.": 
        "718bcacc3751b150fc84a538fad02f6378b6bc5f",

    # 22 kmodloader
    "Component responsible for loading, initializing, and unloading kernel modules (device drivers) during boot.": 
        "70dacfd82fd271b6f15c23ec777e3d9aab679cd8",

    # 23 mount_root
    "Component that mounts the real root filesystem on top of an initramfs: creating directories, pivoting mounts, and execing init.": 
        "fd668ce90af37b419b8d343f66d39cff68ea414a",

    # 24 ujail
    "Component creating isolated sandboxes for processes: setting up namespaces, resource limits, and seccomp filters.": 
        "71692cdb8dd66cc2cdf8515a12f19d7e0af1b2cd",

    # 25 jsonfilter
    "Component parsing JSON from a byte stream in shell scripts: handling objects, arrays, nested structures, and errors.": 
        "1eb9c0a8335156dd24243bf3570b2f88f32ebe1d",
}
