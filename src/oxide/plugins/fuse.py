import json
import math
import re
import logging
from collections import Counter, defaultdict
from typing import List, Dict, Tuple, Optional, Any
import os
from pathlib import Path
import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import pearsonr
import time

try:
    from rank_bm25 import BM25Okapi
except ImportError:
    BM25Okapi = None


import numpy as np
from sentence_transformers import SentenceTransformer
from transformers import AutoTokenizer

from oxide.core import api

AUTHOR="Nathan"
NAME="fuse"

# -------------------------------------------------------------
# Configuration & Setup
# -------------------------------------------------------------
MODEL_ID = "sentence-transformers/all-MiniLM-L6-v2"
tokenizer = AutoTokenizer.from_pretrained(MODEL_ID)
model = SentenceTransformer(MODEL_ID)
MAX_TOKENS = tokenizer.model_max_length
ALNUM = re.compile(r"[A-Za-z]{3,}")

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(NAME)

# ---------------------------------------------------------------------------
# Entry points
# ---------------------------------------------------------------------------
def fuse(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Search for a single prompt loaded from a text file."""
    prompt_path = opts.get('prompt')
    if not prompt_path:
        return {'error': "Please provide a '.txt' via 'prompt' option."}

    try:
        with open(prompt_path) as fp:
            prompt = fp.read().strip()
    except OSError as e:
        return {'error': f'Failed to read prompt: {e}'}
    
    cid = api.valid_oids(args)[0]
    return search_prompt(cid, prompt, use_tags=opts.get('use_tags', True))

def fuse_batch(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Run batch NL search across collections, returning per-collection and global metrics plus avg retrieval time in ms."""
    comp_path   = opts.get('comp_path')
    prompt_path = opts.get('prompt_path')
    if not comp_path or not prompt_path:
        print("Error: 'comp_path' or 'prompt_path' not provided.")
        return {'error': "Use 'comp_path' and 'prompt_path' to specify JSON file paths."}

    # 1) load ground truth
    comp_map = create_ground_truth(comp_path)

    # 2) load prompts
    try:
        with open(prompt_path, 'r') as f:
            prompt_map = json.load(f)
    except Exception as e:
        print(f"Error loading prompt JSON: {e}")
        return {'error': f"Failed to load prompt JSON: {e}"}

    per_collection: Dict[str, Any] = {}
    total_queries = 0
    sum_p1 = sum_h2 = sum_h5 = sum_mrr = 0.0

    # *** accumulate in nanoseconds to avoid any epoch confusion ***
    total_search_time_ns = 0

    for cid, golds in comp_map.items():
        colname = api.get_colname_from_oid(cid)
        print(f"Processing collection '{colname}' (CID: {cid})...")

        batch_res: List[Dict[str, Any]] = []
        ranks_map: Dict[str, int] = {}

        for idx, (comp, gold_oid) in enumerate(golds.items(), start=1):
            prompt = prompt_map.get(comp)
            if prompt is None:
                print(f"  Skipping missing prompt for component: {comp}")
                continue

            print(f"  Prompt {idx}/{len(golds)}: '{prompt[:50]}{'...' if len(prompt)>50 else ''}'")
            # --- time just the search_prompt call ---
            start_ns = time.perf_counter_ns()
            out = search_prompt(cid, prompt, use_tags=opts.get('use_tags', True))
            elapsed_ns = time.perf_counter_ns() - start_ns
            total_search_time_ns += elapsed_ns

            # compute rank
            cands = out['results']['candidates']
            oid_list = [c['oid'] for c in cands]
            rank = oid_list.index(gold_oid) + 1

            batch_res.append({'component': comp, 'rank': rank, 'gold': gold_oid})

            # update global accumulators
            sum_p1  += (rank == 1)
            sum_h2  += (rank <= 2)
            sum_h5  += (rank <= 5)
            sum_mrr += (1.0 / rank)
            total_queries += 1

            ranks_map[comp] = rank

        if batch_res:
            n = len(batch_res)
            per_collection[colname] = {
                'metrics': {
                    'P@1':   sum(1 for r in batch_res if r['rank']==1) / n,
                    'Hit@2': sum(1 for r in batch_res if r['rank']<=2) / n,
                    'Hit@5': sum(1 for r in batch_res if r['rank']<=5) / n,
                    'MRR':   sum((1.0/r['rank']) for r in batch_res) / n
                },
                'ranks_by_prompt': ranks_map
            }

    if total_queries == 0:
        print("No prompts tested.")
        return {'error': 'No prompts tested.'}

    # 3) Global metrics
    global_metrics = {
        'P@1':   sum_p1  / total_queries,
        'Hit@2': sum_h2  / total_queries,
        'Hit@5': sum_h5  / total_queries,
        'MRR':   sum_mrr / total_queries
    }

    # 4) nanoseconds → ms, then format as a string to avoid any timestamp conversion
    avg_retrieval_time_ms = (total_search_time_ns / total_queries) / 1_000_000.0
    avg_retrieval_time_ms_str = f"{avg_retrieval_time_ms:.3f}"

    # **Returned value is a plain float**—no datetime conversion anywhere!
    return {
        'per_collection':        per_collection,
        'global_metrics':        global_metrics,
        'avg_retrieval_time_ms': avg_retrieval_time_ms_str
    }

def baseline_fuse_bm25(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    BM25 baseline outputting per_collection, global_metrics, and avg query time in ms.
    """
    comp_path = opts.get("comp_path")
    prompt_path = opts.get("prompt_path")
    if not comp_path or not prompt_path:
        return {"error": "Use 'comp_path' and 'prompt_path' to specify JSON files."}
    if not os.path.isfile(prompt_path) or not prompt_path.endswith('.json'):
        return {"error": "The 'prompt_path' must be a .json file."}

    try:
        with open(prompt_path) as f:
            prompt_map = json.load(f)
    except Exception as e:
        return {"error": f"Failed to load prompt JSON: {e}"}

    comp_map = create_ground_truth(comp_path)
    
    # global accumulators
    global_acc = {'total': 0, 'sum_p1': 0, 'sum_h2': 0, 'sum_h5': 0, 'sum_mrr': 0.0}
    per_collection: Dict[str, Any] = {}

    # timing accumulators
    total_search_time_ns = 0
    total_queries = 0

    for cid, oid_map in comp_map.items():
        colname = api.get_colname_from_oid(cid)
        oids, _ = api.valid_oids([cid])
        exes = filter_executables(api.expand_oids(oids))

        # build corpus for BM25
        exe_oids: List[str] = []
        corpus: List[List[str]] = []
        for comp_name, exe_oid in oid_map.items():
            if exe_oid in exes:
                strings = api.get_field("strings", exe_oid, exe_oid) or {}
                tokens = list(strings.values())
                if tokens:
                    exe_oids.append(exe_oid)
                    corpus.append(tokens)

        bm25 = None
        if BM25Okapi and corpus:
            try:
                bm25 = BM25Okapi(corpus)
            except Exception:
                bm25 = None

        # evaluate prompts
        batch_res: List[Dict[str, Optional[int]]] = []
        ranks_map: Dict[str, Optional[int]] = {}

        for comp_name, gold_oid in oid_map.items():
            prompt = prompt_map.get(comp_name)
            if not prompt or bm25 is None:
                ranks_map[comp_name] = None
                continue

            query_tokens = prompt.split()

            # time this BM25 query+ranking
            start_ns = time.perf_counter_ns()
            scores = bm25.get_scores(query_tokens)
            ranked = sorted(zip(exe_oids, scores), key=lambda x: x[1], reverse=True)
            ranked_oids = [oid for oid, _ in ranked]

            try:
                rank = ranked_oids.index(gold_oid) + 1
            except ValueError:
                rank = None

            elapsed_ns = time.perf_counter_ns() - start_ns
            total_search_time_ns += elapsed_ns
            total_queries += 1

            batch_res.append({'component': comp_name, 'rank': rank})
            ranks_map[comp_name] = rank

            # update global accumulators
            global_acc['total'] += 1
            global_acc['sum_p1'] += int(rank == 1)
            global_acc['sum_h2'] += int(rank is not None and rank <= 2)
            global_acc['sum_h5'] += int(rank is not None and rank <= 5)
            global_acc['sum_mrr'] += (1.0 / rank) if rank else 0.0

        # compute collection metrics
        n = len(batch_res)
        metrics: Dict[str, float] = {}
        if n > 0:
            metrics = {
                'P@1':   sum(1 for r in batch_res if r['rank'] == 1) / n,
                'Hit@2': sum(1 for r in batch_res if r['rank'] and r['rank'] <= 2) / n,
                'Hit@5': sum(1 for r in batch_res if r['rank'] and r['rank'] <= 5) / n,
                'MRR':   sum((1.0 / r['rank']) for r in batch_res if r['rank']) / n
            }

        per_collection[colname] = {
            'metrics': metrics,
            'ranks_by_prompt': ranks_map
        }

    # compute global metrics
    T = global_acc['total'] or 1
    global_metrics = {
        'bm25': {
            'P@1':   global_acc['sum_p1'] / T,
            'Hit@2': global_acc['sum_h2'] / T,
            'Hit@5': global_acc['sum_h5'] / T,
            'MRR':   global_acc['sum_mrr'] / T
        }
    }

    # 4) nanoseconds → ms, then format as a string to avoid any timestamp conversion
    avg_retrieval_time_ms = (total_search_time_ns / total_queries) / 1_000_000.0
    avg_retrieval_time_ms_str = f"{avg_retrieval_time_ms:.3f}"

    return {
        'per_collection':        per_collection,
        'global_metrics':        global_metrics,
        'avg_retrieval_time_ms': avg_retrieval_time_ms_str
    }


def baseline_fuse_bm25_best(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    BM25-best baseline outputting per_collection and global_metrics
    in the same format as fuse_batch_dual.
    """
    comp_path = opts.get("comp_path")
    prompt_path = opts.get("prompt_path")
    if not comp_path or not prompt_path:
        return {"error": "Use 'comp_path' and 'prompt_path' to specify JSON files."}
    if not os.path.isfile(prompt_path) or not prompt_path.endswith('.json'):
        return {"error": "The 'prompt_path' must be a .json file."}

    try:
        with open(prompt_path) as f:
            prompt_map = json.load(f)
    except Exception as e:
        return {"error": f"Failed to load prompt JSON: {e}"}

    comp_map = create_ground_truth(comp_path)
    global_acc = {'total': 0, 'sum_p1': 0, 'sum_h2': 0, 'sum_h5': 0, 'sum_mrr': 0.0}
    per_collection: Dict[str, Any] = {}

    for cid, oid_map in comp_map.items():
        colname = api.get_colname_from_oid(cid)
        oids, _ = api.valid_oids([cid])
        exes = filter_executables(api.expand_oids(oids))

        # corpus for BM25
        exe_oids: List[str] = []
        corpus: List[List[str]] = []
        for comp_name, exe_oid in oid_map.items():
            if exe_oid in exes:
                strings = api.get_field("strings", exe_oid, exe_oid) or {}
                tokens = list(strings.values())
                if tokens:
                    exe_oids.append(exe_oid)
                    corpus.append(tokens)

        bm25 = None
        if BM25Okapi and corpus:
            try:
                bm25 = BM25Okapi(corpus)
            except Exception:
                bm25 = None

        batch_res: List[Dict[str, Optional[int]]] = []
        ranks_map: Dict[str, Optional[int]] = {}

        for comp_name, gold_oid in oid_map.items():
            prompt = prompt_map.get(comp_name)
            if not prompt:
                continue
            query_tokens = prompt.split()

            best_rank: Optional[int] = None

            scores_full = bm25.get_scores(query_tokens)
            ranked_full = sorted(zip(exe_oids, scores_full), key=lambda x: x[1], reverse=True)
            ranked_oids_full = [oid for oid, _ in ranked_full]
            try:
                rank_full = ranked_oids_full.index(gold_oid) + 1
            except ValueError:
                rank_full = None
            best_rank = rank_full

            # each token
            for tok in set(query_tokens):
                scores_tok = bm25.get_scores([tok])
                ranked_tok = sorted(zip(exe_oids, scores_tok), key=lambda x: x[1], reverse=True)
                ranked_oids_tok = [oid for oid, _ in ranked_tok]
                try:
                    rank_tok = ranked_oids_tok.index(gold_oid) + 1
                except ValueError:
                    rank_tok = None

                if rank_tok and (best_rank is None or rank_tok < best_rank):
                    best_rank = rank_tok

            batch_res.append({'component': comp_name, 'rank': best_rank})
            ranks_map[comp_name] = best_rank

            global_acc['total'] += 1
            global_acc['sum_p1'] += int(best_rank == 1)
            global_acc['sum_h2'] += int(best_rank is not None and best_rank <= 2)
            global_acc['sum_h5'] += int(best_rank is not None and best_rank <= 5)
            global_acc['sum_mrr'] += (1.0 / best_rank) if best_rank else 0.0

        n = len(batch_res)
        metrics: Dict[str, float] = {}
        if n > 0:
            metrics = {
                'P@1':   sum(1 for r in batch_res if r['rank'] == 1) / n,
                'Hit@2': sum(1 for r in batch_res if r['rank'] and r['rank'] <= 2) / n,
                'Hit@5': sum(1 for r in batch_res if r['rank'] and r['rank'] <= 5) / n,
                'MRR':   sum((1.0 / r['rank']) for r in batch_res if r['rank']) / n
            }

        per_collection[colname] = {
            'metrics': metrics,
            'ranks_by_prompt': ranks_map
        }

    # compute global metrics
    T = global_acc['total'] or 1
    global_metrics = {
        'bm25_best': {
            'P@1':   global_acc['sum_p1'] / T,
            'Hit@2': global_acc['sum_h2'] / T,
            'Hit@5': global_acc['sum_h5'] / T,
            'MRR':   global_acc['sum_mrr'] / T
        }
    }

    return {'per_collection': per_collection, 'global_metrics': global_metrics}


def run_all(args, opts):
    results = {}
    results['FUSE'] = fuse_batch(args, opts)
    opts['use_tags'] = False
    results['FUSE_no_Tags'] = fuse_batch(args, opts)
    results['BM25'] = baseline_fuse_bm25(args, opts)
    results['BM25-UB'] = baseline_fuse_bm25_best(args, opts)

    return results


def effort_analysis(args, opts):
    """
    Compute analyst-effort statistics and save CDF plot.

    Args:
        args, opts: forwarded to run_all()

    Returns:
        table_data: dict mapping system →
            {'median', 'mean', 'p75', 'p90'}
    """
    data = run_all(args, opts)
    systems = ['BM25', 'BM25-UB', 'FUSE_no_Tags', 'FUSE']

    # --------------------------------------------------
    # Collect ranks for each system
    # --------------------------------------------------
    all_ranks = {}
    for sys in systems:
        ranks = []
        for col_data in data[sys]['per_collection'].values():
            ranks.extend(col_data['ranks_by_prompt'].values())
        all_ranks[sys] = np.asarray(ranks)

    stats = {
        sys: {
            'median': float(np.median(r)),
            'mean'  : float(np.mean(r)),
            'p75'   : float(np.percentile(r, 75)),
            'p90'   : float(np.percentile(r, 90)),
        }
        for sys, r in all_ranks.items()
    }

    # Table-friendly dict (same keys, but only the needed fields)
    table_data = {
        sys: {k: v for k, v in stats[sys].items()
                     if k in ('median', 'mean', 'p75', 'p90')}
        for sys in systems
    }

    max_rank = max(r.max() for r in all_ranks.values())
    plt.figure(figsize=(8, 5))

    for sys in systems:
        ranks = all_ranks[sys]
        xs = np.arange(1, max_rank + 1)
        ys = (ranks[:, None] <= xs).mean(axis=0)  # vectorised CDF
        plt.step(xs, ys, where="post", label=sys)

    plt.xlabel("Rank of Correct Result")
    plt.ylabel("Cumulative Percentage of Queries Resolved")
    plt.grid(True, linestyle="--", linewidth=0.5)
    plt.legend()
    plt.tight_layout()
    plt.savefig("effort_cdf.pdf")
    plt.close()

    return table_data

def component_analysis(args, opts):
    """
    Compute per-component retrieval metrics + avg size / #strings / #tags / tag density,
    and Pearson correlation between features and median rank.

    Args:
        args, opts: forwarded to fuse_batch()

    Returns:
        metrics: dict mapping
          component → {
            'median', 'mean', 'p75', 'p90',
            'P@1', 'Hit@2', 'Hit@5', 'MRR',
            'avg_size', 'avg_strings', 'avg_tags', 'tag_density'
          }
        Plus a reserved '__correlation__' key with Pearson r values.
    """
    # 1) Run the search
    data = fuse_batch(args, opts)

    # 2) Load ground truth: {collection → {component: oid, ...}}
    ground_truth = create_ground_truth(opts['comp_path'])

    # 3) Gather raw feature lists per component
    feat_map = defaultdict(list)
    for cid, oid_map in ground_truth.items():
        for comp, oid in oid_map.items():
            size = api.get_field("file_meta", oid, "size")
            strings = len(api.get_field("strings", oid, oid))
            tags = len(api.retrieve("tag_all_functions", oid))
            feat_map[comp].append((size, strings, tags))

    # 4) Gather all retrieval ranks per component
    comp_ranks = defaultdict(list)
    for col_data in data['per_collection'].values():
        for comp, rank in col_data['ranks_by_prompt'].items():
            comp_ranks[comp].append(rank)

    # 5) Compute metrics
    metrics = {}
    for comp, ranks in comp_ranks.items():
        arr = np.asarray(ranks, dtype=float)

        feats = np.asarray(feat_map.get(comp, []), dtype=float)
        if feats.size:
            sizes, strings, tags = feats.T
        else:
            sizes = strings = tags = np.array([], dtype=float)

        avg_size = float(sizes.mean()) if sizes.size else None
        avg_strings = float(strings.mean()) if strings.size else None
        avg_tags = float(tags.mean()) if tags.size else None
        tag_density = avg_tags / avg_strings if avg_strings else None

        stats = {
            'median'     : float(np.median(arr)),
            'mean'       : float(np.mean(arr)),
            'p75'        : float(np.percentile(arr, 75)),
            'p90'        : float(np.percentile(arr, 90)),
            'P@1'        : float((arr == 1).mean()),
            'Hit@2'      : float((arr <= 2).mean()),
            'Hit@5'      : float((arr <= 5).mean()),
            'MRR'        : float((1.0 / arr).mean()),
            'avg_size'   : avg_size,
            'avg_strings': avg_strings,
            'avg_tags'   : avg_tags,
            'tag_density': tag_density,
        }
        metrics[comp] = stats

    # 6) Compute Pearson correlation between median rank and features
    x_ranks = []
    x_size = []
    x_strings = []
    x_tags = []
    x_density = []

    for comp, stats in metrics.items():
        if any(v is None for v in [stats['avg_size'], stats['avg_strings'], stats['avg_tags'], stats['tag_density']]):
            continue
        x_ranks.append(stats['median'])
        x_size.append(stats['avg_size'])
        x_strings.append(stats['avg_strings'])
        x_tags.append(stats['avg_tags'])
        x_density.append(stats['tag_density'])

    corr = {
        'avg_size':    pearsonr(x_ranks, x_size)[0],
        'avg_strings': pearsonr(x_ranks, x_strings)[0],
        'avg_tags':    pearsonr(x_ranks, x_tags)[0],
        'tag_density': pearsonr(x_ranks, x_density)[0],
    }

    metrics['__correlation__'] = corr
    return metrics

def measure_string_overlap(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Measures string-overlap between components per collection and computes averages across all collections.
    Also generates a per-component commonality metric (average overlap count across all other components).

    Returns a mapping with:
      - per-collection overlaps
      - '_all_collections_': average overlaps per component-other pair
      - '_commonality_': { component: avg_overlap_count }
    """
    comp_path = opts.get("comp_path")
    if not comp_path:
        return {"error": "Use 'comp_path' to specify the component-ground-truth JSON file."}

    comp_map = create_ground_truth(comp_path)
    per_collection: Dict[str, Any] = {}

    # Accumulate stats across collections
    global_acc: Dict[Tuple[str, str], List[int]] = {}

    for cid, oid_map in comp_map.items():
        colname = api.get_colname_from_oid(cid)
        comp_strings: Dict[str, Set[str]] = {}
        for comp_name, oid in oid_map.items():
            raw = api.get_field("strings", oid, oid) or {}
            comp_strings[comp_name] = set(raw.values())

        comp_overlap: Dict[str, List[Dict[str, Any]]] = {}
        names = list(comp_strings.keys())
        for comp in names:
            s1 = comp_strings[comp]
            overlaps: List[Dict[str, Any]] = []
            for other in names:
                if other == comp:
                    continue
                s2 = comp_strings[other]
                inter = s1 & s2
                count = len(inter)
                # record for global average count
                key = (comp, other)
                global_acc.setdefault(key, []).append(count)
                overlaps.append({
                    'component': other,
                    'overlap_count': count
                })
            overlaps.sort(key=lambda x: x['overlap_count'], reverse=True)
            comp_overlap[comp] = overlaps
        per_collection[colname] = comp_overlap

    # Compute average overlap counts across collections
    avg_map: Dict[str, Dict[str, float]] = {}
    for (comp, other), counts in global_acc.items():
        avg_count = sum(counts) / len(counts)
        avg_map.setdefault(comp, {})[other] = avg_count

    # Prepare all_collections averages
    all_collections: Dict[str, List[Dict[str, Any]]] = {}
    for comp, others in avg_map.items():
        lst = [
            {'component': other, 'avg_overlap_count': avg}
            for other, avg in sorted(others.items(), key=lambda x: x[1], reverse=True)
        ]
        all_collections[comp] = lst

    # Compute per-component commonality metric: mean of average overlaps with all others
    commonality: Dict[str, float] = {}
    for comp, others in avg_map.items():
        values = list(others.values())
        commonality[comp] = sum(values) / len(values) if values else 0.0

    # Assemble final result
    # per_collection['_all_collections_'] = all_collections
    per_collection['_commonality_'] = commonality
    return per_collection


def measure_search_latency(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Retrieves the average per-query latency (in ms) reported by
    baseline_fuse_bm25 and fuse_batch themselves.
    """
    if not opts.get('comp_path') or not opts.get('prompt_path'):
        return {"error": "Use 'comp_path' and 'prompt_path' in opts for latency measurement."}

    # run BM25 baseline and grab its avg_retrieval_time_ms
    bm25_res = baseline_fuse_bm25(args, opts)
    bm25_ms = bm25_res.get('avg_retrieval_time_ms')
    if bm25_ms is None:
        return {"error": "baseline_fuse_bm25 did not return avg_retrieval_time_ms"}

    # run FUSE semantic search and grab its avg_retrieval_time_ms
    fuse_res = fuse_batch(args, opts)
    fuse_ms = fuse_res.get('avg_retrieval_time_ms')
    if fuse_ms is None:
        return {"error": "fuse_batch did not return avg_retrieval_time_ms"}

    return {
        'bm25_ms': bm25_ms,
        'fuse_ms': fuse_ms
    }

def process_collection(args, opts):
    return


exports = [fuse, fuse_batch, baseline_fuse_bm25, baseline_fuse_bm25_best, run_all, effort_analysis, component_analysis, measure_search_latency]

# -------------------------------------------------------------
# Embedding & Search
# -------------------------------------------------------------

def build_embedding_matrix(oids: List[str], use_tags: bool = True) -> Tuple[np.ndarray, Dict[str, float], Dict[str, float]]:
    """Generate fused embedding matrix and IDF maps for oids."""
    tokens_map = {oid: extract_tokens(oid, use_tags) for oid in oids}
    str_idf = compute_idf({k: v['str'] for k, v in tokens_map.items()})
    tag_idf = compute_idf({k: v['tag'] for k, v in tokens_map.items()}) if use_tags else {}

    vectors = []
    eps = 1e-8
    for oid in oids:
        # Prepare string embedding
        strs = select_until(tokens_map[oid]['str'], str_idf, MAX_TOKENS)
        str_doc = ' '.join(strs)
        str_emb = model.encode(str_doc, normalize_embeddings=True)

        if use_tags:
            tags = select_until(tokens_map[oid]['tag'], tag_idf, MAX_TOKENS)
            tag_doc = ' '.join(tags)
            tag_emb = model.encode(tag_doc, normalize_embeddings=True)
            n_s = len(tokenizer.tokenize(str_doc))
            n_t = len(tokenizer.tokenize(tag_doc))
            alpha = n_t / (n_s + n_t + eps)
            vec = (1 - alpha) * str_emb + alpha * tag_emb
        else:
            vec = str_emb

        vectors.append(vec / (np.linalg.norm(vec) + eps))

    return np.vstack(vectors).astype('float32')


def search_prompt(cid: str, prompt: str, use_tags: bool = True) -> Dict[str, Any]:
    """Search a prompt over given OIDs, returning all ranked matches."""
    exes = filter_executables(api.expand_oids(cid))

    # Retrieve/Generate Embedding Matrix
    if api.local_exists(NAME, f"{cid}_{use_tags}"):
        emb_mat = api.local_retrieve(NAME, f"{cid}_{use_tags}")[cid]
    else:
        emb_mat = build_embedding_matrix(exes, use_tags)
        api.local_store(NAME, f"{cid}_{use_tags}", {cid: emb_mat})

    q = model.encode(prompt, normalize_embeddings=True).astype('float32')
    sims = emb_mat.dot(q)
    idxs = np.argsort(-sims)  # sort all scores descending

    def fmt(i: int) -> Dict[str, Any]:
        return {'oid': exes[i], 'names': get_names(exes[i]), 'score': float(sims[i])}

    # build full ranked list
    ranked = [fmt(i) for i in idxs]
    best = ranked[0] if ranked else None
    return {
        'prompt': prompt,
        'results': {
            'best_match': best,
            'candidates': ranked
        }
    }

# -------------------------------------------------------------
# Utilities
# -------------------------------------------------------------

def create_ground_truth(data_path):
    """
    Build a mapping { collection_cid: { component_name: oid, … }, … }
    by matching each OID’s names to the basenames of the file paths in your JSON.
    """
    data = json.loads(Path(data_path).read_text())

    ground_truth = {}
    for cid in api.collection_cids():
        c_name = api.get_colname_from_oid(cid)
        if c_name not in data:
            # skip collections we have no JSON for
            continue

        collection_data = data[c_name]


        oids = api.expand_oids(cid)
        # build a name→component map from your ground truth
        basename_map = {}
        for component, paths in collection_data.items():
            # normalize to list
            candidates = paths if isinstance(paths, list) else [paths]
            for p in candidates:
                basename_map[component] = Path(p).name

        ground_truth[cid] = build_col_gt(filter_executables(api.expand_oids(oids)), basename_map)

    return ground_truth

def build_col_gt(exes, basename_map):
    col_gt = {}
    for oid in exes:
        for name in api.get_names_from_oid(oid):
            # find first c such that basename_map[c] == name
            match = next((c for c, f in basename_map.items() if f == name), None)
            if match is not None:
                col_gt[match] = oid
                break  # break out of `for name`
    return col_gt

def normalize(text: str) -> str:
    """Normalize tag or context text."""
    try:
        from unicodedata import normalize as u_norm
        text = u_norm('NFC', text)
    except ImportError:
        pass
    text = text.replace('_', ' ')
    text = re.sub(r"[^\w\s]", ' ', text)
    return re.sub(r"\s+", ' ', text).strip().lower()


def get_names(oid: str) -> List[str]:
    """Return all recorded file names for an OID."""
    return list(api.get_names_from_oid(oid))


def separate_oids(oids: List[str]) -> Tuple[List[str], List[str]]:
    """Split OIDs into executables and others."""
    exes, others = [], []
    for oid in oids:
        cat = api.get_field('categorize', oid, oid)
        if cat == 'executable':
            exes.append(oid)
        else:
            others.append(oid)
    return exes, others


def filter_executables(oids: List[str]) -> List[str]:
    """Filter out .so and .ko executables."""
    exes, _ = separate_oids(oids)
    filtered = []
    for oid in exes:
        names = get_names(oid)
        if not any(ext in name for name in names for ext in ('.so', '.ko')):
            filtered.append(oid)
    return filtered


def extract_tokens(oid: str, use_tags: bool = True, tags_context: bool = False) -> Dict[str, List[str]]:
    """Extract and normalize strings and tags for an OID."""
    raw_strs = api.get_field('strings', oid, oid) or {}
    strings = [s.lower() for s in raw_strs.values()
               if ALNUM.search(s) and len(s) < 60]

    tags: List[str] = []
    if use_tags:
        inf = api.retrieve('tag_all_functions', oid) or {}
        if inf != 'FAILED':
            for entry in inf.values():
                text = entry.get('tag' if tags_context else 'tag')
                if isinstance(text, str):
                    tags.append(normalize(text))

    return {'str': strings, 'tag': tags}


def compute_idf(docs: Dict[str, List[str]]) -> Dict[str, float]:
    """Compute smoothed IDF scores for tokens."""
    df = Counter()
    N = len(docs)
    for toks in docs.values():
        for t in set(toks):
            df[t] += 1
    return {t: math.log((N + 1) / (cnt + 1)) + 1 for t, cnt in df.items()}


def select_until(tokens: List[str], idf: Dict[str, float], budget: int) -> List[str]:
    """Select highest-IDF tokens until budget (in tokenized length)."""
    picked, used = [], 0
    for tok in sorted(tokens, key=lambda x: idf.get(x, 0), reverse=True):
        length = len(tokenizer.tokenize(tok))
        if used + length > budget:
            continue
        picked.append(tok)
        used += length
        if used >= budget:
            break
    return picked