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
import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
from typing import List, Dict, Any
import textwrap

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
    sum_p1 = sum_h2 = sum_h5 = sum_mrr = sum_rank = 0.0
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
            start_ns = time.perf_counter_ns()
            out = search_prompt(cid, prompt, use_tags=opts.get('use_tags', True))
            elapsed_ns = time.perf_counter_ns() - start_ns
            total_search_time_ns += elapsed_ns

            cands = out['results']['candidates']
            oid_list = [c['oid'] for c in cands]
            rank = oid_list.index(gold_oid) + 1

            batch_res.append({'component': comp, 'rank': rank, 'gold': gold_oid})

            sum_p1  += (rank == 1)
            sum_h2  += (rank <= 2)
            sum_h5  += (rank <= 5)
            sum_mrr += (1.0 / rank)
            sum_rank += rank
            total_queries += 1

            ranks_map[comp] = rank

        if batch_res:
            n = len(batch_res)
            per_collection[colname] = {
                'metrics': {
                    'P@1':   sum(1 for r in batch_res if r['rank']==1) / n,
                    'Hit@2': sum(1 for r in batch_res if r['rank']<=2) / n,
                    'Hit@5': sum(1 for r in batch_res if r['rank']<=5) / n,
                    'MRR':   sum((1.0/r['rank']) for r in batch_res) / n,
                    'mean':  sum(r['rank'] for r in batch_res) / n
                },
                'ranks_by_prompt': ranks_map
            }

    if total_queries == 0:
        print("No prompts tested.")
        return {'error': 'No prompts tested.'}

    global_metrics = {
        'P@1':   sum_p1  / total_queries,
        'Hit@2': sum_h2  / total_queries,
        'Hit@5': sum_h5  / total_queries,
        'MRR':   sum_mrr / total_queries,
        'Mean':  sum_rank / total_queries
    }

    avg_retrieval_time_ms = (total_search_time_ns / total_queries) / 1_000_000.0
    avg_retrieval_time_ms_str = f"{avg_retrieval_time_ms:.3f}"

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
        bm25_construction_time = None  # in seconds

        if BM25Okapi and corpus:
            try:
                start = time.perf_counter()
                bm25 = BM25Okapi(corpus)
                end = time.perf_counter()
                bm25_construction_time = end - start
                print(f"{api.get_colname_from_oid(cid)} BM25 index construction took {bm25_construction_time:.4f} seconds")
            except Exception as e:
                bm25 = None
                print(f"BM25 index construction failed: {e}")

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

                # look up the gold_oid’s score and skip if zero or negative
                try:
                    gold_idx = exe_oids.index(gold_oid)
                except ValueError:
                    continue
                if scores_tok[gold_idx] <= 0:
                    continue

                ranked_tok = sorted(zip(exe_oids, scores_tok),key=lambda x: x[1],reverse=True)
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
    results['FUSE-S'] = fuse_batch(args, opts)
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
    systems = ['BM25', 'BM25-UB', 'FUSE-S', 'FUSE']

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

    plt.xlabel("Rank of Correct Result", fontsize=18)
    plt.ylabel("Cumulative % of Queries Resolved", fontsize=18)
    plt.grid(True, linestyle="--", linewidth=0.5)
    plt.legend(fontsize=18)
    plt.xticks(fontsize=18)
    plt.yticks(fontsize=18)
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
    results = {}
    cids, _ = api.valid_oids(args)
    for cid in cids:
        c_results = {}
        use_tags = opts.get("use_tags", True)

        oids = api.expand_oids(cid)
        exes = filter_executables(oids)

        total_data_cpu_hours = 0.0
        total_data_gpu_hours = 0.0

        # Build a list of (exe, num_functions)
        exe_counts = []
        for exe in exes:
            funcs = api.get_field("ghidra_disasm", exe, "functions") or []
            exe_counts.append((exe, len(funcs)))

        # Sort by num_functions (ascending)
        exe_counts.sort(key=lambda pair: pair[1])

        total_data_cpu_hours = 0.0
        total_data_gpu_hours = 0.0

        count = 1

        # Tag in order from fewest to most functions
        for exe, func_count in exe_counts:
            print(f"{count} of {len(exe_counts)}")
            # --- CPU + GPU: Data extraction (strings + tagging) ---
            t0 = time.time()
            gpu_time_sec = api.get_field("tag_all_functions", exe, "total_gpu_time_sec")
            t1 = time.time()

            wall_time_sec = t1 - t0
            data_gpu = gpu_time_sec / 3600.0
            cpu_time_sec = max(0.0, wall_time_sec - gpu_time_sec)
            data_cpu = cpu_time_sec / 3600.0

            total_data_cpu_hours += data_cpu
            total_data_gpu_hours += data_gpu
            count += 1

def collection_embedding(args, opts):
    results = {}
    cid = api.valid_oids(args)[0]
    use_tags = opts.get("use_tags", True)

    oids = api.expand_oids(cid)
    exes, _ = separate_oids(oids)

    _, total_emb_cpu_sec, total_emb_gpu_sec = build_embedding_matrix(exes, use_tags)

    # Results dictionary
    results = {
        "Embedding CPU-seconds": f"{total_emb_cpu_sec:.2f}",
        "Embedding GPU-seconds": f"{total_emb_gpu_sec:.2f}",
    }

    return results

def experiment_semantic_variants(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:

    comp_path = opts.get("comp_path")
    prompt_path = opts.get("prompt_path")
    if not comp_path or not prompt_path:
        return {"error": "Use 'comp_path' and 'prompt_path' to specify JSON files."}
    if not os.path.isfile(prompt_path) or not prompt_path.endswith('.json'):
        return {"error": "The 'prompt_path' must be a .json file ending in .json."}

    try:
        with open(prompt_path, 'r') as f:
            prompt_map = json.load(f)
    except Exception as e:
        return {"error": f"Failed to load prompt JSON: {e}"}

    ground_truth = create_ground_truth(comp_path)
    use_tags = opts.get('use_tags', True)

    # 1) initialize nested dict: component → prompt → list of ranks
    raw_ranks_fuse: Dict[str, Dict[str, List[int]]] = {
        comp: {prompt: [] for prompt in prompts}
        for comp, prompts in prompt_map.items()
    }

    # 2) collect raw ranks
    for component, comp_prompts in prompt_map.items():
        for cid, oid_map in ground_truth.items():
            gold_oid = oid_map.get(component)
            if not gold_oid:
                continue

            for prompt in comp_prompts:
                out_fuse = search_prompt(cid, prompt, use_tags=use_tags)
                cands = out_fuse.get("results", {}).get("candidates", [])
                oid_list = [c.get("oid") for c in cands]
                if gold_oid in oid_list:
                    rank = oid_list.index(gold_oid) + 1
                else:
                    rank = len(oid_list) + 1
                raw_ranks_fuse[component][prompt].append(rank)

    # 3) get BM25-UB results once (dict: prompt → metrics)
    bm25_raw = experiment_bm25_ub(comp_path, prompt_path)

    # 4) for each component, build its own table + plot
    tables_by_component: Dict[str, pd.DataFrame] = {}
    for component, prompt_dict in raw_ranks_fuse.items():
        prompts = list(prompt_dict.keys())
        aliases = {f"P{idx}": p for idx, p in enumerate(prompts)}

        # compute FUSE metrics per alias
        fuse_metrics: Dict[str, Dict[str, float]] = {}
        for alias, prompt in aliases.items():
            arr = np.array(prompt_dict[prompt], dtype=float)
            fuse_metrics[alias] = {
                "FUSE_P@1": float((arr == 1).mean()),
                "FUSE_Hit@2": float((arr <= 2).mean()),
                "FUSE_Hit@5": float((arr <= 5).mean()),
                "FUSE_MRR": float((1.0 / arr).mean()),
            }

        # pull BM25 metrics into same alias space
        bm25_metrics = {
            alias: bm25_raw.get(prompt, {})
            for alias, prompt in aliases.items()
        }

        # merge into DataFrame
        rows = []
        for alias, prompt in aliases.items():
            row = {"Prompt": prompt, "Alias": alias}
            row.update(fuse_metrics[alias])
            bm = bm25_metrics.get(alias, {})
            row.update({
                "BM25_P@1": bm.get("P@1", 0.0),
                "BM25_Hit@2": bm.get("Hit@2", 0.0),
                "BM25_Hit@5": bm.get("Hit@5", 0.0),
                "BM25_MRR": bm.get("MRR", 0.0),
            })
            rows.append(row)

        df = pd.DataFrame(rows).set_index("Prompt")
        tables_by_component[component] = df

        csv_path = f"{component}_metrics.csv"
        df.to_csv(csv_path, index=True)
        print(f"Saved metrics table to {csv_path}")

        metric = 'P@1'
        fuse_col  = f'FUSE_{metric}'
        bm25_col  = f'BM25_{metric}'
        xlabel    = metric

        # prepare y labels (wrap long prompts so they fit)
        wrapped = [ textwrap.fill(p, width=40) for p in df.index ]

        # positions
        y = np.arange(len(df))
        height = 0.4

        fig, ax = plt.subplots(figsize=(10, max(6, len(df)*0.5)))
        ax.barh(y - height/2, df[bm25_col], height, label='BM25-UB', color='tab:orange')
        ax.barh(y + height/2, df[fuse_col],  height, label='FUSE',    color='tab:gray')

        ax.set_yticks(y)
        ax.set_yticklabels(wrapped, fontsize=10)
        ax.invert_yaxis()            # highest prompt on top
        ax.set_xlabel(xlabel, fontsize=12)
        ax.set_title(f"{component} {xlabel} Comparison", fontsize=14)
        ax.legend(loc='lower right')

        plt.tight_layout()
        plt.savefig(f"{component}_{metric.replace('@','')}_comparison.pdf")
        plt.close()

    # 5) return all per-component tables
    return {
        'tables': tables_by_component,
    }

def search_semantic_variants(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    cid = args[0]
    gold_oid = args[1]

    prompt_path = opts.get("prompt_path")
    if not prompt_path:
        return {"error": "Use 'comp_path' and 'prompt_path' to specify both JSON files."}

    if not os.path.isfile(prompt_path) or not prompt_path.endswith('.json'):
        return {"error": "The 'prompt_path' must be an existing .json file."}

    # load prompts → component mapping
    try:
        with open(prompt_path, 'r') as f:
            prompt_map: Dict[str, List[str]] = json.load(f)
    except Exception as e:
        return {"error": f"Failed to load prompt JSON: {e}"}

    use_tags = opts.get('use_tags', True)

    # 1) collect FUSE raw ranks
    fuse_ranks: Dict[str, Dict[str, int]] = {}
    for component, prompts in prompt_map.items():
        fuse_ranks[component] = {}
        for prompt in prompts:
            out = search_prompt(cid, prompt, use_tags=use_tags)
            cands = out.get("results", {}).get("candidates", [])
            oid_list = [c.get("oid") for c in cands]
            try:
                rank = oid_list.index(gold_oid) + 1
            except ValueError:
                rank = None
            fuse_ranks[component][prompt] = rank

    # 3) collect BM25-UB raw ranks via the helper
    bm25_ranks: Dict[str, Dict[str, int]] = {}
    for component, prompts in prompt_map.items():
        bm25_ranks[component] = get_bm25_ub_raw_ranks(cid, prompts, gold_oid)

    # 4) return both sets of ranks
    return {
        "fuse_ranks": fuse_ranks,
        "bm25_ranks": bm25_ranks,
    }



exports = [fuse, fuse_batch, baseline_fuse_bm25, baseline_fuse_bm25_best, run_all, effort_analysis, component_analysis, measure_search_latency, process_collection, collection_embedding, experiment_semantic_variants, search_semantic_variants]

# -------------------------------------------------------------
# Embedding & Search
# -------------------------------------------------------------

def build_embedding_matrix(oids: List[str], use_tags: bool = True) -> Tuple[np.ndarray, float, float]:
    """
    Generate fused embedding matrix and IDF maps for oids.
    Returns: (embedding matrix, cpu_hours, gpu_hours)
    """
    t_cpu_start = time.time()

    tokens_map = {oid: extract_tokens(oid, use_tags) for oid in oids}
    str_idf = compute_idf({k: v['str'] for k, v in tokens_map.items()})
    tag_idf = compute_idf({k: v['tag'] for k, v in tokens_map.items()}) if use_tags else {}

    t_cpu_end = time.time()  # all preprocessing up to this point is CPU
    cpu_time = t_cpu_end - t_cpu_start

    vectors = []
    gpu_time = 0.0
    eps = 1e-8

    for oid in oids:
        # Prepare string embedding
        strs = select_until(tokens_map[oid]['str'], str_idf, MAX_TOKENS)
        str_doc = ' '.join(strs)

        # GPU: encode string embedding
        t0 = time.time()
        str_emb = model.encode(str_doc, normalize_embeddings=True)
        t1 = time.time()
        gpu_time += (t1 - t0)

        if use_tags:
            tags = select_until(tokens_map[oid]['tag'], tag_idf, MAX_TOKENS)
            tag_doc = ' '.join(tags)

            t0 = time.time()
            tag_emb = model.encode(tag_doc, normalize_embeddings=True)
            t1 = time.time()
            gpu_time += (t1 - t0)

            n_s = len(tokenizer.tokenize(str_doc))
            n_t = len(tokenizer.tokenize(tag_doc))
            alpha = n_t / (n_s + n_t + eps)
            vec = (1 - alpha) * str_emb + alpha * tag_emb
        else:
            vec = str_emb

        vectors.append(vec / (np.linalg.norm(vec) + eps))

    total_cpu_sec = cpu_time
    total_gpu_sec = gpu_time

    return np.vstack(vectors).astype('float32'), total_cpu_sec, total_gpu_sec


def search_prompt(cid: str, prompt: str, use_tags: bool = True) -> Dict[str, Any]:
    """Search a prompt over given OIDs, returning all ranked matches."""
    exes = filter_executables(api.expand_oids(cid))

    # Retrieve/Generate Embedding Matrix
    if api.local_exists(NAME, f"{cid}_{use_tags}"):
        emb_mat = api.local_retrieve(NAME, f"{cid}_{use_tags}")[cid]
    else:
        emb_mat, _, _ = build_embedding_matrix(exes, use_tags)
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

# def extract_tokens(oid: str, use_tags: bool = True) -> Dict[str, List[str]]:
#     """Extract and normalize strings and tags for an OID."""
#     raw_strs = api.get_field('strings', oid, oid) or {}
#     strings = [s.lower() for s in raw_strs.values()
#                if ALNUM.search(s) and len(s) < 60]

#     tags: List[str] = []
#     if use_tags:
#         inf = api.get_field('tag_all_functions', oid, 'func_tags') or {}
#         if inf != 'FAILED':
#             for entry in inf.values():
#                 if isinstance(entry, str):
#                     tags.append(normalize(entry))

#     return {'str': strings, 'tag': tags}


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

def experiment_bm25_ub(comp_path: str, prompt_path: str) -> Dict[str, Dict[str, float]]:
    """
    Run the BM25-UB (upper-bound) variant experiment for all components in the prompt JSON.
    Returns a mapping from prompt to its metrics: { 'P@1', 'Hit@2', 'Hit@5', 'MRR', 'Mean' }.
    """
    # 1) Load prompts and ground-truth
    with open(prompt_path, 'r') as f:
        prompt_map: Dict[str, List[str]] = json.load(f)
    ground_truth = create_ground_truth(comp_path)

    # 2) Flatten all prompts and initialize raw ranks
    all_prompts = [p for comp_prompts in prompt_map.values() for p in comp_prompts]
    raw_ranks: Dict[str, List[int]] = {p: [] for p in all_prompts}

    # 3) For each collection ID, build BM25 index once and score all component prompts
    for cid, oid_map in ground_truth.items():
        # Build corpus: a list of token lists, one per component in this collection
        exe_oids: List[str] = []
        corpus: List[List[str]] = []
        oids = []
        for comp, oid in oid_map.items():
            toks = list(api.get_field("strings", oid, oid).values() or [])
            oids.append(oid)
            if not toks:
                continue
            corpus.append(toks)
        exe_oids = filter_executables(oids)

        if not corpus:
            continue

        bm25 = BM25Okapi(corpus)

        # Score each component's prompts
        for component, comp_prompts in prompt_map.items():
            gold_oid = oid_map.get(component)
            if gold_oid is None:
                continue

            for prompt in comp_prompts:
                q_tokens = prompt.split()
                # full-query scoring
                full_scores = bm25.get_scores(q_tokens)
                ranked_full = sorted(zip(exe_oids, full_scores), key=lambda x: x[1], reverse=True)
                ranked_oids_full = [oid for oid, _ in ranked_full]
                try:
                    best_rank = ranked_oids_full.index(gold_oid) + 1
                except ValueError:
                    best_rank = None

                # token-level upper-bound scoring
                for tok in set(q_tokens):
                    tok_scores = bm25.get_scores([tok])

                    try:
                        gold_idx = exe_oids.index(gold_oid)
                    except ValueError:
                        continue  # gold_oid not in this list for some reason

                    gold_score = tok_scores[gold_idx]
                    if gold_score <= 0:
                        # skip tokens that give the gold binary zero score
                        continue

                    ranked_tok = sorted(
                        zip(exe_oids, tok_scores), key=lambda x: x[1], reverse=True
                    )
                    ranked_oids_tok = [oid for oid, _ in ranked_tok]
                    try:
                        r = ranked_oids_tok.index(gold_oid) + 1
                        if best_rank is None or r < best_rank:
                            best_rank = r
                    except ValueError:
                        pass

                rank = best_rank if best_rank is not None else (len(exe_oids) + 1)
                raw_ranks[prompt].append(rank)

    # 4) Compute metrics per prompt
    metrics: Dict[str, Dict[str, float]] = {}
    for prompt, ranks in raw_ranks.items():
        arr = np.array(ranks, dtype=float)
        metrics[prompt] = {
            'P@1':   float((arr == 1).mean()),
            'Hit@2': float((arr <= 2).mean()),
            'Hit@5': float((arr <= 5).mean()),
            'MRR':   float((1.0 / arr).mean()),
            'Mean':  float(arr.mean())
        }
    return metrics

def get_bm25_ub_raw_ranks(cid: str, prompts: List[str], gold_oid: str) -> Dict[str, int]:
    """
    For collection `cid`, build a BM25-UB index over all executables
    and return the raw best rank of `gold_oid` for each prompt.
    Ranks are 1-based; if `gold_oid` never appears, returns len(executables)+1.
    """
    # 1) get and filter the list of OIDs
    all_oids = api.expand_oids(cid)
    exe_oids = filter_executables(all_oids)

    # 2) build the BM25 corpus in lockstep with exe_oids
    corpus: List[List[str]] = []
    for oid in exe_oids:
        toks = list(api.get_field("strings", oid, oid).values() or [])
        if toks:
            corpus.append(toks)
    print(len(corpus))

    if not corpus:
        return {prompt: None for prompt in prompts}

    bm25 = BM25Okapi(corpus)
    max_rank = len(exe_oids) + 1

    # 3) score each prompt
    ranks: Dict[str, int] = {}
    for prompt in prompts:
        best = None

        # full-query
        scores = bm25.get_scores(prompt.split())
        ranked = sorted(zip(exe_oids, scores), key=lambda x: x[1], reverse=True)
        order = [oid for oid, _ in ranked]
        if gold_oid in order:
            best = order.index(gold_oid) + 1
            print(best)

        # token-level upper bound
        for tok in set(prompt.split()):
            tok_scores = bm25.get_scores([tok])

            try:
                gold_idx = exe_oids.index(gold_oid)
            except ValueError:
                continue  # gold_oid not in this list for some reason

            gold_score = tok_scores[gold_idx]
            if gold_score <= 0:
                # skip tokens that give the gold binary zero score
                continue

            ranked_tok = sorted(zip(exe_oids, tok_scores), key=lambda x: x[1], reverse=True)
            order_tok = [oid for oid, _ in ranked_tok]
            if gold_oid in order_tok:
                r = order_tok.index(gold_oid) + 1
                if best is None or r < best:
                    best = r

        ranks[prompt] = best if best is not None else max_rank

    return ranks