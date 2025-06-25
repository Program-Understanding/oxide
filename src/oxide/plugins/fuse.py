import json
import math
import re
import logging
from collections import Counter
from typing import List, Dict, Tuple, Optional, Any
import os
from pathlib import Path

try:
    from rank_bm25 import BM25Okapi
except ImportError:
    BM25Okapi = None


import numpy as np
from sentence_transformers import SentenceTransformer
from transformers import AutoTokenizer

from oxide.core import api
# -------------------------------------------------------------
# Configuration & Setup
# -------------------------------------------------------------
MODEL_ID = "sentence-transformers/all-MiniLM-L6-v2"
tokenizer = AutoTokenizer.from_pretrained(MODEL_ID)
model = SentenceTransformer(MODEL_ID)
MAX_TOKENS = tokenizer.model_max_length
ALNUM = re.compile(r"[A-Za-z]{3,}")

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

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

    oids = filter_executables(api.expand_oids(api.valid_oids(args)[0]))
    return search_prompt(oids, prompt, use_tags=opts.get('use_tags', True))

def fuse_batch(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """Run batch NL search across collections, returning per-collection and global metrics plus per-prompt ranks."""
    comp_path = opts.get('comp_path')
    prompt_path = opts.get('prompt_path')
    if not comp_path or not prompt_path:
        print("Error: 'comp_path' or 'prompt_path' not provided.")
        return {'error': "Use 'comp_path' and 'prompt_path' to specify JSON file or directory."}

    comp_map = create_ground_truth(comp_path)

    results: Dict[str, Any] = {}

    # Collect prompt files
    if os.path.isdir(prompt_path):
        prompt_files = [os.path.join(prompt_path, f)
                        for f in os.listdir(prompt_path)
                        if f.endswith(".json")]
    else:
        prompt_files = [prompt_path]

    for prompt_file in prompt_files:
        print(f"\nProcessing prompt file: {prompt_file}")
        try:
            prompt_map = json.load(open(prompt_file))
        except Exception as e:
            print(f"  Failed to load prompt JSON: {e}")
            results[os.path.basename(prompt_file)] = {'error': str(e)}
            continue

        per_collection: Dict[str, Any] = {}
        total, sum_p1, sum_h2, sum_h5, sum_mrr = 0, 0.0, 0.0, 0.0, 0.0

        for cid, golds in comp_map.items():
            colname = api.get_colname_from_oid(cid)
            print(f"  Processing collection '{colname}' (CID: {cid})...")
            oids, _ = api.valid_oids([cid])
            exes = filter_executables(api.expand_oids(oids))

            batch_res: List[Dict[str, Any]] = []
            ranks_map: Dict[str, Optional[int]] = {}

            for idx, (comp, gold_oid) in enumerate(golds.items()):
                prompt = prompt_map.get(comp)
                if prompt is None:
                    print(f"    Skipping missing prompt for component: {comp}")
                    continue

                print(f"    Prompt {idx+1}/{len(golds)}: '{prompt[:50]}{'...' if len(prompt) > 50 else ''}'")
                out = search_prompt(exes, prompt, use_tags=opts.get('use_tags', True))
                cands = out['results']['candidates']
                oid_list = [c['oid'] for c in cands]

                try:
                    rank = oid_list.index(gold_oid) + 1
                except ValueError:
                    rank = None

                # Record component name and its rank
                batch_result = {
                    'component': comp,
                    'rank': rank,
                    'gold': gold_oid
                }
                batch_res.append(batch_result)

                # Accumulate global metrics
                sum_p1 += int(rank == 1)
                sum_h2 += int(rank and rank <= 2)
                sum_h5 += int(rank and rank <= 5)
                sum_mrr += (1.0 / rank) if rank else 0.0
                total += 1

                # Store per-prompt rank
                ranks_map[comp] = rank

            if batch_res:
                n = len(batch_res)
                metrics = {
                    'P@1':   sum(int(r['rank'] == 1) for r in batch_res) / n,
                    'Hit@2': sum(int(r['rank'] and r['rank'] <= 2) for r in batch_res) / n,
                    'Hit@5': sum(int(r['rank'] and r['rank'] <= 5) for r in batch_res) / n,
                    'MRR':   sum((1.0 / r['rank']) for r in batch_res if r['rank']) / n
                }

                per_collection[colname] = {
                    'batch': batch_res,
                    'metrics': metrics,
                    'ranks_by_prompt': ranks_map
                }
                print(f"  Finished '{colname}'. Metrics: "
                      f"P@1={metrics['P@1']:.3f}, Hit@2={metrics['Hit@2']:.3f}, "
                      f"Hit@5={metrics['Hit@5']:.3f}, MRR={metrics['MRR']:.3f}")

        if total == 0:
            print("  No prompts tested for this file.")
            results[os.path.basename(prompt_file)] = {'error': 'No prompts tested.'}
        else:
            global_metrics = {
                'P@1':   sum_p1 / total,
                'Hit@2': sum_h2 / total,
                'Hit@5': sum_h5 / total,
                'MRR':   sum_mrr / total
            }
            print(f"Global metrics for {os.path.basename(prompt_file)}: "
                  f"P@1={global_metrics['P@1']:.3f}, Hit@2={global_metrics['Hit@2']:.3f}, "
                  f"Hit@5={global_metrics['Hit@5']:.3f}, MRR={global_metrics['MRR']:.3f}")

            results[os.path.basename(prompt_file)] = {
                'per_collection': per_collection,
                'global_metrics': global_metrics
            }

    return results

def fuse_batch_dual(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Run FUSE twice (with tags and without) across a single prompt JSON, returning:
      - per_collection[collection][variant]['batch']        : List[{'component', 'rank', 'gold'}]
      - per_collection[collection][variant]['metrics']      : {'P@1','Hit@2','Hit@5','MRR'}
      - per_collection[collection][variant]['ranks_by_prompt']: {component:rank}
      - global_metrics[variant]                             : same four metrics over all queries
    Variants: 'full' (use_tags=True) and 'no_tags' (use_tags=False).
    """
    comp_path   = opts.get('comp_path')
    prompt_path = opts.get('prompt_path')
    if not comp_path or not prompt_path:
        return {'error': "Use 'comp_path' and 'prompt_path' to specify JSON file paths."}

    if not os.path.isfile(prompt_path) or not prompt_path.endswith('.json'):
        return {'error': "The 'prompt_path' must be a .json file, not a directory or other file type."}

    comp_map = create_ground_truth(comp_path)

    # load the prompt mapping from the JSON file
    try:
        with open(prompt_path) as f:
            prompt_map = json.load(f)
    except Exception as e:
        return {'error': f"Failed to load prompt JSON: {e}"}

    # define the two variants
    variants = {
        'full':    {'use_tags': True},
        'no_tags': {'use_tags': False}
    }

    # initialize accumulators
    global_acc = {
        v: {'total': 0, 'sum_p1': 0, 'sum_h2': 0, 'sum_h5': 0, 'sum_mrr': 0.0}
        for v in variants
    }
    per_collection: Dict[str, Any] = {}

    # iterate through collections
    for cid, golds in comp_map.items():
        colname = api.get_colname_from_oid(cid)
        oids, _ = api.valid_oids([cid])
        exes = filter_executables(api.expand_oids(oids))

        per_collection[colname] = {}
        for vname, vopts in variants.items():
            batch_res: List[Dict[str,Any]] = []
            ranks_map: Dict[str, Optional[int]] = {}
            acc = global_acc[vname]

            for comp, gold_oid in golds.items():
                prompt = prompt_map.get(comp)
                if prompt is None:
                    continue

                out = search_prompt(exes, prompt, use_tags=vopts['use_tags'])
                oid_list = [c['oid'] for c in out['results']['candidates']]

                try:
                    rank = oid_list.index(gold_oid) + 1
                except ValueError:
                    rank = None

                batch_res.append({'component': comp, 'rank': rank, 'gold': gold_oid})
                ranks_map[comp] = rank

                # update global accumulators
                acc['total']  += 1
                acc['sum_p1'] += int(rank == 1)
                acc['sum_h2'] += int(rank is not None and rank <= 2)
                acc['sum_h5'] += int(rank is not None and rank <= 5)
                acc['sum_mrr']+= (1.0/rank) if rank else 0.0

            # compute metrics for this collection & variant
            n = len(batch_res)
            metrics = {}
            if n > 0:
                metrics = {
                    'P@1':   sum(1 for r in batch_res if r['rank']==1) / n,
                    'Hit@2': sum(1 for r in batch_res if r['rank'] and r['rank']<=2) / n,
                    'Hit@5': sum(1 for r in batch_res if r['rank'] and r['rank']<=5) / n,
                    'MRR':   sum((1.0/r['rank']) for r in batch_res if r['rank']) / n
                }

            per_collection[colname][vname] = {
                'batch': batch_res,
                'metrics': metrics,
                'ranks_by_prompt': ranks_map
            }

    # compute global metrics
    global_metrics = {}
    for vname, acc in global_acc.items():
        T = acc['total'] or 1
        global_metrics[vname] = {
            'P@1':   acc['sum_p1'] / T,
            'Hit@2': acc['sum_h2'] / T,
            'Hit@5': acc['sum_h5'] / T,
            'MRR':   acc['sum_mrr'] / T
        }

    return {'per_collection': per_collection, 'global_metrics': global_metrics}


def baseline_fuse_bm25(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Run batch search using BM25 ranking over the set of strings in each executable,
    for a single prompt JSON file.
    """
    comp_path = opts.get("comp_path")
    prompt_path = opts.get("prompt_path")
    if not comp_path or not prompt_path:
        print("Error: 'comp_path' or 'prompt_path' not provided.")
        return {"error": "Use 'comp_path' and 'prompt_path' to specify JSON files."}

    comp_map = create_ground_truth(comp_path)

    # Load prompt map from single JSON file
    try:
        prompt_map = json.load(open(prompt_path))
    except Exception as e:
        print(f"Failed to load prompt JSON: {e}")
        return {"error": f"Failed to load prompt JSON: {e}"}

    comp_details: Dict[str, Any] = {}
    total_prompts = 0
    sum_p1 = sum_h2 = sum_h5 = sum_mrr = 0.0

    for cid, oid_map in comp_map.items():
        colname = api.get_colname_from_oid(cid)
        print(f"  Collection '{colname}' (CID: {cid})")

        # Expand and filter executables
        oids, _ = api.valid_oids([cid])
        exes = filter_executables(api.expand_oids(oids))

        # Build a per-collection corpus
        exe_oids: List[str] = []
        corpus: List[List[str]] = []
        for comp_name, exe_oid in oid_map.items():
            if exe_oid in exes:
                strings = api.get_field("strings", exe_oid, exe_oid) or {}
                tokens = list(strings.values())
                if tokens:
                    exe_oids.append(exe_oid)
                    corpus.append(tokens)

        # Initialize BM25 for this collection
        bm25 = None
        if BM25Okapi and corpus:
            try:
                bm25 = BM25Okapi(corpus)
            except Exception:
                print("    Warning: BM25 init failed; falling back to overlap.")
        elif BM25Okapi:
            print("    Warning: empty corpus; falling back to overlap.")

        # Evaluate each component prompt within this collection
        for comp_name, gold_oid in oid_map.items():
            prompt = prompt_map.get(comp_name)
            if not prompt:
                print(f"    Skipping missing prompt for: {comp_name}")
                continue

            query_tokens = prompt.split()
            scores = bm25.get_scores(query_tokens)
            ranked = sorted(zip(exe_oids, scores), key=lambda x: x[1], reverse=True)
            ranked_oids = [oid for oid, _ in ranked]

            try:
                rank = ranked_oids.index(gold_oid) + 1
            except ValueError:
                rank = None

            sum_p1 += int(rank == 1)
            sum_h2 += int(rank and rank <= 2)
            sum_h5 += int(rank and rank <= 5)
            sum_mrr += (1.0 / rank) if rank else 0.0
            total_prompts += 1

            # Drill-down: string-match counts, example hits & prompt
            top_oids = ranked_oids[:5]
            match_counts: Dict[str, int] = {}
            example_hits: Dict[str, Dict[str, List[str]]] = {}
            for oid in top_oids:
                strings_map = api.get_field("strings", oid, oid) or {}
                all_strs = list(strings_map.values())
                cnt = sum(1 for t in set(query_tokens) if any(t in s for s in all_strs))
                match_counts[oid] = cnt
                token_hits = {
                    t: [s for s in all_strs if t in s][:5]
                    for t in set(query_tokens)
                    if any(t in s for s in all_strs)
                }
                example_hits[oid] = token_hits

            comp_details[comp_name] = {
                'prompt': prompt,
                'rank': rank,
                'match_count_top5': match_counts,
                'example_hits': example_hits
            }

    if total_prompts == 0:
        print("  No prompts tested.")
        return {'error': 'No prompts tested.'}

    metrics = {
        "P@1":  sum_p1 / total_prompts,
        "Hit@2": sum_h2 / total_prompts,
        "Hit@5": sum_h5 / total_prompts,
        "MRR":   sum_mrr / total_prompts
    }
    print(
        f"  Metrics: P@1={metrics['P@1']:.3f}, Hit@2={metrics['Hit@2']:.3f}, "
        f"Hit@5={metrics['Hit@5']:.3f}, MRR={metrics['MRR']:.3f}"
    )

    return {
        'global_metrics': metrics,
        'details': comp_details
    }


def baseline_fuse_bm25_best(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    BM25 baseline testing full prompt and individual tokens,
    for a single prompt JSON file.
    """
    comp_path = opts.get("comp_path")
    prompt_path = opts.get("prompt_path")
    if not comp_path or not prompt_path:
        print("Error: 'comp_path' or 'prompt_path' not provided.")
        return {"error": "Use 'comp_path' and 'prompt_path' to specify JSON files."}

    comp_map = create_ground_truth(comp_path)

    try:
        prompt_map = json.load(open(prompt_path))
    except Exception as e:
        print(f"Failed to load prompt JSON: {e}")
        return {"error": f"Failed to load prompt JSON: {e}"}

    comp_details: Dict[str, Any] = {}
    total_prompts = 0
    sum_p1 = sum_h2 = sum_h5 = sum_mrr = 0.0

    for cid, oid_map in comp_map.items():
        colname = api.get_colname_from_oid(cid)
        print(f"  Collection '{colname}' (CID: {cid})")

        oids, _ = api.valid_oids([cid])
        exes = filter_executables(api.expand_oids(oids))

        exe_oids: List[str] = []
        corpus: List[List[str]] = []
        for _comp, exe_oid in oid_map.items():
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
                print("    Warning: BM25 init failed; falling back to overlap.")
        elif BM25Okapi:
            print("    Warning: empty corpus; falling back to overlap.")

        for comp_name, gold_oid in oid_map.items():
            prompt = prompt_map.get(comp_name)
            if not prompt:
                print(comp_name)
                
                print(prompt_map)
                input()
                print(f"    Skipping missing prompt for: {comp_name}")
                continue

            query_tokens = prompt.split()
            best_rank = None
            best_variant = "full_prompt"
            all_ranked_lists: Dict[str, List[str]] = {}

            # full prompt
            scores_full = bm25.get_scores(query_tokens)
            rank_full, ranked_full = _rank(gold_oid, exe_oids, scores_full)
            all_ranked_lists['full_prompt'] = ranked_full[:5]
            best_rank = rank_full

            # each token
            for tok in set(query_tokens):
                scores_tok = bm25.get_scores([tok])
                rank_tok, ranked_tok = _rank(gold_oid, exe_oids, scores_tok)
                all_ranked_lists[tok] = ranked_tok[:5]
                if rank_tok and (best_rank is None or rank_tok < best_rank):
                    best_rank = rank_tok
                    best_variant = tok

            sum_p1 += int(best_rank == 1)
            sum_h2 += int(best_rank and best_rank <= 2)
            sum_h5 += int(best_rank and best_rank <= 5)
            sum_mrr += (1.0 / best_rank) if best_rank else 0.0
            total_prompts += 1

            comp_details[comp_name] = {
                'prompt': prompt,
                'best_rank': best_rank,
                'best_variant': best_variant,
                'rank_lists': all_ranked_lists
            }

    if total_prompts == 0:
        print("  No prompts tested.")
        return {'error': 'No prompts tested.'}

    metrics = {
        "P@1":  sum_p1 / total_prompts,
        "Hit@2": sum_h2 / total_prompts,
        "Hit@5": sum_h5 / total_prompts,
        "MRR":   sum_mrr / total_prompts
    }
    print(
        f"  Metrics: P@1={metrics['P@1']:.3f}, Hit@2={metrics['Hit@2']:.3f}, Hit@5={metrics['Hit@5']:.3f}, MRR={metrics['MRR']:.3f}"
    )

    return {
        'global_metrics': metrics,
        'details': comp_details
    }


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

exports = [fuse, fuse_batch, fuse_batch_dual, baseline_fuse_bm25, baseline_fuse_bm25_best, create_ground_truth]

# -------------------------------------------------------------
# Embedding & Search
# -------------------------------------------------------------

def build_embedding_matrix(
    oids: List[str], use_tags: bool = True
) -> Tuple[np.ndarray, Dict[str, float], Dict[str, float]]:
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

    return np.vstack(vectors).astype('float32'), str_idf, tag_idf


def search_prompt(
    oids: List[str], prompt: str, use_tags: bool = True
) -> Dict[str, Any]:
    """Search a prompt over given OIDs, returning all ranked matches."""
    emb_mat, _, _ = build_embedding_matrix(oids, use_tags)
    q = model.encode(prompt, normalize_embeddings=True).astype('float32')
    sims = emb_mat.dot(q)
    idxs = np.argsort(-sims)  # sort all scores descending

    def fmt(i: int) -> Dict[str, Any]:
        return {'oid': oids[i], 'names': get_names(oids[i]), 'score': float(sims[i])}

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


def extract_tokens(
    oid: str, use_tags: bool = True, tags_context: bool = False
) -> Dict[str, List[str]]:
    """Extract and normalize strings and tags for an OID."""
    raw_strs = api.get_field('strings', oid, oid) or {}
    strings = [s.lower() for s in raw_strs.values()
               if ALNUM.search(s) and len(s) < 60]

    tags: List[str] = []
    if use_tags:
        inf = api.retrieve('tag_all_functions', oid) or {}
        if inf != 'FAILED':
            for entry in inf.values():
                text = entry.get('tag_context' if tags_context else 'tag')
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

def _rank(gold_oid: str, exe_oids: List[str], scores: List[float]) -> Tuple[int | None, List[str]]:
    """Return 1‑based rank of gold_oid and the ranked oid list."""
    ranked = sorted(zip(exe_oids, scores), key=lambda x: x[1], reverse=True)
    ranked_oids = [oid for oid, _ in ranked]
    try:
        return ranked_oids.index(gold_oid) + 1, ranked_oids
    except ValueError:
        return None, ranked_oids