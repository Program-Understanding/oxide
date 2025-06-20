import json
import math
import re
import logging
from collections import Counter
from typing import List, Dict, Tuple, Optional, Any
import os

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
    """Run batch NL search across collections, returning per-collection and global metrics."""
    comp_path = opts.get('comp_path')
    prompt_path = opts.get('prompt_path')
    if not comp_path or not prompt_path:
        print("Error: 'comp_path' or 'prompt_path' not provided.")
        return {'error': "Use 'comp_path' and 'prompt_path' to specify JSON file or directory."}

    print(f"Loading component map from {comp_path}...")
    try:
        comp_map = json.load(open(comp_path))
    except Exception as e:
        print(f"Failed to load component JSON: {e}")
        return {'error': f'Failed to load component JSON: {e}'}

    results = {}

    # Handle directory of prompts
    prompt_files = []
    if os.path.isdir(prompt_path):
        prompt_files = [os.path.join(prompt_path, f) for f in os.listdir(prompt_path) if f.endswith(".json")]
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

            batch_res = []
            for idx, (comp, gold) in enumerate(golds.items()):
                prompt = prompt_map.get(comp)
                if prompt is None:
                    print(f"    Skipping missing prompt for component: {comp}")
                    continue
                print(f"    Prompt {idx+1}/{len(golds)}: '{prompt[:50]}{'...' if len(prompt) > 50 else ''}'")
                out = search_prompt(exes, prompt, use_tags=opts.get('use_tags', True))

                cands = out['results']['candidates']
                ranks = [c['oid'] for c in cands]
                try:
                    rank = ranks.index(gold) + 1
                except ValueError:
                    rank = None
                out.update({'rank': rank, 'gold': {'oid': gold, 'names': get_names(gold)}})
                batch_res.append(out)

                sum_p1 += int(rank == 1)
                sum_h2 += int(rank and rank <= 2)
                sum_h5 += int(rank and rank <= 5)
                sum_mrr += (1.0 / rank) if rank else 0.0
                total += 1

            if batch_res:
                n = len(batch_res)
                metrics = {
                    'P@1':   sum(int(r['rank'] == 1) for r in batch_res)/n,
                    'Hit@2': sum(int(r['rank'] and r['rank'] <= 2) for r in batch_res)/n,
                    'Hit@5': sum(int(r['rank'] and r['rank'] <= 5) for r in batch_res)/n,
                    'MRR':   sum((1.0/r['rank']) for r in batch_res if r['rank'])/n
                }
                per_collection[colname] = {'batch': batch_res, 'metrics': metrics}
                print(f"  Finished '{colname}'. Metrics: P@1={metrics['P@1']:.3f}, Hit@2={metrics['Hit@2']:.3f}, Hit@5={metrics['Hit@5']:.3f}, MRR={metrics['MRR']:.3f}")

        if total == 0:
            print("  No prompts tested for this file.")
            results[os.path.basename(prompt_file)] = {'error': 'No prompts tested.'}
        else:
            global_metrics = {
                'P@1':   sum_p1/total,
                'Hit@2': sum_h2/total,
                'Hit@5': sum_h5/total,
                'MRR':   sum_mrr/total
            }
            print(f"Global metrics for {os.path.basename(prompt_file)}: "
                  f"P@1={global_metrics['P@1']:.3f}, Hit@2={global_metrics['Hit@2']:.3f}, "
                  f"Hit@5={global_metrics['Hit@5']:.3f}, MRR={global_metrics['MRR']:.3f}")
            results[os.path.basename(prompt_file)] = {'global_metrics': global_metrics}

    return results

def baseline_fuse_strings(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Run batch search per collection using string-overlap ranking,
    returning per-file global metrics if prompt_path is a directory.
    """
    comp_path = opts.get("comp_path")
    prompt_path = opts.get("prompt_path")
    if not comp_path or not prompt_path:
        print("Error: 'comp_path' or 'prompt_path' not provided.")
        return {"error": "Use 'comp_path' and 'prompt_path' to specify JSON files."}

    print(f"Loading component map from {comp_path}...")
    try:
        comp_map = json.load(open(comp_path))
    except Exception as e:
        print(f"Failed to load component JSON: {e}")
        return {"error": f"Failed to load component JSON: {e}"}

    results = {}
    prompt_files = []

    # Support both single prompt JSON and directory of prompts
    if os.path.isdir(prompt_path):
        prompt_files = [os.path.join(prompt_path, f) for f in os.listdir(prompt_path) if f.endswith('.json')]
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

        total_prompts = 0
        sum_p1 = sum_h2 = sum_h5 = sum_mrr = 0.0

        for cid, gold_map in comp_map.items():
            colname = api.get_colname_from_oid(cid)
            print(f"  Processing collection '{colname}' (CID: {cid})...")
            oids, _ = api.valid_oids([cid])
            exes = filter_executables(api.expand_oids(oids))

            n_prompts = len(gold_map)
            for idx, (comp, gold_oid) in enumerate(gold_map.items(), start=1):
                prompt = prompt_map.get(comp)
                if not prompt:
                    print(f"    Skipping missing prompt for component: {comp}")
                    continue

                print(f"    Prompt {idx}/{n_prompts}: '{prompt[:50]}{'...' if len(prompt) > 50 else ''}'")
                prompt_tokens = set(prompt.split())

                scores = {}
                for exe_oid in exes:
                    strings = set((api.get_field("strings", exe_oid, exe_oid) or {}).values())
                    scores[exe_oid] = len(prompt_tokens & strings)

                ranked_oids = sorted(scores, key=lambda o: scores[o], reverse=True)

                try:
                    rank = ranked_oids.index(gold_oid) + 1
                except (ValueError, TypeError):
                    rank = None

                sum_p1  += int(rank == 1)
                sum_h2  += int(rank and rank <= 2)
                sum_h5  += int(rank and rank <= 5)
                sum_mrr += (1.0 / rank) if rank else 0.0
                total_prompts += 1

        if total_prompts == 0:
            print("  No prompts tested for this file.")
            results[os.path.basename(prompt_file)] = {'error': 'No prompts tested.'}
        else:
            global_metrics = {
                "P@1":   sum_p1  / total_prompts,
                "Hit@2": sum_h2  / total_prompts,
                "Hit@5": sum_h5  / total_prompts,
                "MRR":   sum_mrr / total_prompts
            }
            print(f"Global metrics for {os.path.basename(prompt_file)}: "
                  f"P@1={global_metrics['P@1']:.3f}, Hit@2={global_metrics['Hit@2']:.3f}, "
                  f"Hit@5={global_metrics['Hit@5']:.3f}, MRR={global_metrics['MRR']:.3f}")
            results[os.path.basename(prompt_file)] = {'global_metrics': global_metrics}

    return results

def baseline_fuse_bm25(args: List[str], opts: Dict[str, Any]) -> Dict[str, Any]:
    """
    Run batch search per collection using BM25 ranking over
    the set of strings in each executable.
    """
    comp_path = opts.get("comp_path")
    prompt_path = opts.get("prompt_path")
    if not comp_path or not prompt_path:
        print("Error: 'comp_path' or 'prompt_path' not provided.")
        return {"error": "Use 'comp_path' and 'prompt_path' to specify JSON files."}

    # Load component → gold OID map
    try:
        comp_map = json.load(open(comp_path))
    except Exception as e:
        print(f"Failed to load component JSON: {e}")
        return {"error": f"Failed to load component JSON: {e}"}

    results: Dict[str, Any] = {}
    # Determine prompt files
    if os.path.isdir(prompt_path):
        prompt_files = [os.path.join(prompt_path, f)
                        for f in os.listdir(prompt_path) if f.endswith(".json")]
    else:
        prompt_files = [prompt_path]

    for prompt_file in prompt_files:
        print(f"\nProcessing prompt file: {prompt_file}")
        try:
            prompt_map = json.load(open(prompt_file))
        except Exception as e:
            results[os.path.basename(prompt_file)] = {'error': str(e)}
            continue

        total_prompts = 0
        sum_p1 = sum_h2 = sum_h5 = sum_mrr = 0.0

        # Iterate over each collection ID
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

        if total_prompts == 0:
            print("  No prompts tested for this file.")
            results[os.path.basename(prompt_file)] = {'error': 'No prompts tested.'}
        else:
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
            results[os.path.basename(prompt_file)] = {'global_metrics': metrics}

    return results

exports = [fuse, fuse_batch, baseline_fuse_strings, baseline_fuse_bm25]

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
