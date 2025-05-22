"""Oxide plugin: semantic‑tag matching utilities.

  • tag_firmware   – fetch and cache tag summaries for executables
  • firmware_exes  – quick inventory of executables + tag status
  • search_component   – match a reference component against a firmware image
  • batch_test     – micro‑benchmark over a fixed test set

  The implementation purposefully stays **simple**: we rely on normalised
  string overlap plus RapidFuzz Levenshtein similarity. No stemming, IDF,
  or trigram logic is used, which keeps runtime fast and accuracy around
  75 % on the current OpenWrt dataset.
"""

from oxide.core import api
from rapidfuzz import fuzz
import re
from typing import List, Tuple, Set, Dict, Optional
from collections import defaultdict
from llm_service import runner
from unicodedata import normalize
import textwrap
import os

import math

NAME = "test_tagging"
DESC = "" 
USG = ""

def tag_firmware(args, opts):
    """Fetch tag summaries, processing *smaller* executables first.

    We sort executables by the number of Ghidra‑discovered functions so that
    quick, interactive runs surface their results earlier in the stream.
    """
    valid, _ = api.valid_oids(args)
    oids = api.expand_oids(valid or api.collection_cids())
    exes, _ = separate_oids(oids)

    # count functions per executable (0 if disassembly missing)
    fn_counts = {
        oid: len(api.get_field("ghidra_disasm", oid, "functions") or [])
        for oid in exes
    }

    for idx, oid in enumerate(sorted(fn_counts, key=fn_counts.get), 1):
        print(f"[{idx}/{len(exes)}] {oid}")
        api.retrieve("tag_influential_functions", oid)  # warm cache; ignore returned value
        api.retrieve("tag_file", oid)

def tag_firmware_all(args, opts):
    """Fetch tag summaries, processing *smaller* executables first.

    We sort executables by the number of Ghidra‑discovered functions so that
    quick, interactive runs surface their results earlier in the stream.
    """
    for collection in api.collection_cids():
        print(api.get_colname_from_oid(collection))
        oids = api.expand_oids(collection)
        exes, _ = separate_oids(oids)

        # count functions per executable (0 if disassembly missing)
        fn_counts = {
            oid: len(api.get_field("ghidra_disasm", oid, "functions") or [])
            for oid in exes
        }

        for idx, oid in enumerate(sorted(fn_counts, key=fn_counts.get), 1):
            print(f"[{idx}/{len(exes)}] {oid}")
            api.retrieve("tag_all_functions", oid)  # warm cache; ignore returned value

        break

# ---------------------------------------------------------------------------
# firmware_exes
# ---------------------------------------------------------------------------

def firmware_exes(args, opts):
    """Return a quick inventory of executables within the given OIDs/collections."""
    valid, _ = api.valid_oids(args)
    oids = api.expand_oids(valid)
    exes, _ = separate_oids(oids)

    report = {}
    for oid in sorted(exes):
        # total_funcs = len(api.get_field("ghidra_disasm", oid, "functions"))
        report[oid] = {
            "names":               get_file_names(oid),
            # "total functions":     total_funcs
        }
    return report

# ---------------------------------------------------------------------------
# search_firmware – Search firmware based of natural language prompt
# ---------------------------------------------------------------------------
def search_firmware(args, opts):
    """
    Search firmware components by matching query tags to function-level tags
    using fuzzy matching for improved recall.
    """
    # 1) Collect firmware executables
    valid, _ = api.valid_oids(args)
    fw_exes, _ = separate_oids(api.expand_oids(valid))

    # 2) Generate query tags
    query = opts.get('prompt') or opts.get('query') or ""
    query_tags = expand_query(query)
    if not query_tags:
        return {"error": "No query tags generated"}

    # 3) Gather component tags per executable
    components: Dict[str, List[str]] = {}
    for oid in fw_exes:
        inf = api.retrieve("tag_all_functions", oid) or {}
        if inf == "FAILED":
            continue
        tags = [normalize_tag(e.get('tag_context', e.get('tag', ''))) for e in inf.values() if isinstance(e, dict)]
        components[oid] = tags
    if not components:
        return {"error": "No tags available in firmware"}

    # 4) Fuzzy-match and score each component
    thresh = opts.get('fuzzy_threshold', 80)
    scored: List[Tuple[str, float]] = []
    for oid, tags in components.items():
        norm_tags = [normalize_tag(t) for t in tags]
        pairs = fuzzy_pairs(query_tags, norm_tags, thresh)
        score = float(len(pairs))
        scored.append((oid, score))

    # 5) Sort results by descending score
    scored.sort(key=lambda x: x[1], reverse=True)
    top5 = scored[:5]

    # 6) Format output
    def fmt(oid, score):
        return {
            "oid": oid,
            "names": get_file_names(oid),
            "score": round(score, 4)
        }

    return {
        "search": {"query_tags": query_tags},
        "results": {
            "best_match": fmt(*top5[0]) if top5 else None,
            "candidates": [fmt(oid, sc) for oid, sc in top5]
        }
    }


# ---------------------------------------------------------------------------
# search_component – Search firmware based of example
# ---------------------------------------------------------------------------

def search_component(args, opts):
    """Match *component_oid* against executables in *firmware_image_collection*.

    JSON result now contains `pairs` in each candidate: list of
    (component_tag, firmware_tag) selected by the matcher.
    """
    valid, _ = api.valid_oids(args)
    if len(valid) < 2:
        raise ValueError("Usage: search_component <component_oid> <firmware_image_collection>")
    component, firmware = valid[:2]

    # reference component tags
    comp_inf = api.retrieve("tag_influential_functions", component) or {} 
    if comp_inf == 'FAILED':
        return None
    comp_norms = [normalise(e["tag"]) for e in comp_inf.values() if isinstance(e, dict) and "tag" in e]

    comp_size  = len(comp_norms)

    # candidate executables
    fw_exes, _ = separate_oids(api.expand_oids(firmware))

    scores: List[Tuple[str,float,dict,List[Tuple[str,str]]]] = []
    for oid in fw_exes:
        inf = api.retrieve("tag_influential_functions", oid) or {}
        if inf == 'FAILED':
            continue
        cand_norms = [normalise(e["tag"]) for e in inf.values() if isinstance(e, dict) and "tag" in e]
        cand_size   = len(cand_norms)

        pairs = fuzzy_pairs(comp_norms, cand_norms)
        inter = len(pairs)

        # Dice coefficient
        dice   = (2 * inter) / (comp_size + cand_size) if (comp_size + cand_size) else 0.0

        # Jaccard coefficient
        union    = comp_size + cand_size - inter
        jaccard  = inter / union if union else 0.0

        brk = {"intersection": inter, "comp_size": comp_size, "cand_size": len(cand_norms), "dice": dice}
        scores.append((oid, dice, brk, pairs))

    scores.sort(key=lambda x: x[1], reverse=True)
    top = scores[:5]
    best_oid = top[0][0] if top else None

    return {
        "component": {"oid": component, "names": get_file_names(component)},
        "results": {
            "best_match": {"oid": best_oid, "names": get_file_names(best_oid) if best_oid else []},
            "candidates": [
                {
                    "oid": oid,
                    "score": sc,
                    "breakdown": brk,
                    "names": get_file_names(oid),
                    "pairs": pairs,        # (component_tag, firmware_tag)
                }
                for oid, sc, brk, pairs in top
            ],
        },
    }

def batch_test(args, opts):
    """Run *search_component* over the fixed test set and report @1 and @5 accuracy.

    * CORRECT – correct component is the top‑ranked candidate.
    * TOP-5 – correct component appears in the **top 5** candidates.
    """
    valid, _ = api.valid_oids(args)
    if not valid:
        raise ValueError("Usage: batch_test <firmware_image_cid>")
    known_firmware = valid[0]
    known_exes, _ = separate_oids(api.expand_oids(known_firmware))
    known_exes_names = get_all_file_names(known_exes)

    unknown_firmware = valid[1]
    unknown_exes, _ = separate_oids((api.expand_oids(unknown_firmware)))
    unknown_exes_names = get_all_file_names(unknown_exes)

    matching_exes = pair_exes(known_exes_names, unknown_exes_names)

    per_file = {
        'CORRECT': {},
        'TOP-5': {},
        'MISS': {}
    }
    top1_good = top1_bad = top5_good = 0

    for match in matching_exes:
        comp = match[0]
        comp_match = match[1]
        res = search_component([comp, unknown_firmware], None)
        size = len(api.get_field("ghidra_disasm", comp, "functions") or [])

        if res is None:
            #TODO Fix this
            continue

        # --- top‑1 check -------------------------------------------------
        top1_hit = res["results"]["best_match"]["oid"] == comp_match

        # --- top‑5 check ------------------------------------------------
        top5_hit = False
        for c in res["results"]["candidates"]:
            if c['oid'] == comp_match:
                top5_hit = True
                continue

        # bookkeeping ----------------------------------------------------
        if top1_hit:
            per_file['CORRECT'][comp] = {
                'Name': get_file_names(comp).pop(),
                '# Functions': size
            }
            top1_good += 1
        elif top5_hit:
            per_file['TOP-5'][comp] = {
                'Name': get_file_names(comp).pop(),
                '# Functions': size
            }
            top1_bad  += 1
            top5_good += 1
        else:
            per_file['MISS'][comp] = {
                'Name': get_file_names(comp).pop(),
                '# Functions': size
            }
            top1_bad += 1

    total = len(matching_exes)
    return {
        "RESULTS":  per_file,
        "CORRECT %": top1_good / total if total else 0.0,
        "TOP-5 %": (top1_good + top5_good) / total if total else 0.0,
    }

exports = [tag_firmware, firmware_exes, search_component, search_firmware, batch_test, tag_firmware_all]

# ---------------------------------------------------------------------------
# Utility helpers
# ---------------------------------------------------------------------------

def separate_oids(oids):
    """Split an iterable of OIDs into executables and non‑executables."""
    exes, non_exes = set(), set()
    for oid in oids:
        cat = api.get_field("categorize", oid, oid)
        (exes if cat == "executable" else non_exes).add(oid)
    return exes, non_exes

def get_file_names(oid):
    """Return *all* file names recorded for an OID (list may be empty)."""
    return list(api.get_names_from_oid(oid))

def get_all_file_names(collection):
    """Return *all* file names recorded for a collection (list may be empty)."""
    result = {}
    for oid in collection:
        result[oid] = list(api.get_names_from_oid(oid))
    return result

def pair_exes(dict1, dict2):
    matches = []

    for key1, list1 in dict1.items():
        for key2, list2 in dict2.items():
            # Find intersection
            common = set(list1) & set(list2)
            if common:
                matches.append((key1, key2))

    return matches

def normalise(tag: str) -> str:
    """Lower-case, replace _ / - with space, strip punct, collapse whitespace."""
    tag = tag.replace("_", " ").replace("-", " ")
    tag = re.sub(r"[^\w\s]", " ", tag)
    return " ".join(tag.split()).lower()

# ----------------------------------------------------------------------------
# Greedy 1-to-1 fuzzy matcher that RETURNS TAG PAIRS
# ----------------------------------------------------------------------------

def fuzzy_pairs(src: List[str], tgt: List[str], thresh: int = 80) -> List[Tuple[str,str]]:
    """Return list of (src_tag, tgt_tag) pairs selected greedily.

    • exact matches first  • otherwise best remaining target ≥ *thresh*
    """
    pairs: List[Tuple[str,str]] = []
    remaining = tgt.copy()

    for s in src:
        # exact hit
        if s in remaining:
            pairs.append((s, s))
            remaining.remove(s)
            continue

        # fuzzy best hit
        best_i, best_sc = None, 0
        for i, t in enumerate(remaining):
            sc = fuzz.ratio(s, t)
            if sc > best_sc:
                best_i, best_sc = i, sc
        if best_sc >= thresh:
            t = remaining.pop(best_i)
            pairs.append((s, t))

    return pairs

def norm(t: str) -> str:
    return normalize("NFC", t).casefold()

def build_index(components: Dict[str, List[str]]):
    if not components:
        raise ValueError("Component corpus is empty")

    # 1. Count how many components each tag appears in (document frequency)
    doc_freq: Dict[str, int] = defaultdict(int)
    total_unique_tags = 0

    for tags in components.values():
        # Normalize and deduplicate tags for this component
        unique_tags = {norm(tag) for tag in tags}
        total_unique_tags += len(unique_tags)

        for tag in unique_tags:
            doc_freq[tag] += 1

    num_components = len(components)

    # 2. Compute IDF for each tag with smoothing
    idf: Dict[str, float] = {}
    for tag, df in doc_freq.items():
        # Add 1 to numerator/denominator to avoid division-by-zero
        idf[tag] = math.log((num_components + 1) / (df + 1))

    # 3. Compute average document length (in unique tags)
    avg_doc_length = total_unique_tags / num_components

    return idf, avg_doc_length

def bm25lite_score(query_tags, component_tags, idf, avg_len, k1=1.2, b=0.75):
    # 1. Identify tags common to both the query and the component
    matching_tags = query_tags & component_tags
    if not matching_tags:
        return 0.0

    # 2. Compute document-length normalization factor
    doc_length = len(component_tags)
    length_norm = (1 - b) + b * (doc_length / avg_len)
    denom = k1 * length_norm + 1

    # 3. Sum up each matching tag's contribution
    score = 0.0
    for tag in matching_tags:
        tag_weight = idf.get(tag, 0.0)
        term_factor = (k1 + 1) / denom
        score += tag_weight * term_factor

    return score

def rank_components(query_tags, components, idf, avg_len):
    # 1. Normalize the query tags once
    normalized_query: Set[str] = {norm(tag) for tag in query_tags}

    scored_components: List[Tuple[str, float]] = []
    for comp_id, tags in components.items():
        # 2. Normalize this component’s tags
        normalized_tags: Set[str] = {norm(tag) for tag in tags}

        # 3. Compute BM25Lite score
        score = bm25lite_score(
            normalized_query,
            normalized_tags,
            idf,
            avg_len
        )
        scored_components.append((comp_id, score))

    # 4. Sort by descending score, then ascending tag-count for tie-breaking
    scored_components.sort(key=lambda item: (-item[1], len(components[item[0]])))

    return scored_components


def expand_query(query: str, temperature: float = 0.1, max_new_tokens: int = 150) -> Optional[str]:
    # Build the prompt
    prompt = textwrap.dedent(f"""
    Query: “{query}”

    CONTEXT
    You are converting a user’s high-level description of a firmware
    component into search tags that can be matched against **function-level
    tags** extracted from decompiled binaries.

    TASK
    Produce bullet-list of low-level runtime-behaviour tags:
        • 2-6 words, lowercase, space-separated
        • verbs or noun phrases a reverse-engineer would assign to **one
        function** (e.g., “diffie hellman key exchange”, “checks buffer bounds”)
        • **NO protocol / product names** (ssh, tls, …)
        • ≥ 15 unique tags; more if relevant

    OUTPUT FORMAT (exactly):
    tags:
    - <tag 1>
    - <tag 2>
    …
    - <tag N>
    …
    """).strip()

    # ---------- 2. Call model ---------------------------------------------------
    response = runner.generate(
        user_input=prompt,
        temperature=temperature,
        max_new_tokens=max_new_tokens,
    )

    # The runner may return a list of chunks or a single string
    generated_text = "\n".join(response).strip() if isinstance(response, list) else response.strip()

    # ---------- 3. Parse the bullet list ---------------------------------------
    tags: List[str] = []
    in_block = False
    for line in generated_text.splitlines():
        line = line.strip()
        # Detect the start of the list (case‑insensitive)
        if not in_block and re.match(r"^tags\s*[:]", line, re.IGNORECASE):
            in_block = True
            continue

        if in_block:
            # extract and normalize
            raw = line[1:].strip()
            norm = normalize_tag(raw)
            if norm:
                tags.append(norm)

    return tags

def normalize_tag(raw: str) -> str:
    # 1) replace underscores/hyphens with spaces  
    # 2) collapse multiple spaces into one  
    # 3) lowercase everything  
    t = raw.replace("_", " ").replace("-", " ")
    t = " ".join(t.split())
    return t.lower()