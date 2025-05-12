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
from typing import List, Tuple, Set, Dict
from llm_service import runner
import textwrap

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
        r = api.retrieve("tag_influential_functions", oid) or {}
        status = r.get("functions")
        if status == "FAILED":
            report[oid] = "FAILED"
            continue
        if status is None:
            report[oid] = None
            continue
        total_funcs = len(api.get_field("ghidra_disasm", oid, "functions"))
        infl_funcs  = len(r.get("influential functions") or {})
        report[oid] = {
            "names":               get_file_names(oid),
            "total functions":     total_funcs,
            "influential functions": infl_funcs,
        }
    return report

# ---------------------------------------------------------------------------
# search_firmware – Search firmware based of natural language prompt
# ---------------------------------------------------------------------------
def search_firmware(args, opts):
    # 1) collect firmware executables
    valid, _ = api.valid_oids(args)
    fw_exes, _ = separate_oids(api.expand_oids(valid))

    # 2) extract simple keywords from the prompt
    prompt = opts.get('keyword', '')
    # split on word characters, drop 1‐letter tokens
    keywords = [kw.lower() 
                for kw in re.findall(r'\w+', prompt) 
                if len(kw) > 1]

    # 3) score each executable by keyword‐in‐tag matches
    scores = []
    for oid in fw_exes:
        inf = api.retrieve("tag_influential_functions", oid) or {}
        if inf == 'FAILED':
            continue

        # collect all tags (lowercase)
        tags = [e["tag"].lower() 
                for e in inf.values() 
                if isinstance(e, dict) and "tag" in e]

        # count total hits: each time a keyword is substring of a tag
        hits = sum(1 for tag in tags for kw in keywords if kw in tag)
        scores.append((oid, hits, tags))

    # 4) sort by hits desc, take top-5
    scores.sort(key=lambda x: x[1], reverse=True)
    top5 = scores[:5]
    best_oid, best_hits, _ = top5[0] if top5 else (None, 0, [])

    # 5) assemble output
    return {
        "search": {
            "prompt":   prompt,
            "keywords": keywords,
        },
        "results": {
            "best_match": {
                "oid":  best_oid,
                'names': get_file_names(oid),
                "hits": best_hits,
            },
            "candidates": [
                {
                    "oid":  oid,
                    "names": get_file_names(oid),
                    "hits": hits,
                    "tags": tags,
                }
                for oid, hits, tags in top5
            ],
        },
    }


# ---------------------------------------------------------------------------
# search_component – Search firmware based of example
# ---------------------------------------------------------------------------

def search_component(args, opts):
    """Match *component_oid* against executables in *firmware_image_cid*.

    JSON result now contains `pairs` in each candidate: list of
    (component_tag, firmware_tag) selected by the matcher.
    """
    valid, _ = api.valid_oids(args)
    if len(valid) < 2:
        raise ValueError("Usage: search_component <component_oid> <firmware_image_cid>")
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

exports = [tag_firmware, firmware_exes, search_component, search_firmware, batch_test]

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


test_oids = [
    '135247c73bbf508fe51865711bdf07172d585ad1',
    '4c18b4ff8b157506e2c9021f9af26effdc80cefb',
    '7c2b0e741125cfbcdb3e13c919d41ff3236ad02e',
    'a3ad384f1a7013ed70968057f68a97f01ca50f56',
    '633bbcb06d402ba03ac87a55790a1c10d3bcf042',
    'ace9b957ddaa9a9097839d5b6348ad9f5a80b598',
    '9f75924628faee1a24bdade8ec6c40c81a23d317',
    '54c44545bb0d836693087abeb1a860477364d081',
    '853d74057dd0beade811f5a36e60594dbfa164a2',
    '2340cbdd4c3cb212230145147d6cd1c581f53050',
    '4683235bdc6e3ef43389902f84043c79a1ee2b70',
    '508ac86395e87a0c9d93a4a2ac4416720e008b4c',
    'a1027ae8c27a972a704bd5862375e64e7fafb36d',
    '491a6807aa65576ecc185cff0357a1117a0ea596',
    '63f231c4a704a88fb49ae8e8ff30291d372e7172',
    '096975fa03b16c7a52abbcf735d542e47b463612',
    '9839eb89616312c98e4ed48e9151bb3bfff4bdfe',
    'ec9d4a96df67b69a2697aea7a7455361b2190e8e',
    'bd29bbf773547a80259839497fbd2931dce14306',
    '16b6f6b1b30e2d6d59fe4ab6f4f0fd8d5e7d4e7e',
    'f05d9a47c92055a815f57054684421db7471fcfb',
    '181ebd27b0d4e0ee4a4d1594a0775992236019ba',
    'a826ef88295ee1a523c79f6fc812d399c42c944f',
    'ad4946a5721eb5cc64aa38f8bc3fa21932d6808a',
    'b2ba827835f9a6a3bce181bb2e2c8c7960165496',
    'a2994f2955413519da0a71b9538975a6d01c0433',
    '9b5a907d7c92620cb8000a1cf09a9174755807bc',
    '0e0f9648a81471b817da1eb4e7c1bd79e3056fba',
    'bb52ea17ca1dd4388708b5afb54e91cc812babcd',
    'c20070b393b03c0c760b219eaeedbd85f0bb3f05',
    '13bcc95ca280457687f892c01fa4d0888d43692c',
    '7c73f3022f37afb2aa97434f98734bce42e54b8f',
    '3a1a815ec2f264ddd0c047714f1844276f840fcb',
    '1fa66a464097fa4a4020b3a79419d437058bfc64',
    '8840ce462b178ec44cbbdc4dd888c2b1483999d1',
    'c0ec5832a6643ff3573bb2022834d71dcf6c69c3'
]
