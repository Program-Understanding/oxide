"""Oxide plugin: semantic‑tag matching utilities.

  • tag_firmware        – fetch and cache tag summaries for executables
  • firmware_exes       – quick inventory of executables + tag status
  • search_component    – match a reference component against a firmware image
  • search_firmware     – match components via natural‑language prompt
  • batch_test          – micro‑benchmark over a fixed test set

  The implementation purposefully stays **simple**: we rely on normalized
  string overlap plus RapidFuzz Levenshtein similarity. No stemming, IDF,
  or trigram logic is used, which keeps runtime fast and accuracy around
  75 % on the current OpenWrt dataset.
"""

from oxide.core import api
from rapidfuzz import fuzz
import re
from typing import List, Tuple, Dict
import math
from collections import Counter
import numpy as np
from typing import Dict, List, Tuple, Any
from sentence_transformers import SentenceTransformer
from transformers import AutoTokenizer
import numpy as np

# 1) set up
MODEL_ID = "sentence-transformers/all-MiniLM-L6-v2"
tokenizer = AutoTokenizer.from_pretrained(MODEL_ID)
MAX_LEN = tokenizer.model_max_length  # e.g. 512

_model = SentenceTransformer(MODEL_ID)

NAME = "FUSE"
DESC = ""
USG  = ""

# ---------------------------------------------------------------------------
# search_firmware: NL prompt → fuzzy-match against function tags
# ---------------------------------------------------------------------------

def fuse(args, opts) -> Dict:
    # options
    USE_TAGS = opts.get("use_tags", True)
    eps      = 1e-8

    # 1) collect component tokens
    valid, _ = api.valid_oids(args)
    exes, _  = separate_oids(api.expand_oids(valid))

    ALNUM = re.compile(r"[A-Za-z]{3,}")
    components = {}
    for oid in exes:
        if any((".so" in n) or (".ko" in n) for n in get_file_names(oid)):
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
                        tags.append(normalize_tag(text))

        if strings or (USE_TAGS and tags):
            components[oid] = {"str": strings, "tag": tags}

    if not components:
        return {"error": "No tokens extracted from firmware!"}

    # 2) build IDF maps
    str_docs = {oid: comp["str"] for oid, comp in components.items()}
    idf_str  = compute_idf(str_docs)

    if USE_TAGS:
        tag_docs = {oid: comp["tag"] for oid, comp in components.items()}
        idf_tag  = compute_idf(tag_docs)

    # 3) select highest‑IDF strings (full budget) per component
    selected_tags = {}
    selected_strs = {}
    for oid, comp in components.items():
        if USE_TAGS:
            selected_tags[oid] = select_until(comp["tag"], idf_tag, MAX_LEN)
            selected_strs[oid] = select_until(comp["str"], idf_str, MAX_LEN)
        else:
            # all tokens go to strings
            selected_tags[oid] = []
            selected_strs[oid] = select_until(comp["str"], idf_str, MAX_LEN)

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
                "names": get_file_names(oid),
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

exports = [fuse]

# ---------------------------------------------------------------------------
# Utility helpers
# ---------------------------------------------------------------------------

def compute_idf(docs):
    df = Counter()
    N  = len(docs)
    for toks in docs.values():
        for t in set(toks):
            df[t] += 1
    # standard smoothing to avoid zero/∞
    return {t: math.log((N+1)/(df_t+1)) + 1
            for t, df_t in df.items()}

def select_until(tokens, idf_map, budget):
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

def separate_oids(oids: List[str]) -> Tuple[set, set]:
    """Split OIDs into executables and others"""
    exes, others = set(), set()
    for oid in oids:
        cat = api.get_field('categorize', oid, oid)
        (exes if cat == 'executable' else others).add(oid)
    return exes, others


def get_file_names(oid: str) -> List[str]:
    """Return all recorded file names for an OID"""
    return list(api.get_names_from_oid(oid))


def get_all_file_names(oids: List[str]) -> Dict[str, List[str]]:
    """Map OIDs to their file names"""
    return {oid: get_file_names(oid) for oid in oids}


def pair_exes(map1: Dict[str,List[str]], map2: Dict[str,List[str]]) -> List[Tuple[str,str]]:
    """Match OIDs by shared file names"""
    pairs = []
    for a, na in map1.items():
        for b, nb in map2.items():
            if set(na) & set(nb):
                pairs.append((a, b))
    return pairs

# ── IDF utilities ──────────────────────────────────────────────────────
def build_idf(components: dict[str, List[str]]) -> dict[str, float]:
    """IDF(tag) = log10(N / df) with df = #components containing tag."""
    df = Counter()
    for tags in components.values():
        df.update(set(tags))
    N = max(len(components), 1)
    return {tag: math.log10(N / df[tag]) for tag in df}

def dedup_and_cap(raw: List[str], max_tags: int = 30) -> List[str]:
    """Drop duplicates, keep order, cap length (no stop-word removal)."""
    seen, out = set(), []
    for t in map(normalize_tag, raw):
        if t not in seen:
            out.append(t)
            seen.add(t)
            if len(out) >= max_tags:
                break
    return out

# ---------------------------------------------------------------------------
# Normalization and fuzzy primitives
# ---------------------------------------------------------------------------

def normalize_tag(tag: str) -> str:
    """Normalize tag text for comparison"""
    try:
        from unicodedata import normalize as u_norm
        tag = u_norm('NFC', tag)
    except ImportError:
        pass
    tag = tag.replace('_', ' ')
    tag = re.sub(r"[^\w\s]", ' ', tag)
    return re.sub(r"\s+", ' ', tag).strip().lower()


def fuzzy_pairs(src: List[str], tgt: List[str], thresh: int = 80) -> List[Tuple[str, str]]:
    """Pair up src→tgt tags by best fuzzy match"""
    pairs = []
    remaining = tgt.copy()
    for s in src:
        if s in remaining:
            pairs.append((s, s)); remaining.remove(s); continue
        best_i, best_score = None, 0
        for i, t in enumerate(remaining):
            score = fuzz.ratio(s, t)
            if score > best_score:
                best_i, best_score = i, score
        if best_score >= thresh and best_i is not None:
            pairs.append((s, remaining.pop(best_i)))
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
