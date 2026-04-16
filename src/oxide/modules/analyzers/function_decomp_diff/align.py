# -*- coding: utf-8 -*-
"""
Make baseline and target decompiled lines comparable before diffing.

Two sub-responsibilities:
  Normalize  — apply canonical substitutions so address-dependent noise
               (label names, variable names, types) doesn't produce spurious diffs.
  Project    — map baseline tokens (FUN_, LAB_, variable names) into the target
               namespace so the SequenceMatcher sees semantic equality where it exists.
"""

import re
from typing import Any, Dict, List, Optional, Tuple

# ---------------------------------------------------------------------------
# Regex constants (Ghidra decompiler token patterns)
# ---------------------------------------------------------------------------

RE_FUN = re.compile(r"\bFUN_([0-9a-fA-F]+)\b")
RE_LAB = re.compile(r"\b(?:LAB_|joined_r0x|code_r0x)[0-9a-fA-F]+\b")
RE_DAT = re.compile(r"\b_?DAT_[0-9a-fA-F]+\b")
RE_UNK = re.compile(r"\b_?UNK_[0-9a-fA-F]+\b")
RE_PTR = re.compile(r"\bPTR_[0-9a-fA-F]+\b")
RE_TMP = re.compile(r"\b(?:p{0,3}[a-z]{1,3}Var\d+)\b")
RE_LOCAL = re.compile(r"\blocal_[A-Za-z0-9_]+\b")
RE_PARAM = re.compile(r"\bparam_[0-9A-Fa-f]+\b")
RE_IN = re.compile(r"\bin_[A-Za-z0-9_]+\b")
RE_EXTRAOUT = re.compile(r"\bextraout_[A-Za-z0-9_]+\b")
RE_UNAFF = re.compile(r"\bunaff_[A-Za-z0-9_]+\b")
RE_WS = re.compile(r"\s+")

# Ordered tuple used by _same_var_kind to classify variable tokens.
VAR_KIND_PATTERNS = (
    RE_LOCAL, RE_TMP, RE_DAT, RE_PTR, RE_PARAM, RE_IN, RE_EXTRAOUT, RE_UNAFF
)

# Single regex that captures any variable token for extraction.
VAR_TOKEN_RE = re.compile(
    r"(local_[A-Za-z0-9_]+|"
    r"(?:p{0,3}[a-z]{1,3}Var\d+)|"
    r"DAT_[0-9A-Fa-f]+|"
    r"PTR_[0-9A-Fa-f]+|"
    r"param_[0-9A-Fa-f]+|"
    r"in_[A-Za-z0-9_]+|"
    r"extraout_[A-Za-z0-9_]+|"
    r"unaff_[A-Za-z0-9_]+)"
)

# Matches simple variable declarations: TYPE *? name ;
# Handles pointer types (char *p, void **pp) but not arrays or function pointers.
_RE_DECL_LINE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_]*(?:\s*\*+\s*)?)\s*([A-Za-z_][A-Za-z0-9_]*)\s*;\s*$"
)

# Minimum co-occurrence count to accept a baseline→target variable mapping.
_VAR_MAP_MIN_SUPPORT = 2


# ---------------------------------------------------------------------------
# Normalization
# ---------------------------------------------------------------------------

def apply_standard_subs(s: str) -> str:
    """Replace address-dependent tokens with canonical placeholders."""
    s = RE_LAB.sub("LAB_<ADDR>", s)
    s = RE_DAT.sub("DAT_<ADDR>", s)
    s = RE_UNK.sub("UNK_<ADDR>", s)
    s = RE_PTR.sub("PTR_<ADDR>", s)
    s = RE_TMP.sub("<TMP>", s)
    s = RE_LOCAL.sub("<LOCAL>", s)
    s = RE_PARAM.sub("<PARAM>", s)
    s = RE_IN.sub("<IN>", s)
    s = RE_EXTRAOUT.sub("<EXTRAOUT>", s)
    s = RE_UNAFF.sub("<UNAFF>", s)
    return s


def _normalize_decl_line(s: str) -> str:
    """Collapse 'TYPE *? name ;' declarations to '<TYPE> name;' to suppress type-rename noise."""
    st = s.strip()
    if "(" in st or ")" in st:
        return s
    m = _RE_DECL_LINE.match(st)
    if not m:
        return s
    return f"<TYPE> {m.group(2)};"


def normalize_lines(lines: List[str]) -> List[str]:
    """Return a version of each line with address-dependent tokens canonicalized."""
    out: List[str] = []
    for s in lines:
        s = _normalize_decl_line(s)
        s = apply_standard_subs(s)
        s = RE_WS.sub(" ", s).strip()
        out.append(s)
    return out


# ---------------------------------------------------------------------------
# Address parsing (used by projection and annotation)
# ---------------------------------------------------------------------------

def parse_addr_any(v: Any) -> Optional[int]:
    """Parse an address from int, hex string, FUN_<hex> token, or dict with addr keys."""
    try:
        if isinstance(v, int):
            return v
        if isinstance(v, str):
            s = v.strip()
            m = RE_FUN.fullmatch(s) or RE_FUN.search(s)
            if m:
                return int(m.group(1), 16)
            if s.lower().startswith("0x"):
                return int(s, 16)
            if s.isdigit():
                return int(s, 10)
        if isinstance(v, dict):
            for k in ("addr", "address", "start", "start_addr", "ea"):
                if k in v:
                    a = parse_addr_any(v[k])
                    if a is not None:
                        return a
            for k in ("name", "label"):
                if k in v and isinstance(v[k], str):
                    m = RE_FUN.search(v[k])
                    if m:
                        return int(m.group(1), 16)
        return None
    except Exception:
        return None


def _tok_from_any(v: Any) -> Optional[str]:
    a = parse_addr_any(v)
    return f"FUN_{a:08x}" if a is not None else None


# ---------------------------------------------------------------------------
# Projection — map baseline tokens into target namespace
# ---------------------------------------------------------------------------

def build_maps(baseline_func_addr: Any, target_func_addr: Any, call_diff: Dict) -> Dict[str, str]:
    """
    Build a baseline-FUN_token → target-FUN_token map from function_call_diff output.
    Seeded with the function's own address so its definition line aligns.
    """
    projmap: Dict[str, str] = {}

    base_tok = _tok_from_any(baseline_func_addr)
    tgt_tok = _tok_from_any(target_func_addr)
    if base_tok and tgt_tok:
        projmap.setdefault(base_tok, tgt_tok)

    paired = call_diff.get("fc_paired") or call_diff.get("paired") or []
    for item in paired:
        b_tok = _tok_from_any(item.get("baseline", {}).get("addr"))
        t_tok = _tok_from_any(item.get("target", {}).get("addr"))
        if b_tok and t_tok:
            projmap[b_tok] = t_tok

    return projmap


def project_fun_tokens(lines: List[str], projmap: Dict[str, str]) -> List[str]:
    """Rewrite FUN_<addr> tokens in baseline lines to match target addresses."""
    num_map: Dict[int, int] = {}
    for k, v in projmap.items():
        try:
            num_map[int(k[4:], 16)] = int(v[4:], 16)
        except Exception:
            pass

    # Infer image-base bias to handle ASLR differences not covered by projmap.
    candidates = (0, 0x100000, 0x200000, -0x100000, 0x1000, -0x1000)
    seen: List[int] = []
    for s in lines[:120]:
        for m in RE_FUN.finditer(s):
            try:
                seen.append(int(m.group(1), 16))
            except Exception:
                pass
        if len(seen) >= 64:
            break

    bias = 0
    if seen:
        best_hits = -1
        for b in candidates:
            hits = sum(1 for a in seen if (a - b) in num_map)
            if hits > best_hits:
                best_hits = hits
                bias = b

    def _sub(m: re.Match) -> str:
        a = int(m.group(1), 16)
        if a in num_map:
            return f"FUN_{num_map[a]:08x}"
        ab = a - bias
        if ab in num_map:
            return f"FUN_{(num_map[ab] + bias):08x}"
        return f"FUN_{a:08x}"

    return [RE_FUN.sub(_sub, s) for s in lines]


def build_lab_map(
    base_orig: List[str],
    tgt_orig: List[str],
    opcodes: List[Tuple[str, int, int, int, int]],
) -> Dict[str, str]:
    """Map baseline LAB_ tokens to target LAB_ tokens using equal opcode spans."""
    lab_map: Dict[str, str] = {}

    for tag, i1, i2, j1, j2 in opcodes:
        if tag != "equal":
            continue

        span = min(i2 - i1, j2 - j1)
        for off in range(span):
            b_labs = RE_LAB.findall(base_orig[i1 + off])
            t_labs = RE_LAB.findall(tgt_orig[j1 + off])

            if not b_labs or not t_labs or len(b_labs) != len(t_labs):
                continue

            for bl, tl in zip(b_labs, t_labs):
                existing = lab_map.get(bl)
                if existing is None:
                    lab_map[bl] = tl
                elif existing != tl:
                    lab_map.pop(bl, None)

    return lab_map


def project_lab_tokens(lines: List[str], lab_map: Dict[str, str]) -> List[str]:
    if not lab_map:
        return lines

    def _sub(m: re.Match) -> str:
        return lab_map.get(m.group(0), m.group(0))

    return [RE_LAB.sub(_sub, s) for s in lines]


def _extract_var_tokens(line: str) -> List[str]:
    return [m.group(0) for m in VAR_TOKEN_RE.finditer(line)]


def _same_var_kind(a: str, b: str) -> bool:
    for pat in VAR_KIND_PATTERNS:
        if pat.fullmatch(a):
            return bool(pat.fullmatch(b))
    return False


def _min_support_for(vb: str) -> int:
    # Temps are unstable across versions; require more evidence or skip entirely.
    return 999999 if RE_TMP.fullmatch(vb) else _VAR_MAP_MIN_SUPPORT


def build_var_map(
    base_orig: List[str],
    tgt_orig: List[str],
    base_norm: List[str],
    tgt_norm: List[str],
    opcodes: List[Tuple[str, int, int, int, int]],
) -> Dict[str, str]:
    """
    Infer baseline→target variable name mappings from co-occurrences in equal spans.
    Only maps variables that appear together consistently (_VAR_MAP_MIN_SUPPORT times).
    """
    by_baseline: Dict[str, Dict[str, int]] = {}

    for tag, i1, i2, j1, j2 in opcodes:
        if tag != "equal":
            continue

        for k in range(i2 - i1):
            b_idx = i1 + k
            t_idx = j1 + k

            if base_norm[b_idx] != tgt_norm[t_idx]:
                continue

            b_vars = _extract_var_tokens(base_orig[b_idx])
            t_vars = _extract_var_tokens(tgt_orig[t_idx])

            if not b_vars or not t_vars or len(b_vars) != len(t_vars):
                continue

            for vb, vt in zip(b_vars, t_vars):
                if not _same_var_kind(vb, vt):
                    continue
                tgt_counts = by_baseline.setdefault(vb, {})
                tgt_counts[vt] = tgt_counts.get(vt, 0) + 1

    var_map: Dict[str, str] = {}
    for vb, tgt_counts in by_baseline.items():
        vt_best, c_best = max(tgt_counts.items(), key=lambda kv: kv[1])
        if c_best >= _min_support_for(vb):
            var_map[vb] = vt_best

    return var_map


def project_var_tokens(lines: List[str], var_map: Dict[str, str]) -> List[str]:
    if not var_map:
        return lines

    keys = sorted(var_map.keys(), key=len, reverse=True)
    re_keys = re.compile(r"\b(" + "|".join(re.escape(k) for k in keys) + r")\b")

    def _sub(m: re.Match) -> str:
        return var_map.get(m.group(1), m.group(1))

    return [re_keys.sub(_sub, s) for s in lines]
