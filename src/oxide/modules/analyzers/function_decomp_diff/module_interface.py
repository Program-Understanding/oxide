# -*- coding: utf-8 -*-
"""
function_decomp_diff — unified diff of decompiler text for one function.

Full pipeline (default):
  1) Retrieve baseline/target decompiler text.
  2) Build call pairing from function_call_diff (target-centric labels).
  3) Normalize both sides to stable labels (for alignment).
  4) Align with SequenceMatcher to get opcodes.
  5) Infer baseline→target LAB_ and variable/DAT/PTR/etc mappings from normalized equal lines.
  6) Project baseline ORIGINAL names into the target namespace (FUN_/LAB_/vars).
  7) Emit unified diff with replace-refinement (collapse identical lines to context).
  8) Optionally post-annotate ONLY '+' lines with tags for known target calls.
  9) Optionally compact to fit an LLM budget.

Raw mode (new flag: raw=True):
  Turns off ALL processing steps (no normalize, no mapping, no projection, no refinement,
  no annotation, no compaction). Produces a straightforward unified diff of ORIGINAL lines.

Behavior policy (important):
  - retrieve_function_decomp_lines(...) returns:
      * None  => hard failure (function not found / decmap missing / bad structure)
      * []    => function resolved but no decompiler lines (treated as SAFE/benign)
  - results(...) treats None as an error and emits error_kind metadata.
    Empty lists are allowed and produce a valid (possibly header-only) unified diff.
"""

DESC = ""
NAME = "function_decomp_diff"

import logging
import re
from difflib import SequenceMatcher
from typing import Any, Dict, List, Optional, Tuple

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

# ---------------------------
# LLM context sizing (approx)
# ---------------------------

_LLM_NUM_CTX_TOKENS = 8192
_LLM_RESERVED_TOKENS = 1024
_APPROX_CHARS_PER_TOKEN = 4

_MAX_UNIFIED_CHARS = (_LLM_NUM_CTX_TOKENS - _LLM_RESERVED_TOKENS) * _APPROX_CHARS_PER_TOKEN
_LLM_DIFF_CHAR_BUDGET = min(_MAX_UNIFIED_CHARS, 20000)

# Mapping / compaction hyperparameters
_VAR_MAP_MIN_SUPPORT = 2
_COMPACTION_CTX_CANDIDATES = (100, 50, 25, 10, 7, 5, 3, 1, 0)

# ---------------------------
# Options
# ---------------------------

opts_doc = {
    "target": {"type": str, "mangle": True, "default": "None"},
    "baseline": {"type": str, "mangle": True, "default": "None"},
    "annotate": {"type": bool, "mangle": True, "default": False},
    "compact": {"type": bool, "mangle": True, "default": True},
    # New: turn off ALL steps and emit a raw unified diff
    "raw": {"type": bool, "mangle": True, "default": False},
}


def documentation() -> Dict[str, Any]:
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }


# ---------------------------
# Regexes
# ---------------------------

_RE_FUN = re.compile(r"\bFUN_([0-9a-fA-F]+)\b")
_RE_LAB = re.compile(r"\bLAB_[0-9a-fA-F]+\b")
_RE_DAT = re.compile(r"\bDAT_[0-9a-fA-F]+\b")
_RE_PTR = re.compile(r"\bPTR_[0-9a-fA-F]+\b")
_RE_TMP = re.compile(r"\b(?:p{0,3}[a-z]{1,3}Var\d+)\b")
_RE_LOCAL = re.compile(r"\blocal_[A-Za-z0-9_]+\b")

_RE_PARAM = re.compile(r"\bparam_[0-9A-Fa-f]+\b")
_RE_IN = re.compile(r"\bin_[A-Za-z0-9_]+\b")
_RE_EXTRAOUT = re.compile(r"\bextraout_[A-Za-z0-9_]+\b")
_RE_UNAFF = re.compile(r"\bunaff_[A-Za-z0-9_]+\b")

_RE_WS = re.compile(r"\s+")
_FUN_TOKEN_RE = re.compile(r"\bFUN_([0-9a-fA-F]+)\b")

_VAR_TOKEN_RE = re.compile(
    r"(local_[A-Za-z0-9_]+|"
    r"(?:p{0,3}[a-z]{1,3}Var\d+)|"
    r"DAT_[0-9A-Fa-f]+|"
    r"PTR_[0-9A-Fa-f]+|"
    r"param_[0-9A-Fa-f]+|"
    r"in_[A-Za-z0-9_]+|"
    r"extraout_[A-Za-z0-9_]+|"
    r"unaff_[A-Za-z0-9_]+)"
)

# ---------------------------
# Public entry
# ---------------------------


def results(oid_list: List[str], opts: dict) -> Dict[str, Any]:
    oid_list = api.expand_oids(oid_list)
    if not oid_list or len(oid_list) < 2:
        raise ValueError("function_decomp_diff requires two OIDs: [target_oid, baseline_oid]")

    target_oid, baseline_oid = oid_list[0], oid_list[1]
    target_addr = opts["target"]
    baseline_addr = opts["baseline"]

    raw = bool(opts.get("raw", False))

    tgt_orig = retrieve_function_decomp_lines(target_oid, target_addr)
    base_orig = retrieve_function_decomp_lines(baseline_oid, baseline_addr)

    # None = hard failure (function not found / decmap missing / malformed)
    if tgt_orig is None or base_orig is None:
        return {
            "error": "Could not retrieve function decomp lines for one or both sides.",
            "error_kind": "missing_function_or_decmap",
            "meta": {
                "target_oid": target_oid,
                "baseline_oid": baseline_oid,
                "target_addr": str(target_addr),
                "baseline_addr": str(baseline_addr),
                "target_none": tgt_orig is None,
                "baseline_none": base_orig is None,
            },
        }

    # [] is allowed (empty decomp output is not an error)
    tgt_orig = _strip_decmap_prefix_if_present(tgt_orig)
    base_orig = _strip_decmap_prefix_if_present(base_orig)

    fn_b = _get_function_name(baseline_oid, baseline_addr) or f"{baseline_addr}"
    fn_t = _get_function_name(target_oid, target_addr) or f"{target_addr}"
    fromfile = f"{fn_b} (baseline {baseline_oid})"
    tofile = f"{fn_t} (target   {target_oid})"

    target_decomp_empty = (len(tgt_orig) == 0)
    baseline_decomp_empty = (len(base_orig) == 0)

    # ---------------------------
    # RAW MODE: turn off ALL steps
    # ---------------------------
    if raw:
        unified_raw = _emit_unified_raw(base_orig, tgt_orig, fromfile, tofile)
        return {
            "unified": unified_raw,
            "meta": {
                "pipeline": "raw",
                "baseline_func": fn_b,
                "baseline_oid": baseline_oid,
                "target_func": fn_t,
                "target_oid": target_oid,
                "normalized_alignment": False,
                "raw": True,
                "unified_len": len(unified_raw),
                "target_decomp_empty": target_decomp_empty,
                "baseline_decomp_empty": baseline_decomp_empty,
            },
        }

    # ---------------------------
    # FULL PIPELINE
    # ---------------------------

    base_norm = _normalize_lines(base_orig)
    tgt_norm = _normalize_lines(tgt_orig)

    # Alignment over normalized text
    sm = SequenceMatcher(
        None,
        [l + "\n" for l in base_norm],
        [l + "\n" for l in tgt_norm],
        autojunk=False,
    )
    opcodes = sm.get_opcodes()

    projmap_base = _build_maps(baseline_oid, target_oid, baseline_addr, target_addr)
    lab_map = _build_lab_map_from_opcodes(base_orig, tgt_orig, opcodes)
    var_map = _build_var_map(base_orig, tgt_orig, base_norm, tgt_norm, opcodes)

    # Project baseline ORIGINAL lines into target namespace
    base_proj = _project_fun_tokens(base_orig, projmap_base)
    base_proj = _project_lab_tokens(base_proj, lab_map)
    base_proj = _project_var_tokens(base_proj, var_map)

    # Headers
    a_len = len(base_orig)
    b_len = len(tgt_orig)
    a_start_disp = 1 if a_len else 0
    b_start_disp = 1 if b_len else 0

    out: List[str] = [
        f"--- {fromfile}",
        f"+++ {tofile}",
        f"@@ -{a_start_disp},{a_len} +{b_start_disp},{b_len} @@",
    ]

    # Emit ORIGINAL with replace-refinement
    for tag, i1, i2, j1, j2 in opcodes:
        base_slice = base_proj[i1:i2]
        tgt_slice = tgt_orig[j1:j2]

        if tag == "equal":
            # In full pipeline, we keep aggressive canonical collapsing for readability.
            # If you want "no collapsing", use raw=True.
            if _lines_equal_canon(base_slice, tgt_slice):
                for s in tgt_slice:
                    out.append(" " + s)
            else:
                _emit_refined(out, base_slice, tgt_slice)
        else:
            _emit_refined(out, base_slice, tgt_slice)

    unified = "\n".join(out) + ("\n" if out else "")

    # Post-diff annotation (added lines)
    if opts.get("annotate", False):
        name_to_addr = _get_function_calls(target_oid, baseline_oid, target_addr, baseline_addr)
        if name_to_addr:
            unified = _annotate_unified_with_tags(
                unified,
                name_to_addr,
                target_oid,
                annotate_kinds=("+",),
            )

    # Optional compaction for LLM context budget
    unified_full = unified
    unified_compact = _maybe_compact_unified(unified_full, max_chars=_LLM_DIFF_CHAR_BUDGET)

    if opts.get("compact", True):
        unified = unified_compact
    else:
        unified = unified_full

    return {
        "unified": unified,
        "meta": {
            "pipeline": "full",
            "baseline_func": fn_b,
            "baseline_oid": baseline_oid,
            "target_func": fn_t,
            "target_oid": target_oid,
            "normalized_alignment": bool(opts.get("normalize", True)),
            "raw": False,
            "unified_full_len": len(unified_full),
            "unified_compact_len": len(unified_compact),
            "unified_truncated": len(unified_compact) < len(unified_full),
            "target_decomp_empty": target_decomp_empty,
            "baseline_decomp_empty": baseline_decomp_empty,
        },
    }


# ---------------------------
# RAW diff emitter
# ---------------------------


def _emit_unified_raw(base_lines: List[str], tgt_lines: List[str], fromfile: str, tofile: str) -> str:
    a_len = len(base_lines)
    b_len = len(tgt_lines)
    a_start_disp = 1 if a_len else 0
    b_start_disp = 1 if b_len else 0

    out: List[str] = [
        f"--- {fromfile}",
        f"+++ {tofile}",
        f"@@ -{a_start_disp},{a_len} +{b_start_disp},{b_len} @@",
    ]

    sm = SequenceMatcher(
        None,
        [l + "\n" for l in base_lines],
        [l + "\n" for l in tgt_lines],
        autojunk=False,
    )

    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            for s in tgt_lines[j1:j2]:
                out.append(" " + s)
        elif tag == "delete":
            for s in base_lines[i1:i2]:
                out.append("-" + s)
        elif tag == "insert":
            for s in tgt_lines[j1:j2]:
                out.append("+" + s)
        else:  # replace
            for s in base_lines[i1:i2]:
                out.append("-" + s)
            for s in tgt_lines[j1:j2]:
                out.append("+" + s)

    return "\n".join(out) + ("\n" if out else "")


# ---------------------------
# Label + variable mapping helpers
# ---------------------------


def _build_lab_map_from_opcodes(
    base_orig: List[str],
    tgt_orig: List[str],
    opcodes: List[Tuple[str, int, int, int, int]],
) -> Dict[str, str]:
    lab_map: Dict[str, str] = {}

    for tag, i1, i2, j1, j2 in opcodes:
        if tag != "equal":
            continue

        span = min(i2 - i1, j2 - j1)
        for off in range(span):
            b_line = base_orig[i1 + off]
            t_line = tgt_orig[j1 + off]

            b_labs = _RE_LAB.findall(b_line)
            t_labs = _RE_LAB.findall(t_line)

            if not b_labs or not t_labs:
                continue
            if len(b_labs) != len(t_labs):
                continue

            for bl, tl in zip(b_labs, t_labs):
                existing = lab_map.get(bl)
                if existing is None:
                    lab_map[bl] = tl
                elif existing != tl:
                    lab_map.pop(bl, None)

    return lab_map


def _project_lab_tokens(lines: List[str], lab_map: Dict[str, str]) -> List[str]:
    if not lab_map:
        return lines

    def _sub(m: re.Match) -> str:
        lab = m.group(0)
        return lab_map.get(lab, lab)

    return [_RE_LAB.sub(_sub, s) for s in lines]


def _extract_var_tokens(line: str) -> List[str]:
    return [m.group(0) for m in _VAR_TOKEN_RE.finditer(line)]


def _same_var_kind(a: str, b: str) -> bool:
    if _RE_LOCAL.fullmatch(a):
        return bool(_RE_LOCAL.fullmatch(b))
    if _RE_TMP.fullmatch(a):
        return bool(_RE_TMP.fullmatch(b))
    if _RE_DAT.fullmatch(a):
        return bool(_RE_DAT.fullmatch(b))
    if _RE_PTR.fullmatch(a):
        return bool(_RE_PTR.fullmatch(b))
    if _RE_PARAM.fullmatch(a):
        return bool(_RE_PARAM.fullmatch(b))
    if _RE_IN.fullmatch(a):
        return bool(_RE_IN.fullmatch(b))
    if _RE_EXTRAOUT.fullmatch(a):
        return bool(_RE_EXTRAOUT.fullmatch(b))
    if _RE_UNAFF.fullmatch(a):
        return bool(_RE_UNAFF.fullmatch(b))
    return False


def _build_var_map(
    base_orig: List[str],
    tgt_orig: List[str],
    base_norm: List[str],
    tgt_norm: List[str],
    opcodes: List[Tuple[str, int, int, int, int]],
) -> Dict[str, str]:
    pair_counts: Dict[Tuple[str, str], int] = {}

    for tag, i1, i2, j1, j2 in opcodes:
        if tag != "equal":
            continue

        length = i2 - i1
        for k in range(length):
            b_idx = i1 + k
            t_idx = j1 + k

            if base_norm[b_idx] != tgt_norm[t_idx]:
                continue

            b_line = base_orig[b_idx]
            t_line = tgt_orig[t_idx]

            b_vars = _extract_var_tokens(b_line)
            t_vars = _extract_var_tokens(t_line)

            if not b_vars or not t_vars:
                continue
            if len(b_vars) != len(t_vars):
                continue

            for vb, vt in zip(b_vars, t_vars):
                if not _same_var_kind(vb, vt):
                    continue
                pair_counts[(vb, vt)] = pair_counts.get((vb, vt), 0) + 1

    by_baseline: Dict[str, Dict[str, int]] = {}
    for (vb, vt), cnt in pair_counts.items():
        by_baseline.setdefault(vb, {})
        by_baseline[vb][vt] = by_baseline[vb].get(vt, 0) + cnt

    var_map: Dict[str, str] = {}
    for vb, tgt_counts in by_baseline.items():
        vt_best, c_best = max(tgt_counts.items(), key=lambda kv: kv[1])
        if c_best < _min_support_for(vb):
            continue
        var_map[vb] = vt_best

    return var_map


def _min_support_for(vb: str) -> int:
    # Temps are unstable; require more evidence or skip entirely.
    return 999999 if _RE_TMP.fullmatch(vb) else _VAR_MAP_MIN_SUPPORT


def _project_var_tokens(lines: List[str], var_map: Dict[str, str]) -> List[str]:
    if not var_map:
        return lines

    keys = sorted(var_map.keys(), key=len, reverse=True)
    pattern = r"\b(" + "|".join(re.escape(k) for k in keys) + r")\b"
    re_keys = re.compile(pattern)

    def _sub(m: re.Match) -> str:
        vb = m.group(1)
        return var_map.get(vb, vb)

    return [re_keys.sub(_sub, s) for s in lines]


# ---------------------------
# Maps via function_call_diff (target-centric)
# ---------------------------


def _parse_addr_any(v: Any) -> Optional[int]:
    try:
        if isinstance(v, int):
            return v
        if isinstance(v, str):
            s = v.strip()
            m = _FUN_TOKEN_RE.fullmatch(s) or _FUN_TOKEN_RE.search(s)
            if m:
                return int(m.group(1), 16)
            if s.lower().startswith("0x"):
                return int(s, 16)
            if s.isdigit():
                return int(s, 10)
        if isinstance(v, dict):
            for k in ("addr", "address", "start", "start_addr", "ea"):
                if k in v:
                    a = _parse_addr_any(v[k])
                    if a is not None:
                        return a
            for k in ("name", "label"):
                if k in v and isinstance(v[k], str):
                    m = _FUN_TOKEN_RE.search(v[k])
                    if m:
                        return int(m.group(1), 16)
        return None
    except Exception:
        return None


def _tok_from_any(v: Any) -> Optional[str]:
    a = _parse_addr_any(v)
    return f"FUN_{a:08x}" if a is not None else None


def _build_maps(
    baseline_oid: str, target_oid: str, baseline_func_addr: Any, target_func_addr: Any
) -> Dict[str, str]:
    projmap_base: Dict[str, str] = {}

    # Seed with the function itself so the def-line syncs.
    base_tok = _tok_from_any(baseline_func_addr)
    tgt_tok = _tok_from_any(target_func_addr)
    if base_tok and tgt_tok:
        projmap_base.setdefault(base_tok, tgt_tok)

    try:
        diff = (
            api.retrieve(
                "function_call_diff",
                [target_oid, baseline_oid],
                {"target": str(target_func_addr), "baseline": str(baseline_func_addr)},
            )
            or {}
        )
    except Exception as e:
        logger.warning(f"[{NAME}] function_call_diff retrieval failed: {e}")
        diff = {}

    paired = diff.get("fc_paired") or diff.get("paired") or []
    for item in paired:
        b_side = item.get("baseline", {})
        t_side = item.get("target", {})

        b_tok = _tok_from_any(b_side.get("addr"))
        t_tok = _tok_from_any(t_side.get("addr"))

        if b_tok and t_tok:
            projmap_base[b_tok] = t_tok

    return projmap_base


# ---------------------------
# Projection / Normalization
# ---------------------------


def _project_fun_tokens(lines: List[str], projmap: Dict[str, str]) -> List[str]:
    # Build int->int map
    num_map: Dict[int, int] = {}
    for k, v in projmap.items():
        try:
            num_map[int(k[4:], 16)] = int(v[4:], 16)
        except Exception:
            pass

    # Infer likely image-base bias
    candidates = (0, 0x100000, 0x200000, -0x100000, 0x1000, -0x1000)
    seen: List[int] = []
    for s in lines[:120]:
        for m in _RE_FUN.finditer(s):
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

    return [_RE_FUN.sub(_sub, s) for s in lines]


_RE_DECL_LINE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_\s\*]*)\s+([A-Za-z_][A-Za-z0-9_]*)\s*;\s*$"
)


def _normalize_decl_line(s: str) -> str:
    st = s.strip()
    if "(" in st or ")" in st:
        return s
    m = _RE_DECL_LINE.match(st)
    if not m:
        return s
    name = m.group(2)
    return f"<TYPE> {name};"


def _normalize_lines(lines: List[str]) -> List[str]:
    out: List[str] = []
    for s in lines:
        s = _normalize_decl_line(s)
        s = _RE_LAB.sub("LAB_<ADDR>", s)
        s = _RE_DAT.sub("DAT_<ADDR>", s)
        s = _RE_PTR.sub("PTR_<ADDR>", s)
        s = _RE_TMP.sub("<TMP>", s)
        s = _RE_LOCAL.sub("<LOCAL>", s)
        s = _RE_PARAM.sub("<PARAM>", s)
        s = _RE_IN.sub("<IN>", s)
        s = _RE_EXTRAOUT.sub("<EXTRAOUT>", s)
        s = _RE_UNAFF.sub("<UNAFF>", s)
        s = _RE_WS.sub(" ", s).strip()
        out.append(s)
    return out


# ---------------------------
# Replace refinement
# ---------------------------

_RE_TYPE = re.compile(
    r"\b(?:"
    r"undefined\d+|"
    r"__uid_t|__gid_t|"
    r"u?int(?:8|16|32|64)?_t|"
    r"int|uint|long|ulong|short|ushort|char|uchar|bool|size_t|"
    r"FILE|"
    r"void"
    r")\b"
)

_RE_PARENRUN = re.compile(r"[()]{2,}")


def _canon_decomp_noise(s: str) -> str:
    s = _RE_LAB.sub("LAB_<ADDR>", s)
    s = _RE_DAT.sub("DAT_<ADDR>", s)
    s = _RE_PTR.sub("PTR_<ADDR>", s)
    s = _RE_TMP.sub("<TMP>", s)
    s = _RE_LOCAL.sub("<LOCAL>", s)
    s = _RE_PARAM.sub("<PARAM>", s)
    s = _RE_IN.sub("<IN>", s)
    s = _RE_EXTRAOUT.sub("<EXTRAOUT>", s)
    s = _RE_UNAFF.sub("<UNAFF>", s)
    s = _RE_TYPE.sub("<TYPE>", s)
    s = _RE_PARENRUN.sub("()", s)
    s = _RE_WS.sub(" ", s).strip()
    return s


def _lines_equal_canon(a: List[str], b: List[str]) -> bool:
    if len(a) != len(b):
        return False
    for x, y in zip(a, b):
        if _canon_decomp_noise(x) != _canon_decomp_noise(y):
            return False
    return True


def _canon_block(lines: List[str]) -> str:
    return " ".join(_canon_decomp_noise(x) for x in lines)


def _emit_refined(out: List[str], base_slice: List[str], tgt_slice: List[str]) -> None:
    if not base_slice and not tgt_slice:
        return

    # If the whole block is canon-equal, emit as context.
    if _canon_block(base_slice) == _canon_block(tgt_slice):
        for t in tgt_slice:
            out.append(" " + t)
        return

    base_keys = [_canon_decomp_noise(s) + "\n" for s in base_slice]
    tgt_keys = [_canon_decomp_noise(s) + "\n" for s in tgt_slice]

    sm = SequenceMatcher(None, base_keys, tgt_keys, autojunk=False)
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            for s in tgt_slice[j1:j2]:
                out.append(" " + s)
        elif tag == "delete":
            for s in base_slice[i1:i2]:
                out.append("-" + s)
        elif tag == "insert":
            for s in tgt_slice[j1:j2]:
                out.append("+" + s)
        else:  # replace
            k = min(i2 - i1, j2 - j1)
            for kidx in range(k):
                b = base_slice[i1 + kidx]
                t = tgt_slice[j1 + kidx]
                if _canon_decomp_noise(b) == _canon_decomp_noise(t):
                    out.append(" " + t)
                else:
                    out.append("-" + b)
                    out.append("+" + t)
            for s in base_slice[i1 + k : i2]:
                out.append("-" + s)
            for s in tgt_slice[j1 + k : j2]:
                out.append("+" + s)


# ---------------------------
# Known calls loader (TARGET side) + post-diff annotation
# ---------------------------


def _normalize_known_calls_shape(obj: Any) -> Optional[Dict[str, int]]:
    if obj is None:
        return None

    out: Dict[str, int] = {}

    if isinstance(obj, dict):
        numeric_like_keys = True
        for k in obj.keys():
            if not isinstance(k, int) and not (
                isinstance(k, str) and (k.isdigit() or k.lower().startswith("0x"))
            ):
                numeric_like_keys = False
                break

        if numeric_like_keys:
            for a, n in obj.items():
                addr = _parse_addr_any(a)
                if addr is None:
                    continue
                if isinstance(n, str) and n:
                    out[n] = addr
            return out or None

        for n, a in obj.items():
            if not isinstance(n, str) or not n:
                continue
            addr = _parse_addr_any(a)
            if addr is None:
                addr = _parse_addr_any(n)
            if addr is not None:
                out[n] = addr
        return out or None

    if isinstance(obj, list):
        for it in obj:
            if isinstance(it, dict):
                n = it.get("name")
                a = _parse_addr_any(it.get("addr"))
                if isinstance(n, str) and n and a is not None:
                    out[n] = a
            elif isinstance(it, str):
                n = it
                a = _parse_addr_any(n)
                if a is not None:
                    out[n] = a
        return out or None

    return None


def _get_function_calls(
    target_oid, baseline_oid, target_func, baseline_func
) -> Optional[Dict[str, int]]:
    diff = (
        api.retrieve(
            "function_call_diff",
            [target_oid, baseline_oid],
            {"target": str(target_func), "baseline": str(baseline_func)},
        )
        or {}
    )

    paired = diff.get("fc_paired") or []
    existing = diff.get("fc_add_existing") or []
    new = diff.get("fc_add_new") or []

    target_func_calls: Dict[Any, Any] = {}
    for item in paired:
        t = item.get("target") or {}
        if "addr" in t and "name" in t:
            target_func_calls[t["addr"]] = t["name"]
    for item in existing:
        t = item.get("target") or {}
        if "addr" in t and "name" in t:
            target_func_calls[t["addr"]] = t["name"]
    for item in new:
        t = item.get("target") or {}
        if "addr" in t and "name" in t:
            target_func_calls[t["addr"]] = t["name"]

    return _normalize_known_calls_shape(target_func_calls)


def _get_tag_for_addr(oid: str, addr: int) -> Optional[str]:
    try:
        return api.get_field("llm_function_analysis", oid, "tag", {"func_offset": addr})
    except Exception:
        return None


def _annotate_unified_with_tags(
    unified: str,
    name_to_addr: Dict[str, int],
    target_oid: str,
    annotate_kinds: Tuple[str, ...] = ("+",),
) -> str:
    if not unified or not name_to_addr:
        return unified

    # Prefetch tags
    name_to_tag: Dict[str, Optional[str]] = {
        name: _get_tag_for_addr(target_oid, addr) for name, addr in name_to_addr.items()
    }

    names_sorted = sorted(name_to_addr.keys(), key=len, reverse=True)
    if not names_sorted:
        return unified

    call_pat = re.compile(
        r"\b(" + "|".join(re.escape(n) for n in names_sorted) + r")\b\s*\("
    )

    out_lines: List[str] = []
    for line in unified.splitlines():
        if line.startswith(("---", "+++", "@@")):
            out_lines.append(line)
            continue

        if not line or line[0] not in annotate_kinds:
            out_lines.append(line)
            continue

        prefix, body = line[0], line[1:]
        code_part, sep, trailing = body.partition("//")

        matches = [m.group(1) for m in call_pat.finditer(code_part)]
        if not matches:
            out_lines.append(line)
            continue

        # Dedup preserving order
        seen: List[str] = []
        for n in matches:
            if n not in seen:
                seen.append(n)

        fragments: List[str] = []
        for n in seen:
            tag = name_to_tag.get(n)
            fragments.append(f"{n}: {tag}" if tag else n)

        if sep and all(fragment in trailing for fragment in fragments):
            out_lines.append(line)
            continue

        annotated = prefix + code_part
        if sep:
            annotated += sep + trailing
        annotated += " // " + "; ".join(fragments)

        out_lines.append(annotated)

    return "\n".join(out_lines) + ("\n" if out_lines else "")


# ---------------------------
# LLM compaction helpers
# ---------------------------

_DECL_LINE_RE2 = re.compile(
    r"^\s*(?:"
    r"undefined\d+|int|uint|long|short|char|bool|size_t|FILE|"
    r"__uid_t|__gid_t|void\s*\*"
    r")\b.*;\s*$"
)


def _extract_changed_regions(unified: str, context_lines: int = 10) -> str:
    """
    Keep:
      - file headers and hunk headers
      - +/- lines (excluding simple decl-only lines)
      - context_lines around each kept +/- line
    Insert "..." between omitted regions.
    """
    lines = unified.splitlines()
    n = len(lines)
    if n == 0:
        return unified

    keep: set[int] = set()

    # Always keep file headers and hunk headers
    for i, line in enumerate(lines):
        if line.startswith(("---", "+++")) or line.startswith(("@@",)):
            keep.add(i)

    # Keep change lines and surrounding context
    for i, line in enumerate(lines):
        if not line:
            continue
        if line.startswith(("---", "+++")):
            continue
        if line[0] not in ("+", "-"):
            continue

        body = line[1:]
        if _DECL_LINE_RE2.match(body):
            continue

        lo = max(0, i - context_lines)
        hi = min(n - 1, i + context_lines)
        for j in range(lo, hi + 1):
            keep.add(j)

    if not keep:
        return unified

    new_lines: List[str] = []
    last_idx = -1
    for idx in sorted(keep):
        if last_idx != -1 and idx > last_idx + 1:
            new_lines.append("...")
        new_lines.append(lines[idx])
        last_idx = idx

    return "\n".join(new_lines) + ("\n" if new_lines else "")


def _maybe_compact_unified(unified: str, max_chars: int = _MAX_UNIFIED_CHARS) -> str:
    if not unified:
        return unified

    budget = min(max_chars, _LLM_DIFF_CHAR_BUDGET)

    if len(unified) <= budget:
        return unified

    last_compact: Optional[str] = None
    for ctx in _COMPACTION_CTX_CANDIDATES:
        last_compact = _extract_changed_regions(unified, context_lines=ctx)
        if len(last_compact) <= budget:
            return last_compact

    compact = last_compact or unified

    # Hard truncate middle while keeping head and tail
    lines = compact.splitlines()
    note = "... [diff truncated to fit LLM context]"
    note_len = len(note) + 1

    if budget <= 2 * note_len:
        return note + "\n"

    remaining_budget = budget - 2 * note_len
    target_each = remaining_budget // 2

    prefix_lines: List[str] = []
    prefix_chars = 0
    for line in lines:
        line_len = len(line) + 1
        if prefix_chars + line_len > target_each:
            break
        prefix_lines.append(line)
        prefix_chars += line_len

    suffix_lines_rev: List[str] = []
    suffix_chars = 0
    for line in reversed(lines):
        line_len = len(line) + 1
        if suffix_chars + line_len > target_each:
            break
        suffix_lines_rev.append(line)
        suffix_chars += line_len

    suffix_lines = list(reversed(suffix_lines_rev))

    if len("\n".join(lines)) <= remaining_budget:
        result_lines = [note] + lines + [note]
        return "\n".join(result_lines) + "\n"

    result_lines: List[str] = [note]
    result_lines.extend(prefix_lines)
    result_lines.append("...")
    result_lines.extend(suffix_lines)
    result_lines.append(note)
    return "\n".join(result_lines) + "\n"


# ---------------------------
# Ghidra helpers
# ---------------------------

_RE_DECMAP_PREFIX = re.compile(r"^\s*\d+:(.*)$")


def _resolve_func_key(decompile: Dict[str, Any], want: str) -> Optional[str]:
    if want in decompile:
        return want

    want_short = want.split("::")[-1]
    cands = [
        k
        for k in decompile.keys()
        if isinstance(k, str) and k.split("::")[-1] == want_short
    ]
    if len(cands) == 1:
        return cands[0]
    return None


def retrieve_function_decomp_lines(oid: str, func_addr: Any) -> Optional[List[str]]:
    """
    Return:
      - None  => hard failure (can't resolve function or decmap)
      - []    => function resolved but no decompiler output (benign/empty)
      - [...] => decompiler lines
    """
    func_name = _get_function_name(oid, func_addr)
    if not func_name:
        # Can't even identify the function => hard failure
        return None

    decmap = api.retrieve("ghidra_decmap", [oid], {"org_by_func": True})
    if not isinstance(decmap, dict) or not decmap:
        # Missing/invalid decmap => hard failure
        return None

    dm = decmap.get(oid, decmap) if isinstance(decmap.get(oid), dict) else decmap
    decompile = dm.get("decompile") if isinstance(dm, dict) else None
    if not isinstance(decompile, dict):
        # Missing/invalid decompile section => hard failure
        return None

    func_key = func_name if func_name in decompile else _resolve_func_key(decompile, func_name)
    if not func_key:
        # Function exists (ghidra_disasm) but no decompile entry => empty decomp, NOT failure
        return []

    func_blocks = decompile.get(func_key)
    if not isinstance(func_blocks, dict):
        # Function exists but no blocks => empty decomp, NOT failure
        return []

    decomp_map: Dict[int, str] = {}
    saw_any_tagged = False
    untagged_fallback: List[str] = []

    for _block_id, block in func_blocks.items():
        if not isinstance(block, dict):
            continue
        lines = block.get("line") or []
        if not isinstance(lines, list):
            continue

        for raw in lines:
            if not isinstance(raw, str):
                continue

            # Prefer split parsing to preserve indentation after the colon.
            try:
                left, right = raw.split(":", 1)
                ln = int(left.strip())
                code = right.rstrip("\r\n")
                saw_any_tagged = True
                decomp_map.setdefault(ln, code)
                continue
            except Exception:
                pass

            untagged_fallback.append(raw.rstrip("\r\n"))

    if saw_any_tagged and decomp_map:
        return [decomp_map[ln] for ln in sorted(decomp_map)]

    if untagged_fallback:
        return untagged_fallback

    # Function existed, but no usable lines => empty decomp
    return []


def _strip_decmap_prefix_if_present(lines: List[str]) -> List[str]:
    if not lines:
        return lines

    if not any(isinstance(s, str) and _RE_DECMAP_PREFIX.match(s) for s in lines[:25]):
        return lines

    out: List[str] = []
    for s in lines:
        if not isinstance(s, str):
            out.append(s)
            continue
        m = _RE_DECMAP_PREFIX.match(s)
        out.append((m.group(1) if m else s).rstrip("\r\n"))
    return out


def _get_function_name(oid: str, offset: Any) -> Optional[str]:
    addr = _parse_addr_any(offset)
    if addr is None:
        return None
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    return funcs.get(addr, {}).get("name")