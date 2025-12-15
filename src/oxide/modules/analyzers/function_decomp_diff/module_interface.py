# -*- coding: utf-8 -*-
"""
function_decomp_diff — unified diff with target-centric call syncing + post-diff annotations.

Pipeline:
  1) Get baseline/target decompiler text.
  2) Build call pairing from function_call_diff (target-centric labels).
  3) Normalize both sides to stable labels (for alignment).
  4) Align with SequenceMatcher to get opcodes.
  5) Infer baseline→target label and variable/local/DAT/PTR mappings from
     normalized equal lines, and project baseline names into the target namespace.
  6) Project baseline FUN_<addr> tokens to the target FUN_<addr> tokens (for ORIGINAL emission).
     - Handles potential image-base bias between "FUN_000xxxxx" vs "FUN_001xxxxx".
  7) Emit unified diff with replace-refinement to collapse identical lines to context.
  8) Post-process the unified diff to append inline comments ONLY on '+' lines for any
     known *target* function calls found on those lines. Tags are fetched via:
         api.get_field("llm_function_analysis", target_oid, "tag", {"func_offset": addr})

Notes:
  • The post-diff annotation step guarantees annotations don't perturb alignment.
  • If a line contains multiple known calls, all are listed in a single trailing comment.
"""

DESC = ""
NAME = "function_decomp_diff"

import logging
import re
from difflib import SequenceMatcher
from typing import Dict, Any, List, Optional, Tuple

from oxide.core import api


logger = logging.getLogger(NAME)
logger.debug("init")

# ---------------------------
# LLM context sizing (approx)
# ---------------------------

_LLM_NUM_CTX_TOKENS = 8192
_LLM_RESERVED_TOKENS = 1024  # system prompt, JSON wrapper, metadata, response, etc.
_APPROX_CHARS_PER_TOKEN = 4  # rough heuristic: 1 token ≈ 4 chars

_MAX_UNIFIED_CHARS = (
    _LLM_NUM_CTX_TOKENS - _LLM_RESERVED_TOKENS
) * _APPROX_CHARS_PER_TOKEN

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
    "normalize": {"type": bool, "mangle": True, "default": True},
    "compact": {"type": bool, "mangle": True, "default": True},
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

# Additional Ghidra-style variable families
_RE_PARAM = re.compile(r"\bparam_[0-9A-Fa-f]+\b")
_RE_IN = re.compile(r"\bin_[A-Za-z0-9_]+\b")  # in_FS_OFFSET, in_stack_...
_RE_EXTRAOUT = re.compile(r"\bextraout_[A-Za-z0-9_]+\b")
_RE_UNAFF = re.compile(r"\bunaff_[A-Za-z0-9_]+\b")

_RE_WS = re.compile(r"\s+")

_FUN_TOKEN_RE = re.compile(r"\bFUN_([0-9a-fA-F]+)\b")

# Variable-like tokens (locals, temps, DAT_*, PTR_*, params, in_*, extraout_*, unaff_*)
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


def _lines_equal_ignoring_ws(a: List[str], b: List[str]) -> bool:
    """
    Return True if two lists of lines are identical up to whitespace.

    Used to double-check 'equal' blocks from normalized alignment against the
    ORIGINAL text (base_proj vs tgt_orig). This prevents canonical alignment
    from hiding real semantic changes like iVar6 -> iVar7.
    """
    if len(a) != len(b):
        return False
    for x, y in zip(a, b):
        if _RE_WS.sub(" ", x).strip() != _RE_WS.sub(" ", y).strip():
            return False
    return True


# ---------------------------
# Public entry
# ---------------------------


def results(oid_list: List[str], opts: dict) -> Dict[str, Any]:
    oid_list = api.expand_oids(oid_list)
    if not oid_list or len(oid_list) < 2:
        raise ValueError(
            "function_decomp_diff requires two OIDs: [target_oid, baseline_oid]"
        )

    target_oid, baseline_oid = oid_list[0], oid_list[1]
    target_addr = opts["target"]
    baseline_addr = opts["baseline"]

    # ORIGINAL decompiler lines (no trailing newlines)
    tgt_orig = retrieve_function_decomp_lines(target_oid, target_addr)
    base_orig = retrieve_function_decomp_lines(baseline_oid, baseline_addr)
    if not tgt_orig or not base_orig:
        return {
            "error": "Could not retrieve function decomp lines for one or both sides."
        }

    # Normalize (for alignment) using stable labels shared by both sides
    if opts.get("normalize", True):
        base_norm = _normalize_lines(base_orig)
        tgt_norm = _normalize_lines(tgt_orig)
    else:
        base_norm = base_orig
        tgt_norm = tgt_orig

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

    # Project baseline ORIGINAL lines:
    #   1) FUN_ tokens -> target-side FUN_ tokens
    #   2) LAB_ tokens -> target-side LAB_ tokens for unchanged blocks
    #   3) variable-like tokens -> target-side names
    base_proj = _project_fun_tokens(base_orig, projmap_base)
    base_proj = _project_lab_tokens(base_proj, lab_map)
    base_proj = _project_var_tokens(base_proj, var_map)

    # Headers
    a_len = len(base_orig)
    b_len = len(tgt_orig)
    a_start_disp = 1 if a_len else 0
    b_start_disp = 1 if b_len else 0

    fn_b = _get_function_name(baseline_oid, baseline_addr) or f"{baseline_addr}"
    fn_t = _get_function_name(target_oid, target_addr) or f"{target_addr}"
    fromfile = f"{fn_b} (baseline {baseline_oid})"
    tofile = f"{fn_t} (target   {target_oid})"

    # Emit ORIGINAL with replace-refinement
    out: List[str] = [
        f"--- {fromfile}",
        f"+++ {tofile}",
        f"@@ -{a_start_disp},{a_len} +{b_start_disp},{b_len} @@",
    ]

    for tag, i1, i2, j1, j2 in opcodes:
        base_slice = base_proj[i1:i2]
        tgt_slice = tgt_orig[j1:j2]

        if tag == "equal":
            # Alignment was done on NORMALIZED text (with <TMP> etc.),
            # so 'equal' may hide real changes like iVar6 -> iVar7.
            # Only treat as unchanged context if the ORIGINAL slices really match.
            if _lines_equal_ignoring_ws(base_slice, tgt_slice):
                for s in base_slice:
                    out.append(" " + s)
            else:
                _emit_refined(out, base_slice, tgt_slice)
        else:
            _emit_refined(out, base_slice, tgt_slice)

    unified = "\n".join(out) + ("\n" if out else "")

    # ---------------------------
    # Post-diff annotation (added lines)
    # ---------------------------
    if opts.get("annotate", False):
        name_to_addr = _get_function_calls(
            target_oid, baseline_oid, target_addr, baseline_addr
        )
        if name_to_addr:
            unified = _annotate_unified_with_tags(
                unified,
                name_to_addr,
                target_oid,
                annotate_kinds=("+",),  # annotate only additions by default
            )

    # ---------------------------
    # LLM-oriented compaction to stay within context window
    # ---------------------------
    unified_full = unified
    unified_compact = _maybe_compact_unified(
        unified_full, max_chars=_LLM_DIFF_CHAR_BUDGET
    )

    if opts.get("compact", True):
        unified = unified_compact
    else:
        unified = unified_full

    result = {
        "unified": unified,
        "meta": {
            "baseline_func": fn_b,
            "baseline_oid": baseline_oid,
            "target_func": fn_t,
            "target_oid": target_oid,
            "normalized_alignment": bool(opts.get("normalize", True)),
            "unified_full_len": len(unified_full),
            "unified_compact_len": len(unified_compact),
            "unified_truncated": len(unified_compact) < len(unified_full),
        },
    }

    return result


# ---------------------------
# Label + variable mapping helpers
# ---------------------------


def _build_lab_map_from_opcodes(
    base_orig: List[str],
    tgt_orig: List[str],
    opcodes: List[Tuple[str, int, int, int, int]],
) -> Dict[str, str]:
    """
    Infer a mapping from baseline label tokens to target label tokens:
        { "LAB_0010e455": "LAB_0010e44e", ... }

    We only learn mappings inside opcodes tagged 'equal' on the *normalized*
    text. For those regions, we assume the control-flow block is the same and
    any LAB_ differences are just renumberings.
    """
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
                    # Conflict: safest is to drop this mapping entirely.
                    lab_map.pop(bl, None)

    return lab_map


def _project_lab_tokens(lines: List[str], lab_map: Dict[str, str]) -> List[str]:
    """
    Rewrite LAB_<addr> tokens in `lines` according to `lab_map`, e.g.:

        LAB_0010e455  ->  LAB_0010e44e

    This is applied after FUN_ projection so unchanged basic blocks that only
    differ by label numbers collapse to context in the unified diff.
    """
    if not lab_map:
        return lines

    def _sub(m: re.Match) -> str:
        lab = m.group(0)  # full token, e.g. "LAB_0010e455"
        return lab_map.get(lab, lab)

    return [_RE_LAB.sub(_sub, s) for s in lines]


def _extract_var_tokens(line: str) -> List[str]:
    """
    Extract ordered variable-like tokens from a line:
    locals, temps, DAT_*, PTR_*, params, in_*, extraout_*, unaff_*.
    """
    return [m.group(0) for m in _VAR_TOKEN_RE.finditer(line)]


def _same_var_kind(a: str, b: str) -> bool:
    """
    Only allow mappings within the same broad kind:
      - local_*       -> local_*
      - p*/i*/pc*/... -> same temp family
      - DAT_*         -> DAT_*
      - PTR_*         -> PTR_*
      - param_*       -> param_*
      - in_*          -> in_*
      - extraout_*    -> extraout_*
      - unaff_*       -> unaff_*
    """
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
    """
    Infer a mapping from baseline variable/local/DAT/PTR/etc. names to target names
    based on lines that match after normalization.

    Returns:
        var_map: { baseline_name -> target_name }
    """
    pair_counts: Dict[Tuple[str, str], int] = {}

    for tag, i1, i2, j1, j2 in opcodes:
        if tag != "equal":
            continue

        length = i2 - i1
        for k in range(length):
            b_idx = i1 + k
            t_idx = j1 + k

            # Sanity: ensure normalized lines really match
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

    # Aggregate by baseline name and pick the most frequent target
    by_baseline: Dict[str, Dict[str, int]] = {}
    for (vb, vt), cnt in pair_counts.items():
        by_baseline.setdefault(vb, {})
        by_baseline[vb][vt] = by_baseline[vb].get(vt, 0) + cnt

    var_map: Dict[str, str] = {}

    for vb, tgt_counts in by_baseline.items():
        vt_best, c_best = max(tgt_counts.items(), key=lambda kv: kv[1])
        if c_best < _VAR_MAP_MIN_SUPPORT:
            continue
        var_map[vb] = vt_best

    return var_map


def _project_var_tokens(lines: List[str], var_map: Dict[str, str]) -> List[str]:
    """
    Replace baseline variable/local/DAT/PTR/etc. tokens using `var_map`.

    Assumes mapping is baseline_name -> target_name. Does not change line count.
    """
    if not var_map:
        return lines

    keys = sorted(var_map.keys(), key=len, reverse=True)
    pattern = r"\b(" + "|".join(re.escape(k) for k in keys) + r")\b"
    re_keys = re.compile(pattern)

    def _sub(m):
        vb = m.group(1)
        return var_map.get(vb, vb)

    out: List[str] = []
    for s in lines:
        out.append(re_keys.sub(_sub, s))
    return out


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


def _sanitize_name(name: str) -> str:
    name = name.strip()
    name = re.sub(r"\s+", "_", name)
    name = re.sub(r"[^A-Za-z0-9_.$@+-]", "", name)
    return name or "unknown"


def _target_pref_label(
    b_name: Optional[str], t_name: Optional[str], t_tok: Optional[str]
) -> str:
    nm = (t_name or b_name or "").strip()
    if nm:
        return _sanitize_name(nm)
    return t_tok or "FUN_<UNKNOWN>"


def _build_maps(
    baseline_oid: str, target_oid: str, baseline_func_addr: Any, target_func_addr: Any
) -> Dict[str, str]:
    """
    Returns:
        projmap_base: baseline FUN_token -> target FUN_token (projection for ORIGINAL)
    """
    projmap_base: Dict[str, str] = {}

    # Seed with the function itself so the def-line syncs.
    base_tok = _tok_from_any(baseline_func_addr)
    tgt_tok = _tok_from_any(target_func_addr)
    tgt_name = _get_function_name(target_oid, target_func_addr)
    _ = _target_pref_label(None, tgt_name, tgt_tok)  # label_fn (currently unused)
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

        if not (b_tok or t_tok):
            continue

        if b_tok and t_tok:
            projmap_base[b_tok] = t_tok

    return projmap_base


# ---------------------------
# Projection / Normalization
# ---------------------------


def _project_fun_tokens(lines: List[str], projmap: Dict[str, str]) -> List[str]:
    """
    Replace FUN_<addr> in `lines` using `projmap`, handling possible image-base bias
    (e.g., code shows FUN_001xxxxx while map has FUN_000xxxxx).
    """
    # Build int->int map like {0x00013400: 0x0001340f}
    num_map: Dict[int, int] = {}
    for k, v in projmap.items():
        try:
            num_map[int(k[4:], 16)] = int(v[4:], 16)
        except Exception:
            pass  # skip malformed

    # Infer a likely bias by seeing which candidate aligns most tokens
    candidates = (0, 0x100000, 0x200000, -0x100000, 0x1000, -0x1000)
    seen: list[int] = []
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
            # Count how many observed addresses align under this bias
            hits = sum(1 for a in seen if (a - b) in num_map)
            if hits > best_hits:
                best_hits = hits
                bias = b

    def _sub(m):
        a = int(m.group(1), 16)
        if a in num_map:
            return f"FUN_{num_map[a]:08x}"
        ab = a - bias
        if ab in num_map:
            return f"FUN_{(num_map[ab] + bias):08x}"
        return f"FUN_{a:08x}"

    return [_RE_FUN.sub(_sub, s) for s in lines]


def _normalize_lines(lines: List[str]) -> List[str]:
    out: List[str] = []
    for s in lines:
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
# Replace refinement (collapse identical pairs inside replace blocks)
# ---------------------------


def _emit_refined(out: List[str], base_slice: List[str], tgt_slice: List[str]) -> None:
    """
    Refine a replace hunk: if lines are equal (or equal ignoring whitespace), emit as context.
    Otherwise, emit -/+ as usual. Keeps delete/insert behavior for unequal-length slices.
    """
    if not base_slice and not tgt_slice:
        return

    if len(base_slice) == len(tgt_slice) and len(base_slice) > 0:

        def squash_ws(s: str) -> str:
            return _RE_WS.sub(" ", s).strip()

        all_equal = True
        for b, t in zip(base_slice, tgt_slice):
            if b == t or squash_ws(b) == squash_ws(t):
                continue
            all_equal = False
            break
        if all_equal:
            for t in tgt_slice:
                out.append(" " + t)
            return

    sm = SequenceMatcher(
        None,
        [s + "\n" for s in base_slice],
        [s + "\n" for s in tgt_slice],
        autojunk=False,
    )
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            for s in base_slice[i1:i2]:
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
                if b == t:
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
    """
    Normalize to: { name: addr_int }
    Accepts:
      - dict addr->name   (we invert)
      - dict name->addr   (direct, supports str/int values)
      - list of {name, addr}
      - list of names (names like FUN_XXXXXXXX will be parsed to addr)
    """
    if obj is None:
        return None

    out: Dict[str, int] = {}

    # dict path
    if isinstance(obj, dict):
        # Heuristics: if keys look numeric/hex -> treat as addr->name and invert
        numeric_like_keys = True
        for k in obj.keys():
            if not isinstance(k, (int,)) and not (
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
            return out

        # Otherwise assume name->addr
        for n, a in obj.items():
            if not isinstance(n, str) or not n:
                continue
            addr = _parse_addr_any(a)
            if addr is None:
                # If it's a FUN_XXXXXX token, parse from name
                addr = _parse_addr_any(n)
            if addr is not None:
                out[n] = addr
        return out if out else None

    # list of dicts or names
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
        return out if out else None

    return None


def _get_function_calls(
    target_oid, baseline_oid, target_func, baseline_func
) -> Optional[Dict[str, int]]:
    """
    Fetch the precomputed list of *target* callees from function_call_diff,
    then normalize to { name: addr }.
    """
    diff = (
        api.retrieve(
            "function_call_diff",
            [target_oid, baseline_oid],
            {"target": str(target_func), "baseline": str(baseline_func)},
        )
        or {}
    )

    # Expected keys in your environment
    paired = diff.get("fc_paired") or []
    existing = diff.get("fc_add_existing") or []
    new = diff.get("fc_add_new") or []

    # Build addr->name first, then normalize to name->addr
    target_func_calls = {}
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


def _get_tag_for_addr(oid: str, addr: int) -> str | None:
    try:
        return api.get_field("llm_function_analysis", oid, "tag", {"func_offset": addr})
    except Exception:
        return None


def _annotate_unified_with_tags(
    unified: str,
    name_to_addr: dict[str, int],
    target_oid: str,
    annotate_kinds: tuple[str, ...] = ("+",),
) -> str:
    """
    Append short tags to diff lines whose first character is in `annotate_kinds`
    (by default, only '+' lines) and that contain calls to known *target* functions.
    '-' lines are left untouched.

    Example result:
      ' + FUN_00106126(x, y); // FUN_00106126: buffer pointer calculation'
    """
    if not unified or not name_to_addr:
        return unified

    # Pre-fetch tags once
    name_to_tag: dict[str, str | None] = {
        name: _get_tag_for_addr(target_oid, addr) for name, addr in name_to_addr.items()
    }

    # Regex that matches any known function name followed by '('
    names_sorted = sorted(name_to_addr.keys(), key=len, reverse=True)
    if not names_sorted:
        return unified
    call_pat = re.compile(
        r"\b(" + "|".join(re.escape(n) for n in names_sorted) + r")\b\s*\("
    )

    out_lines: list[str] = []
    for line in unified.splitlines():
        # Keep diff/file headers verbatim
        if line.startswith(("---", "+++", "@@")):
            out_lines.append(line)
            continue

        if not line or line[0] not in annotate_kinds:
            out_lines.append(line)
            continue

        prefix, body = line[0], line[1:]

        # Avoid altering existing code before '//'; annotate after it
        code_part, sep, trailing = body.partition("//")

        # Find function calls only in the code portion
        matches = [m.group(1) for m in call_pat.finditer(code_part)]
        if not matches:
            out_lines.append(line)
            continue

        # Deduplicate preserving order
        seen: list[str] = []
        for n in matches:
            if n not in seen:
                seen.append(n)

        # Build comment fragments: "name: tag" if tag exists, else just name
        fragments: list[str] = []
        for n in seen:
            tag = name_to_tag.get(n)
            fragments.append(f"{n}: {tag}" if tag else n)

        # If there's already a trailing comment and it already contains all fragments, skip
        if sep and all(fragment in trailing for fragment in fragments):
            out_lines.append(line)
            continue

        annotated = prefix + code_part
        if sep:  # preserve original trailing comment
            annotated += sep + trailing
        # append our annotation comment
        annotated += " // " + "; ".join(fragments)

        out_lines.append(annotated)

    return "\n".join(out_lines) + ("\n" if out_lines else "")


def _extract_changed_regions(unified: str, context_lines: int = 10) -> str:
    """
    Keep only +/- lines (changes) plus a small number of surrounding context lines,
    along with file and hunk headers. Insert '...' markers where unchanged regions
    are omitted. Used as a building block for LLM-oriented compaction.
    """
    lines = unified.splitlines()
    n = len(lines)
    if n == 0:
        return unified

    keep: set[int] = set()

    # Always keep all hunk headers
    for i, line in enumerate(lines):
        if line.startswith(("@@",)):
            keep.add(i)

    # Mark regions around changed lines
    for i, line in enumerate(lines):
        if not line:
            continue

        # Skip file headers (already handled)
        if line.startswith(("---", "+++")):
            keep.add(i)
            continue

        # Changed lines: leading '+' or '-' (but not '+++' / '---' headers)
        prefix = line[0]
        if prefix in ("+", "-"):
            start = max(0, i - context_lines)
            end = min(n, i + context_lines + 1)
            for j in range(start, end):
                keep.add(j)

    if not keep:
        # No obvious changes detected; return original
        return unified

    new_lines: list[str] = []
    last_idx = -1
    for idx in sorted(keep):
        if last_idx != -1 and idx > last_idx + 1:
            # Indicate omitted block
            new_lines.append("...")
        new_lines.append(lines[idx])
        last_idx = idx

    return "\n".join(new_lines) + ("\n" if new_lines else "")


def _maybe_compact_unified(unified: str, max_chars: int = _MAX_UNIFIED_CHARS) -> str:
    """
    Shrink `unified` to fit within `max_chars` by keeping changed lines plus
    as much surrounding context as possible. We start with a large context
    window and decrease it until we fit. Final fallback: keep both the
    beginning and the end of the compacted diff (headers + epilogue) and
    drop only the middle.
    """
    if not unified:
        return unified

    # Use the stricter of our global max and the explicit budget for this call
    budget = min(max_chars, _LLM_DIFF_CHAR_BUDGET)

    # If the whole thing fits, don't touch it
    if len(unified) <= budget:
        return unified

    # Try progressively smaller context windows until we fit
    compact = unified
    for ctx in _COMPACTION_CTX_CANDIDATES:
        compact = _extract_changed_regions(compact, context_lines=ctx)
        if len(compact) <= budget:
            return compact

    # ------------------------------------------------------------------
    # Fallback: even smallest context is too big.
    # At this point, `compact` is a version that keeps only changed lines.
    # We must hard truncate, but we do it by keeping BOTH head and tail
    # so that function epilogues (e.g., `return` lines) are preserved.
    # ------------------------------------------------------------------
    lines = compact.splitlines()
    note = "... [diff truncated to fit LLM context]"
    note_len = len(note) + 1  # account for '\n'

    # If the budget is tiny, just return the note once
    if budget <= 2 * note_len:
        return note + "\n"

    # Reserve space for the note at top and bottom
    remaining_budget = budget - 2 * note_len

    # We will split remaining_budget roughly evenly between prefix and suffix.
    target_each = remaining_budget // 2

    # Collect prefix lines from the top
    prefix_lines: list[str] = []
    prefix_chars = 0
    for line in lines:
        line_len = len(line) + 1  # + '\n'
        if prefix_chars + line_len > target_each:
            break
        prefix_lines.append(line)
        prefix_chars += line_len

    # Collect suffix lines from the bottom
    suffix_lines_rev: list[str] = []
    suffix_chars = 0
    for line in reversed(lines):
        line_len = len(line) + 1
        if suffix_chars + line_len > target_each:
            break
        suffix_lines_rev.append(line)
        suffix_chars += line_len

    suffix_lines = list(reversed(suffix_lines_rev))

    # If the prefix and suffix overlap heavily (short file), just use compact
    if len("\n".join(lines)) <= remaining_budget:
        result_lines = [note] + lines + [note]
        return "\n".join(result_lines) + "\n"

    # Assemble: note at top, prefix, ellipsis, suffix, note at bottom
    result_lines: list[str] = [note]
    result_lines.extend(prefix_lines)
    result_lines.append("...")  # explicit middle truncation marker
    result_lines.extend(suffix_lines)
    result_lines.append(note)

    return "\n".join(result_lines) + "\n"


# ---------------------------
# Ghidra helpers
# ---------------------------


def retrieve_function_decomp_lines(oid: str, func_addr: Any) -> Optional[List[str]]:
    func_name = _get_function_name(oid, func_addr)
    if not func_name:
        return None

    decmap = api.retrieve("ghidra_decmap", [oid], {"org_by_func": True})
    if not decmap:
        return None

    dm = decmap
    if isinstance(decmap, dict) and oid in decmap and isinstance(decmap[oid], dict):
        dm = decmap[oid]

    func_blocks = (dm.get("decompile") or {}).get(func_name)
    if not func_blocks:
        return None

    decomp_map: Dict[int, str] = {}
    for _block_id, block in func_blocks.items():
        lines = block.get("line", [])
        for line in lines:
            split = line.find(": ")
            if split <= 0:
                continue
            try:
                ln = int(line[:split])
                code = line[split + 2 :]
                decomp_map[ln] = code
            except Exception:
                continue

    if not decomp_map:
        return None

    out: List[str] = []
    indent = 0
    for ln in sorted(decomp_map):
        code = decomp_map[ln]
        if "}" in code:
            indent -= 1
        out.append(("    " * max(indent, 0)) + code)
        if "{" in code:
            indent += 1

    return out


def _get_function_name(oid: str, offset: Any) -> Optional[str]:
    addr = _parse_addr_any(offset)
    if addr is None:
        return None
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    return funcs.get(addr, {}).get("name")
