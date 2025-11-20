# -*- coding: utf-8 -*-
"""
function_decomp_diff — unified diff with target-centric call syncing + post-diff annotations.

Pipeline:
  1) Get baseline/target decompiler text.
  2) Build call pairing from function_call_diff (target-centric labels).
  3) Project baseline FUN_<addr> tokens to the target FUN_<addr> tokens (for ORIGINAL emission).
     - Handles potential image-base bias between "FUN_000xxxxx" vs "FUN_001xxxxx".
  4) Normalize both sides to stable labels (for alignment).
  5) Align with SequenceMatcher; refine "replace" hunks to collapse identical lines to context.
  6) Post-process the unified diff to append inline comments ONLY on '+' lines for any
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

_LLM_DIFF_CHAR_BUDGET = 7500

# ---------------------------
# Options
# ---------------------------

opts_doc = {
    "target": {"type": str, "mangle": True, "default": "None"},
    "baseline": {"type": str, "mangle": True, "default": "None"},
    "annotate": {"type": bool, "mangle": True, "default": False},
    "normalize": {"type": bool, "mangle": True, "default": True},
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
_RE_TMP = re.compile(
    r"\b(?:[iu]Var\d+|bVar\d+|pcVar\d+|pvVar\d+|sVar\d+|lVar\d+|uVar\d+|plVar\d+)\b"
)
_RE_LOCAL = re.compile(r"\blocal_[A-Za-z0-9_]+\b")
_RE_WS = re.compile(r"\s+")

_FUN_TOKEN_RE = re.compile(r"\bFUN_([0-9a-fA-F]+)\b")


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

    # Build projection + normalization maps from call diff
    projmap_base = _build_maps(baseline_oid, target_oid, baseline_addr, target_addr)

    # Project baseline ORIGINAL lines so its calls (and header) use target FUN tokens
    base_proj = _project_fun_tokens(base_orig, projmap_base)

    # Normalize (for alignment) using stable labels shared by both sides
    if opts["normalize"]:
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
        if tag == "equal":
            for s in base_proj[i1:i2]:
                out.append(" " + s)
        else:
            _emit_refined(out, base_proj[i1:i2], tgt_orig[j1:j2])

    unified = "\n".join(out) + ("\n" if out else "")

    # ---------------------------
    # Post-diff annotation (context/addition/deletion lines)
    # ---------------------------
    if opts.get("annotate", True):
        name_to_addr = _get_function_calls(
            target_oid, baseline_oid, target_addr, baseline_addr
        )
        if name_to_addr:
            unified = _annotate_unified_with_tags(
                unified,
                name_to_addr,
                target_oid,
                annotate_kinds=(" ", "+", "-"),
            )

    # ---------------------------
    # LLM-oriented compaction to stay within context window
    # ---------------------------
    unified_full = unified
    unified_compact = _maybe_compact_unified(
        unified_full, max_chars=_LLM_DIFF_CHAR_BUDGET
    )

    result = {
        "unified": unified_compact,
        "meta": {
            "baseline_func": fn_b,
            "baseline_oid": baseline_oid,
            "target_func": fn_t,
            "target_oid": target_oid,
            "normalized_alignment": True,
            "unified_full_len": len(unified_full),
            "unified_compact_len": len(unified_compact),
            "unified_truncated": len(unified_compact) < len(unified_full),
        },
    }

    return result


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
) -> Tuple[Dict[str, str], Dict[str, str], Dict[str, str]]:
    """
    Returns:
        projmap_base: baseline FUN_token -> target FUN_token (projection for ORIGINAL)
    """
    projmap_base: Dict[str, str] = {}
    normmap_base: Dict[str, str] = {}
    normmap_tgt: Dict[str, str] = {}

    # Seed with the function itself so the def-line syncs.
    base_tok = _tok_from_any(baseline_func_addr)
    tgt_tok = _tok_from_any(target_func_addr)
    tgt_name = _get_function_name(target_oid, target_func_addr)
    label_fn = _target_pref_label(None, tgt_name, tgt_tok)
    if base_tok and tgt_tok:
        projmap_base.setdefault(base_tok, tgt_tok)
    if base_tok:
        normmap_base.setdefault(base_tok, label_fn)
    if tgt_tok:
        normmap_tgt.setdefault(tgt_tok, label_fn)

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
            hits = sum(1 for a in seen if (a in num_map) or ((a - b) in num_map))
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
        # s = _RE_OFF.sub("OFF_<ADDR>", s)
        # s = _RE_HEX.sub("<NUM>", s)
        # s = _RE_NUM.sub("<NUM>", s)
        s = _RE_TMP.sub("<TMP>", s)
        s = _RE_LOCAL.sub("<LOCAL>", s)
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

    # Build addr->name first (as you outlined), then normalize to name->addr
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


_tag_cache: Dict[Tuple[str, int], Optional[str]] = {}


def _get_tag_for_addr(oid: str, addr: int) -> str | None:
    try:
        return api.get_field("llm_function_analysis", oid, "tag", {"func_offset": addr})
    except Exception:
        return None


def _annotate_unified_with_tags(
    unified: str,
    name_to_addr: dict[str, int],
    target_oid: str,
    annotate_kinds: tuple[str, ...] = (
        " ",
        "+",
        "-",
    ),  # annotate context and additions; skip deletions
) -> str:
    """
    Append short tags to lines that start with ' ' or '+' and that contain calls
    to known *target* functions. '-' lines are left untouched.

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


def _extract_changed_regions(unified: str, context_lines: int = 3) -> str:
    """
    Keep only +/- lines (changes) plus a small number of surrounding context lines
    and all hunk/file headers. Insert "..." between disjoint kept regions.
    Intended for LLM consumption only (not for patch application).
    """
    lines = unified.splitlines()
    n = len(lines)
    if n == 0:
        return unified

    keep: set[int] = set()

    # Always keep initial headers if present
    for i, line in enumerate(lines[:5]):
        if line.startswith(("---", "+++", "@@")):
            keep.add(i)

    # Always keep all hunk headers
    for i, line in enumerate(lines):
        if line.startswith("@@"):
            keep.add(i)

    # Mark regions around changed lines
    for i, line in enumerate(lines):
        if not line:
            continue

        # Skip file/hunk headers (already handled)
        if line.startswith(("---", "+++", "@@")):
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
    If `unified` is too large for the LLM context budget, shrink it to focus on
    changed lines plus limited context. Final fallback: hard truncate at a line
    boundary and add a note.
    """
    if not unified or len(unified) <= max_chars:
        return unified

    # First pass: changed lines + a few context lines
    compact = _extract_changed_regions(unified, context_lines=3)
    if len(compact) <= max_chars:
        return compact

    # Second pass: changed lines only (no extra context)
    compact = _extract_changed_regions(unified, context_lines=0)
    if len(compact) <= max_chars:
        return compact

    # Final fallback: hard truncate at line boundary
    lines = compact.splitlines()
    out_lines: list[str] = []
    total = 0
    for line in lines:
        line_len = len(line) + 1  # + '\n'
        if total + line_len > max_chars:
            break
        out_lines.append(line)
        total += line_len

    out_lines.append("... [diff truncated to fit LLM context]")
    return "\n".join(out_lines) + ("\n" if out_lines else "")


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
    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    return funcs.get(int(offset), {}).get("name")
