# -*- coding: utf-8 -*-
"""
Build unified diff text from opcodes and compact it for LLM context budgets.

Two sub-responsibilities:
  Emit    — convert SequenceMatcher opcodes into unified diff lines, with
            canonical-noise collapsing so trivial token changes appear as context.
  Compact — strip context aggressively and hard-truncate when the diff exceeds
            the LLM character budget.
"""

import re
from difflib import SequenceMatcher
from typing import List, Optional

from align import apply_standard_subs, RE_WS

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

_LLM_NUM_CTX_TOKENS = 8192
_LLM_RESERVED_TOKENS = 2048
_APPROX_CHARS_PER_TOKEN = 3.0

LLM_DIFF_CHAR_BUDGET = min(
    (_LLM_NUM_CTX_TOKENS - _LLM_RESERVED_TOKENS) * _APPROX_CHARS_PER_TOKEN,
    20000,
)

_COMPACTION_CTX_CANDIDATES = (100, 50, 25, 10, 7, 5, 3, 1, 0)

# ---------------------------------------------------------------------------
# Canonical noise collapsing (for equal-block suppression)
# ---------------------------------------------------------------------------

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


def canon_decomp_noise(s: str) -> str:
    """Aggressively canonicalize a line to detect semantic equality despite token noise."""
    s = apply_standard_subs(s)
    s = _RE_TYPE.sub("<TYPE>", s)
    s = _RE_PARENRUN.sub("()", s)
    s = RE_WS.sub(" ", s).strip()
    return s


def lines_equal_canon(a: List[str], b: List[str]) -> bool:
    if len(a) != len(b):
        return False
    return all(canon_decomp_noise(x) == canon_decomp_noise(y) for x, y in zip(a, b))


def _canon_block(lines: List[str]) -> str:
    return " ".join(canon_decomp_noise(x) for x in lines)


# ---------------------------------------------------------------------------
# Diff emitters
# ---------------------------------------------------------------------------

def make_sequence_matcher(base_lines: List[str], tgt_lines: List[str]) -> SequenceMatcher:
    return SequenceMatcher(
        None,
        [l + "\n" for l in base_lines],
        [l + "\n" for l in tgt_lines],
        autojunk=False,
    )


def emit_unified_header(fromfile: str, tofile: str, a_len: int, b_len: int) -> List[str]:
    a_start_disp = 1 if a_len else 0
    b_start_disp = 1 if b_len else 0
    return [
        f"--- {fromfile}",
        f"+++ {tofile}",
        f"@@ -{a_start_disp},{a_len} +{b_start_disp},{b_len} @@",
    ]


def emit_unified_raw(base_lines: List[str], tgt_lines: List[str], fromfile: str, tofile: str) -> str:
    out: List[str] = emit_unified_header(fromfile, tofile, len(base_lines), len(tgt_lines))
    sm = make_sequence_matcher(base_lines, tgt_lines)

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


def emit_refined(out: List[str], base_slice: List[str], tgt_slice: List[str]) -> None:
    """
    Emit a diff block with intra-block refinement: collapse lines that are
    canon-equal (differ only in noise tokens) to context lines.
    """
    if not base_slice and not tgt_slice:
        return

    if _canon_block(base_slice) == _canon_block(tgt_slice):
        for t in tgt_slice:
            out.append(" " + t)
        return

    base_keys = [canon_decomp_noise(s) + "\n" for s in base_slice]
    tgt_keys = [canon_decomp_noise(s) + "\n" for s in tgt_slice]

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
                if base_keys[i1 + kidx] == tgt_keys[j1 + kidx]:
                    out.append(" " + t)
                else:
                    out.append("-" + b)
                    out.append("+" + t)
            for s in base_slice[i1 + k:i2]:
                out.append("-" + s)
            for s in tgt_slice[j1 + k:j2]:
                out.append("+" + s)


# ---------------------------------------------------------------------------
# LLM compaction
# ---------------------------------------------------------------------------

# Matches pure variable-declaration lines — these are filtered out during
# compaction since they carry no semantic diff signal.
_DECL_LINE_RE = re.compile(
    r"^\s*(?:"
    r"undefined\d*|int|uint|long|ulong|short|ushort|char|uchar|bool|size_t|FILE|"
    r"__uid_t|__gid_t|void\s*\*"
    r")\b.*;\s*$"
)


def _extract_changed_regions(lines: List[str], context_lines: int = 10) -> str:
    """
    Strip context lines down to `context_lines` around each meaningful change.
    Pure declaration lines (+/-) are excluded from the "keep" set.
    Inserts "..." between omitted regions.
    """
    n = len(lines)
    if n == 0:
        return ""

    keep: set[int] = set()

    for i, line in enumerate(lines):
        if line.startswith(("---", "+++", "@@")):
            keep.add(i)
            continue
        if not line or line[0] not in ("+", "-"):
            continue
        if line.startswith(("---", "+++")):
            continue

        body = line[1:]
        if _DECL_LINE_RE.match(body):
            continue

        lo = max(0, i - context_lines)
        hi = min(n - 1, i + context_lines)
        for j in range(lo, hi + 1):
            keep.add(j)

    if not keep:
        return "\n".join(lines) + "\n"

    new_lines: List[str] = []
    last_idx = -1
    for idx in sorted(keep):
        if last_idx != -1 and idx > last_idx + 1:
            new_lines.append("...")
        new_lines.append(lines[idx])
        last_idx = idx

    return "\n".join(new_lines) + ("\n" if new_lines else "")


def maybe_compact_unified(unified: str, max_chars: int = LLM_DIFF_CHAR_BUDGET) -> str:
    """
    Compact a unified diff to fit within `max_chars`.
    Tries progressively smaller context windows first, then falls back to
    hard-truncating the middle while preserving head and tail.
    """
    if not unified or len(unified) <= max_chars:
        return unified

    # Pre-split once; _extract_changed_regions operates on the list.
    unified_lines = unified.splitlines()
    last_compact: Optional[str] = None
    for ctx in _COMPACTION_CTX_CANDIDATES:
        last_compact = _extract_changed_regions(unified_lines, context_lines=ctx)
        if len(last_compact) <= max_chars:
            return last_compact

    compact = last_compact or unified

    # Hard truncate: keep head and tail, drop the middle.
    lines = compact.splitlines()
    note = "... [diff truncated to fit LLM context]"
    note_len = len(note) + 1

    if max_chars <= 2 * note_len:
        return note + "\n"

    remaining = max_chars - 2 * note_len
    target_each = remaining // 2

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

    if len("\n".join(lines)) <= remaining:
        return "\n".join([note] + lines + [note]) + "\n"

    return "\n".join([note] + prefix_lines + ["..."] + suffix_lines + [note]) + "\n"
