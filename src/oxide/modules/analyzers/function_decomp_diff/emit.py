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
from typing import List

from align import apply_standard_subs, RE_WS

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
