from __future__ import annotations

from difflib import SequenceMatcher
from typing import List

from text_tools import canon_block, canon_decomp_noise


def emit_refined(out: List[str], base_slice: List[str], tgt_slice: List[str]) -> None:
    if not base_slice and not tgt_slice:
        return

    if canon_block(base_slice) == canon_block(tgt_slice):
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
                if canon_decomp_noise(b) == canon_decomp_noise(t):
                    out.append(" " + t)
                else:
                    out.append("-" + b)
                    out.append("+" + t)
            for s in base_slice[i1 + k : i2]:
                out.append("-" + s)
            for s in tgt_slice[j1 + k : j2]:
                out.append("+" + s)
