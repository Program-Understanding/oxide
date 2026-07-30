"""decompiler-pointer oracle: adopt the decompiler's OWN recovered pointer type, which the model
routinely discards for a scalar guess."""
from __future__ import annotations

import json
import re
from .common import _vid_to_ghidra_name, _V_REGISTER, _V_STACK, _decl_pointer_map, _is_vague_pointer




def decompiler_pointer_facts(call_tool, question) -> list:
    """Parse the decompiler's OWN declared type for each queried variable and, when it declared a
    POINTER (char*/FILE*/T**), emit it. Storage resolves deterministically — a register by the calling
    convention, a stack slot -0xNN to Ghidra's `local_NN`. Returns a list of (vid, ctype) tuples."""
    m = re.search(r"at\s+(?:vaddr\s+)?(0x[0-9a-fA-F]+)", question or "")
    if not m:
        return []
    addr = m.group(1)
    vid_name = _vid_to_ghidra_name(question)
    if not vid_name:
        return []
    try:
        dec = call_tool("decompile", {"addr": addr})
    except Exception:  # noqa: BLE001
        return []
    if not isinstance(dec, str) or dec.startswith("(no"):
        return []
    decl = _decl_pointer_map(dec)
    return [(vid, decl[nm]) for vid, nm in vid_name.items() if nm in decl]


def _oracle_decompiler_pointer(call_tool, question) -> list:
    out = []
    for vid, ctype in decompiler_pointer_facts(call_tool, question):
        out.append({
            "vid": vid, "ctype": ctype, "source": "deterministic_decompiler_pointer",
            "floor": _is_vague_pointer(ctype),
            "claim": (f"{vid} has C type `{ctype}` — this is the decompiler's own recovered POINTER "
                      f"type for the variable. Treat as established; the decompiler's pointer "
                      f"inference overrides a scalar guess for {vid}."),
            "reason": "decompiler declared this a pointer type"})
    return out


