"""spilled-parameter oracle: a stack slot the prologue copies an argument register into is that
parameter's home and shares its type."""
from __future__ import annotations

import json
import re
from .common import _REGNAME_TO_ARG, _SPILL_STORE, _decl_pointer_map, _is_vague_pointer, _libc_type_of_param, _vid_stack_offsets


def spilled_param_facts(call_tool, question) -> list:
    """A stack slot that the prologue spills an ARGUMENT REGISTER into is a copy of that parameter, so
    it has that parameter's type. Resolve slot -> register (stack_var's first store) -> SysV parameter
    -> the parameter's type (the decompiler's declared pointer type, else its library-ABI type). This
    fixes the common failure where the model mis-maps a spilled local to the WRONG parameter and
    inherits the wrong type. Returns (vid, ctype, param, register) tuples."""
    m = re.search(r"at\s+(?:vaddr\s+)?(0x[0-9a-fA-F]+)", question or "")
    if not m:
        return []
    addr = m.group(1)
    slots = _vid_stack_offsets(question)
    if not slots:
        return []
    try:
        dec = call_tool("decompile", {"addr": addr})
    except Exception:  # noqa: BLE001
        return []
    if not isinstance(dec, str) or dec.startswith("(no"):
        return []
    decl = _decl_pointer_map(dec)
    facts = []
    for vid, off in slots.items():
        try:
            sv = call_tool("stack_var", {"addr": addr, "offset": off})
        except Exception:  # noqa: BLE001
            continue
        if not isinstance(sv, str):
            continue
        sm = _SPILL_STORE.search(sv)                         # first store = the prologue spill
        k = _REGNAME_TO_ARG.get(sm.group(1)) if sm else None
        if not k:
            continue
        pname = f"param_{k}"
        ctype = decl.get(pname) or (_libc_type_of_param(dec, pname) or (None,))[0]
        if ctype:
            facts.append((vid, ctype, pname, sm.group(1)))
    return facts


def _oracle_spilled_param(call_tool, question) -> list:
    out = []
    for vid, ctype, pname, reg in spilled_param_facts(call_tool, question):
        out.append({
            "vid": vid, "ctype": ctype, "source": "deterministic_spilled_param",
            "floor": _is_vague_pointer(ctype),
            "claim": (f"{vid} has C type `{ctype}` — its stack slot is where the prologue spills "
                      f"`{reg}` (`{pname}`), so it is a copy of that parameter and shares its type. "
                      f"Treat as established; this overrides a guess that mis-maps the slot to another "
                      f"parameter."),
            "reason": f"prologue spills {reg} ({pname}) into this slot"})
    return out
