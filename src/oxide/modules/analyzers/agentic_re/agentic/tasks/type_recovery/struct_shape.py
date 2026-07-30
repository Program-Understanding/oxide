"""struct-shape oracle: recover an aggregate's field layout from the offsets and widths the code
actually touches. Emits a SHAPE claim -- layout without a source-level name."""
from __future__ import annotations

import json
import re
from .common import _W2T, _vid_stack_offsets, _vid_to_arg


def _render_shape(fields: dict, selfrefs) -> str:
    """`{'0x0': 4, '0x8': 8}` + selfref `['0x8']` -> `struct t1 { int field_0; struct t1 *field_8; } *`.
    A self-referential aggregate is TAGGED (`t1`) because C cannot express recursion anonymously."""
    sr = set(selfrefs or ())
    parts = []
    for off_hex, w in sorted(fields.items(), key=lambda kv: int(kv[0], 16)):
        off = int(off_hex, 16)
        parts.append(f"struct t1 *field_{off}" if off_hex in sr
                     else f"{_W2T.get(w, 'long')} field_{off}")
    return f"struct {'t1 ' if sr else ''}{{ {'; '.join(parts)}; }} *"


def struct_shape_facts(call_tool, question) -> list:
    """Certify an aggregate pointer for a register parameter whose field accesses are observable, and
    for every slot that provably holds the same pointer (its prologue home, and any local assigned a
    self-referential field). Returns (vid, ctype, why) tuples."""
    m = re.search(r"at\s+(?:vaddr\s+)?(0x[0-9a-fA-F]+)", question or "")
    if not m:
        return []
    addr = m.group(1)
    args, slots = _vid_to_arg(question), _vid_stack_offsets(question)
    byoff = {hex(int(o, 16)): vid for vid, o in slots.items()}   # normalized frame offset -> vid
    facts = []
    for vid, k in sorted(args.items()):
        try:
            sh = call_tool("struct_shape", {"addr": addr, "reg": f"param_{k}"})
            sh = json.loads(sh) if isinstance(sh, str) else sh
        except Exception:  # noqa: BLE001
            continue
        if not isinstance(sh, dict) or not sh.get("is_aggregate") or not sh.get("fields"):
            continue
        ctype = _render_shape(sh["fields"], sh.get("self_ref_offsets"))
        facts.append((vid, ctype, f"param_{k} fields {sorted(sh['fields'])}"))
        home = sh.get("home_slot_qoff")               # the spill slot IS the same pointer
        if home and hex(int(home, 16)) in byoff:
            facts.append((byoff[hex(int(home, 16))], ctype, f"home slot of param_{k}"))
        for soff, foff in (sh.get("alias_slots") or {}).items():
            # only a slot holding a SELF-REFERENTIAL field is known to be this same struct pointer;
            # a slot holding any other field is some other type and is left to the agents.
            if foff in set(sh.get("self_ref_offsets") or ()) and hex(int(soff, 16)) in byoff:
                facts.append((byoff[hex(int(soff, 16))], ctype,
                              f"holds self-referential field_{int(foff, 16)}"))
    return facts


def _oracle_struct_shape(call_tool, question) -> list:
    out = []
    for vid, ctype, why in struct_shape_facts(call_tool, question):
        # MODE `shape`: more informative than a bare pointer, less than a named source type. It
        # overrides a non-pointer or a shapeless pointer (`void *`, `struct *`) but DEFERS to any
        # pointer whose pointee the agents named -- we recover layout, never a source-level name.
        out.append({"vid": vid, "ctype": ctype, "mode": "shape", "why": why})
    return out
