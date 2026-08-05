"""Struct-shape oracle: rendering and the slot-aliasing rules."""
import json

from agentic.tasks.type_recovery import struct_shape as SS

Q = ("function at vaddr 0x101000.\nV1  register 0x38  8\n"
     "V2  stack -0x20  8\nV3  stack -0x30  8\n")


def test_render_shape_selfref_tagged():
    out = SS._render_shape({"0x0": 4, "0x8": 8}, ["0x8"])
    assert out == "struct t1 { int field_0; struct t1 *field_8; } *"


def test_render_shape_plain():
    out = SS._render_shape({"0x0": 4, "0x4": 4}, [])
    assert out == "struct { int field_0; int field_4; } *"


def _ct(shape):
    return lambda name, args: json.dumps(shape) if name == "struct_shape" else "{}"


def test_aggregate_certifies_param_home_and_selfref_alias():
    shape = {"register": "rdi", "arg_position": 1, "home_slot_qoff": "-0x20",
             "fields": {"0x0": 4, "0x8": 8}, "self_ref_offsets": ["0x8"],
             "alias_slots": {"-0x30": "0x8", "-0x40": "0x0"}, "is_aggregate": True}
    facts = SS.struct_shape_facts(_ct(shape), Q)
    vids = [f[0] for f in facts]
    assert vids == ["V1", "V2", "V3"]                 # param, its home slot, the selfref alias
    assert all("struct t1" in f[1] for f in facts)
    # -0x40 holds field 0x0 (NOT self-referential) and is absent from the question anyway
    assert all(f[0] != "V4" for f in facts)


def test_non_aggregate_abstains():
    shape = {"register": "rdi", "arg_position": 1, "home_slot_qoff": "-0x20",
             "fields": {"0x0": 8}, "self_ref_offsets": [], "alias_slots": {},
             "is_aggregate": False}
    assert SS.struct_shape_facts(_ct(shape), Q) == []


def test_oracle_wrapper_emits_shape_mode():
    shape = {"register": "rdi", "arg_position": 1, "home_slot_qoff": None,
             "fields": {"0x0": 4, "0x8": 8}, "self_ref_offsets": [],
             "alias_slots": {}, "is_aggregate": True}
    out = SS._oracle_struct_shape(_ct(shape), Q)
    assert out and all(f["mode"] == "shape" for f in out)
