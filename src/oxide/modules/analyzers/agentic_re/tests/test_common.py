"""Question parsers, argument splitting, and pointer predicates (tasks/type_recovery/common.py)."""
import pytest

from agentic.tasks.type_recovery import common as C


# ---- _vid_sizes: must accept BOTH the tab-separated harness question and the space-separated
# variables the verifier passes to oracle tools (measured: 112/112 live calls use spaces). ----
def test_vid_sizes_tabs(q_tabs):
    assert C._vid_sizes(q_tabs) == {"V1": 8, "V2": 4, "V3": 8, "V4": 4}


def test_vid_sizes_spaces(q_spaces):
    assert C._vid_sizes(q_spaces) == {"V1": 8, "V2": 4, "V3": 8, "V4": 4}


def test_vid_sizes_mixed_and_empty():
    assert C._vid_sizes("V7\tregister 0x10\t2\nV8  stack -0x30  1\n") == {"V7": 2, "V8": 1}
    assert C._vid_sizes("") == {}
    assert C._vid_sizes(None) == {}


def test_vid_to_arg(q_tabs):
    assert C._vid_to_arg(q_tabs) == {"V1": 1, "V2": 2}


def test_vid_to_arg_unknown_offset_ignored():
    assert C._vid_to_arg("V1  register 0x99  8\n") == {}


def test_vid_stack_offsets(q_spaces):
    assert C._vid_stack_offsets(q_spaces) == {"V3": "-0x20", "V4": "-0x24"}


def test_vid_to_ghidra_name(q_tabs):
    assert C._vid_to_ghidra_name(q_tabs) == {
        "V1": "param_1", "V2": "param_2", "V3": "local_20", "V4": "local_24"}


# ---- _split_args: top-level commas only ----
def test_split_args_flat():
    assert C._split_args("a, b, c") == ["a", "b", "c"]


def test_split_args_nested_call():
    assert C._split_args("FUN_b(x, y), param_1") == ["FUN_b(x, y)", "param_1"]


def test_split_args_cast():
    assert C._split_args("(char *)param_1, param_2") == ["(char *)param_1", "param_2"]


def test_split_args_empty_and_single():
    assert C._split_args("") == [""]
    assert C._split_args("param_1") == ["param_1"]


def test_split_args_unbalanced_does_not_crash():
    assert C._split_args("f(a, b") == ["f(a, b"]


# ---- _arg_is_value: only the value ITSELF (modulo casts/parens) transfers a callee type ----
def test_arg_is_value_exact_and_cast():
    assert C._arg_is_value("param_1", {"param_1"})
    assert C._arg_is_value("(char *)param_1", {"param_1"})
    assert C._arg_is_value("(int)param_1", {"param_1"})
    assert C._arg_is_value("((param_1))", {"param_1"})


def test_arg_is_value_rejects_derived():
    assert not C._arg_is_value("*param_1", {"param_1"})
    assert not C._arg_is_value("param_1[2]", {"param_1"})
    assert not C._arg_is_value("param_1 + 8", {"param_1"})
    assert not C._arg_is_value("FUN_1(param_1)", {"param_1"})


# ---- pointer-class predicates ----
def test_is_vague_pointer():
    assert C._is_vague_pointer("void *")
    assert C._is_vague_pointer("undefined8 *")
    assert C._is_vague_pointer("undefined *")
    assert C._is_vague_pointer("void **")
    assert not C._is_vague_pointer("char *")
    assert not C._is_vague_pointer("int")


def test_is_shapeless_pointer():
    assert C.is_shapeless_pointer("void *")
    assert C.is_shapeless_pointer("struct *")
    assert C.is_shapeless_pointer("undefined8 *")
    assert not C.is_shapeless_pointer("Hash_table *")
    assert not C.is_shapeless_pointer("char *")


# ---- _decl_pointer_map ----
def test_decl_pointer_map():
    dec = ("undefined8 funcA(char *param_1,uint32_t *param_2)\n"
           "{\n  FILE *local_30;\n  long local_38;\n  return *param_1;\n}\n")
    m = C._decl_pointer_map(dec)
    assert m["param_1"] == "char *"
    assert m["param_2"] == "uint32_t *"
    assert m["local_30"] == "FILE *"
    assert "local_38" not in m                       # non-pointer decl not reported


@pytest.mark.xfail(reason="LATENT BUG found 2026-08-04 by this suite: _decl_pointer_map's base-type "
                          "group requires a trailing [A-Za-z_], so a Ghidra type ending in a DIGIT "
                          "(undefined8/undefined4/undefined2) never matches. decompiler_pointer and "
                          "spilled_param therefore under-fire on the single most common Ghidra "
                          "pointer form, while interproc._sig_param_decls DOES parse it -- the two "
                          "parsers disagree. Needs an A/B before fixing (it adds oracle facts).",
                   strict=False)
def test_decl_pointer_map_undefinedN():
    dec = "undefined8 f(undefined8 *param_1,undefined4 *param_2)\n{\n  return 0;\n}\n"
    m = C._decl_pointer_map(dec)
    assert m.get("param_1") == "undefined8 *"
    assert m.get("param_2") == "undefined4 *"


def test_decl_pointer_map_matches_sig_param_decls_on_pointers():
    """The two declaration parsers must agree on POINTER declarations; where they disagree, one
    oracle sees evidence another cannot (currently they diverge on `undefinedN *` -- see above)."""
    from agentic.tasks.type_recovery.interproc import _sig_param_decls
    dec = "undefined8 f(char *param_1,uint32_t *param_2,long param_3)\n{\n  return 0;\n}\n"
    ptr_from_decl = C._decl_pointer_map(dec)
    ptr_from_sig = {k: v for k, v in _sig_param_decls(dec).items() if "*" in v}
    assert {k: v.replace(" ", "") for k, v in ptr_from_decl.items() if k.startswith("param")} == \
           {k: v.replace(" ", "") for k, v in ptr_from_sig.items()}


def test_decl_pointer_map_skips_keywords():
    assert "param_1" not in C._decl_pointer_map("return *param_1;")


# ---- _libc_type_of_param (AGENTIC_LIBC=1 in this suite) ----
def test_libc_type_of_param_direct():
    dec = "void f(char *param_1)\n{\n  strlen(param_1);\n}\n"
    assert C._libc_type_of_param(dec, "param_1") == ("char *", "strlen", 1)


def test_libc_type_of_param_alias_and_cast():
    dec = "void f(void *param_1)\n{\n  pv = param_1;\n  memcpy((void *)pv,src,8);\n}\n"
    assert C._libc_type_of_param(dec, "param_1") == ("void *", "memcpy", 1)


def test_libc_type_of_param_rejects_deref():
    dec = "void f(char *param_1)\n{\n  fputc(*param_1,stream);\n}\n"
    assert C._libc_type_of_param(dec, "param_1") is None


def test_libc_type_of_param_nested_call_position():
    # the argument AFTER a comma-carrying nested call must map to the right position
    dec = "void f(long param_2)\n{\n  fwrite(buf,FUN_1(a, b),1,param_2);\n}\n"
    hit = C._libc_type_of_param(dec, "param_2")
    assert hit == ("FILE *", "fwrite", 4)


def test_libc_type_of_param_off(empty_libc):
    dec = "void f(char *param_1)\n{\n  strlen(param_1);\n}\n"
    assert C._libc_type_of_param(dec, "param_1") is None
