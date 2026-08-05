"""Interprocedural oracle: signature parsing, deref/scalar evidence, the forwarding walk,
the definition-line guard, and the physical-realizability size guard."""
from agentic.tasks.type_recovery import interproc as I

Q8 = "function at vaddr 0x101b00.\nV1  register 0x38  8\n"
Q4 = "function at vaddr 0x101b00.\nV1  register 0x38  4\n"


def _ct(decs):
    """decs: {addr: decompilation}. Unknown addrs return a no-decompilation marker."""
    return lambda name, args: decs.get(args.get("addr"), "(no decompilation)") \
        if name == "decompile" else "{}"


# ---- helpers ----
def test_sig_param_decls():
    dec = "undefined8 FUN_00101b00(char *param_1,long param_2)\n{\n  return 0;\n}\n"
    assert I._sig_param_decls(dec) == {"param_1": "char *", "param_2": "long"}


def test_sig_param_decls_none():
    assert I._sig_param_decls("void FUN_00101b00(void)\n{\n}\n") == {}


def test_derefs_param_cast_idiom():
    assert I._derefs_param("x = *(char *)(param_1 + 1);", "param_1")


def test_derefs_param_base_plus_length_is_not_deref():
    assert not I._derefs_param("p = (char *)(param_2 + param_1);", "param_1")


def test_derefs_param_offset_alias():
    dec = "local_20 = (char *)(param_1 + 8);\n y = *local_20;"
    assert I._derefs_param(dec, "param_1")


def test_scalar_evidence():
    assert I._scalar_evidence("x = param_1 * 2;", "param_1")
    assert I._scalar_evidence("x = y % param_1;", "param_1")
    assert I._scalar_evidence("x = arr[param_1];", "param_1")
    assert I._scalar_evidence("x = param_1 + y;", "param_1") == ""   # + is pointer-legal


def test_width_matched_int():
    assert I._width_matched_int("long", 4) == "int"
    assert I._width_matched_int("ulong", 4) == "unsigned int"
    assert I._width_matched_int("long", 8) == "long"
    assert I._width_matched_int("int", None) == "int"
    assert I._width_matched_int("bool", 1) == "char"


def test_callee_addr():
    assert I._callee_addr("FUN_0010b353") == "0x10b353"
    assert I._callee_addr("funcB") is None


# ---- end-to-end forwarding walks ----
CALLER = "void FUN_00101b00(undefined8 param_1)\n{\n  FUN_00102000(param_1);\n  return;\n}\n"


def test_declared_ptr_floor():
    callee = "void FUN_00102000(byte *param_1)\n{\n  *param_1 = 0;\n  return;\n}\n"
    facts = I.interprocedural_param_usage_facts(
        _ct({"0x101b00": CALLER, "0x102000": callee}), Q8)
    assert [(f[0], f[1], f[6]) for f in facts] == [("V1", "byte *", "declared_ptr")]


def test_size_guard_drops_pointer_on_small_slot():
    callee = "void FUN_00102000(byte *param_1)\n{\n  *param_1 = 0;\n  return;\n}\n"
    assert I.interprocedural_param_usage_facts(
        _ct({"0x101b00": CALLER, "0x102000": callee}), Q4) == []


def test_size_guard_needs_sizes_parsed_from_spaces():
    # the guard reads _vid_sizes; space-separated variables (the live tool-path form) must work
    callee = "void FUN_00102000(byte *param_1)\n{\n  *param_1 = 0;\n  return;\n}\n"
    q4_spaces = "function at vaddr 0x101b00.\nV1  register 0x38  4\n"
    assert I.interprocedural_param_usage_facts(
        _ct({"0x101b00": CALLER, "0x102000": callee}), q4_spaces) == []


def test_declared_scalar_negative_claim():
    callee = ("void FUN_00102000(long param_1)\n{\n  x = param_1 * 8;\n  return;\n}\n")
    facts = I.interprocedural_param_usage_facts(
        _ct({"0x101b00": CALLER, "0x102000": callee}), Q8)
    (f,) = facts
    assert (f[0], f[1], f[6]) == ("V1", "long", "declared_scalar")


def test_declared_scalar_width_matched():
    callee = ("void FUN_00102000(long param_1)\n{\n  x = param_1 * 8;\n  return;\n}\n")
    facts = I.interprocedural_param_usage_facts(
        _ct({"0x101b00": CALLER, "0x102000": callee}), Q4)
    (f,) = facts
    assert (f[1], f[6]) == ("int", "declared_scalar")   # 4-byte slot narrows `long`


def test_contradictory_declared_int_but_dereferenced_abstains():
    callee = ("void FUN_00102000(long param_1)\n{\n  x = param_1 * 8;\n"
              "  y = *(char *)param_1;\n  return;\n}\n")
    assert I.interprocedural_param_usage_facts(
        _ct({"0x101b00": CALLER, "0x102000": callee}), Q8) == []


def test_bare_long_no_evidence_keeps_walking_to_nothing():
    callee = "void FUN_00102000(long param_1)\n{\n  return;\n}\n"
    assert I.interprocedural_param_usage_facts(
        _ct({"0x101b00": CALLER, "0x102000": callee}), Q8) == []


def test_libc_terminus_via_chain():
    callee = "void FUN_00102000(undefined8 param_1)\n{\n  strlen(param_1);\n}\n"
    facts = I.interprocedural_param_usage_facts(
        _ct({"0x101b00": CALLER, "0x102000": callee}), Q8)
    (f,) = facts
    assert (f[0], f[1], f[4], f[6]) == ("V1", "char *", "strlen", "libc")


def test_two_hop_chain():
    callee1 = "void FUN_00102000(undefined8 param_1)\n{\n  FUN_00103000(param_1);\n}\n"
    callee2 = "void FUN_00103000(undefined8 param_1)\n{\n  puts(param_1);\n}\n"
    facts = I.interprocedural_param_usage_facts(
        _ct({"0x101b00": CALLER, "0x102000": callee1, "0x103000": callee2}), Q8)
    (f,) = facts
    assert (f[1], f[4], f[6]) == ("char *", "puts", "libc")


def test_definition_line_guard():
    # the caller's own definition line names FUN_00101b00(param_1): must not be treated as a call
    caller = ("void FUN_00101b00(undefined8 param_1)\n{\n  return;\n}\n")
    assert I.interprocedural_param_usage_facts(_ct({"0x101b00": caller}), Q8) == []


def test_nested_call_position_mapping():
    # param_1 sits AFTER a comma-carrying nested call: must be read as arg 2, not arg 3
    caller = ("void FUN_00101b00(undefined8 param_1)\n{\n"
              "  FUN_00102000(FUN_00103000(a, b),param_1);\n  return;\n}\n")
    callee = "void FUN_00102000(long p1,char *param_2)\n{\n  *param_2 = 0;\n  return;\n}\n"
    facts = I.interprocedural_param_usage_facts(
        _ct({"0x101b00": caller, "0x102000": callee}), Q8)
    (f,) = facts
    assert (f[0], f[1], f[3], f[6]) == ("V1", "char *", "param_2", "declared_ptr")


def test_oracle_wrapper_modes():
    callee_ptr = "void FUN_00102000(byte *param_1)\n{\n  *param_1 = 0;\n  return;\n}\n"
    out = I._oracle_interprocedural_param_usage(
        _ct({"0x101b00": CALLER, "0x102000": callee_ptr}), Q8)
    (f,) = out
    assert f["mode"] == "floor" and f["floor"] is True
    callee_sc = "void FUN_00102000(long param_1)\n{\n  x = param_1 * 8;\n  return;\n}\n"
    out = I._oracle_interprocedural_param_usage(
        _ct({"0x101b00": CALLER, "0x102000": callee_sc}), Q8)
    (f,) = out
    assert f["mode"] == "scalar" and "IS NOT A POINTER" in f["claim"]
