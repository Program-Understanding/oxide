"""callee_signature and spilled_param oracles, driven by fake tool responses."""
from agentic.tasks.type_recovery import libc_abi as L
from agentic.tasks.type_recovery import spilled as S

Q = "function at vaddr 0x101a00.\nV1\tregister 0x38\t8\nV2\tregister 0x30\t8\n"


def _ct(dec):
    return lambda name, args: dec


DEC_CAST = ("undefined8 FUN_00101a00(char *param_1,long param_2)\n{\n"
            "  iVar1 = strcmp((char *)param_1,(char *)param_2);\n  return iVar1;\n}\n")


def test_callee_signature_cast_call():
    facts = L.callee_type_recall_facts(_ct(DEC_CAST), Q)
    assert ("V1", "char *", "strcmp", 1) in facts
    assert ("V2", "char *", "strcmp", 2) in facts


def test_callee_signature_plain_call():
    dec = DEC_CAST.replace("(char *)param_1,(char *)param_2", "param_1,param_2")
    facts = L.callee_type_recall_facts(_ct(dec), Q)
    assert ("V1", "char *", "strcmp", 1) in facts


def test_callee_signature_alias():
    dec = ("void FUN_00101a00(undefined8 param_1)\n{\n"
           "  pcVar1 = param_1;\n  puts(pcVar1);\n}\n")
    facts = L.callee_type_recall_facts(_ct(dec), Q)
    assert ("V1", "char *", "puts", 1) in facts


def test_callee_signature_vararg_position_unconstrained():
    # printf's fixed position is only arg 1; a parameter at a vararg position transfers nothing
    dec = "void FUN_00101a00(long param_2)\n{\n  printf(fmt,param_2);\n}\n"
    facts = L.callee_type_recall_facts(_ct(dec), Q)
    assert all(f[0] != "V2" for f in facts)


def test_callee_signature_first_hit_wins_per_vid():
    dec = ("void FUN_00101a00(char *param_1)\n{\n"
           "  strlen(param_1);\n  free(param_1);\n}\n")
    facts = L.callee_type_recall_facts(_ct(dec), Q)
    assert facts.count(("V1", "char *", "strlen", 1)) == 1
    assert all(f[2] == "strlen" for f in facts if f[0] == "V1")


def test_callee_signature_abstains_without_libc(empty_libc):
    assert L.callee_type_recall_facts(_ct(DEC_CAST), Q) == []


def test_callee_signature_no_vaddr_or_no_registers():
    assert L.callee_type_recall_facts(_ct(DEC_CAST), "no address here") == []
    assert L.callee_type_recall_facts(_ct(DEC_CAST),
                                      "function at vaddr 0x1.\nV9\tstack -0x8\t8\n") == []


def test_oracle_wrapper_floor_flag():
    dec = "void FUN_00101a00(void *param_1)\n{\n  free(param_1);\n}\n"
    out = L._oracle_callee_signature(_ct(dec), Q)
    (f,) = [x for x in out if x["vid"] == "V1"]
    assert f["ctype"] == "void *"
    assert f["floor"] is True                       # void * is a pointee-unknown floor
    assert "fixes" in f["claim"] or "ABI" in f["claim"]


# ---- spilled_param ----
QS = "function at vaddr 0x101a00.\nV5\tstack -0x20\t8\nV6\tstack -0x30\t8\n"


def _spill_ct(dec, stack_texts):
    def ct(name, args):
        if name == "decompile":
            return dec
        if name == "stack_var":
            return stack_texts.get(args.get("offset"), '{"found": false, "accesses": []}')
        return "{}"
    return ct


def test_spilled_param_maps_slot_to_parameter():
    dec = "void FUN_00101a00(char *param_1)\n{\n  return;\n}\n"
    sv = {"-0x20": '{"accesses": ["0x101a08: mov qword ptr [rbp + -0x18],rdi"]}'}
    facts = S.spilled_param_facts(_spill_ct(dec, sv), QS)
    assert ("V5", "char *", "param_1", "rdi") in facts
    assert all(f[0] != "V6" for f in facts)          # no spill observed -> abstain


def test_spilled_param_ignores_non_argument_stores():
    dec = "void FUN_00101a00(char *param_1)\n{\n  return;\n}\n"
    sv = {"-0x20": '{"accesses": ["0x101a08: mov dword ptr [rbp + -0x18],eax"]}'}
    assert S.spilled_param_facts(_spill_ct(dec, sv), QS) == []


def test_spilled_param_libc_fallback():
    # no declared pointer for param_1, but it flows to strlen -> char *
    dec = "void FUN_00101a00(undefined8 param_1)\n{\n  strlen(param_1);\n}\n"
    sv = {"-0x20": '{"accesses": ["0x101a08: mov qword ptr [rbp + -0x18],rdi"]}'}
    facts = S.spilled_param_facts(_spill_ct(dec, sv), QS)
    assert ("V5", "char *", "param_1", "rdi") in facts


def test_spilled_param_no_decl_no_libc_abstains(empty_libc):
    dec = "void FUN_00101a00(undefined8 param_1)\n{\n  strlen(param_1);\n}\n"
    sv = {"-0x20": '{"accesses": ["0x101a08: mov qword ptr [rbp + -0x18],rdi"]}'}
    assert S.spilled_param_facts(_spill_ct(dec, sv), QS) == []
