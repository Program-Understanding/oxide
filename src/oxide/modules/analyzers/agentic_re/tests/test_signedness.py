"""Signedness oracle: register canonicalization, disasm parsing, the def-use walk, and the
end-to-end facts — including the documented false-positive gap (sign idiom), marked xfail."""
import pytest

from agentic.tasks.type_recovery import signedness as SG

Q = "function at vaddr 0x101000.\nV1  stack -0x24  4\nV2  register 0x30  4\n"


def test_canon_reg():
    assert SG._canon_reg("eax") == "rax"
    assert SG._canon_reg("r8d") == "r8"
    assert SG._canon_reg("sil") == "rsi"
    assert SG._canon_reg("xyzzy") is None


def test_parse_disasm():
    txt = ("CALLS: funcB\n\n0x101000    push rbp\n"
           "0x101004    movzx eax, byte ptr [rbp + -0x1c]    <=== requested address\n")
    dis = SG._parse_disasm(txt)
    assert dis == [(0x101000, "push", "rbp"),
                   (0x101004, "movzx", "eax, byte ptr [rbp + -0x1c]")]


def _fake_tools(stack_accesses, window_text):
    """stack_var returns canned accesses; disassemble returns one canned window."""
    def ct(name, args):
        if name == "stack_var":
            import json
            return json.dumps({"found": True, "accesses": stack_accesses})
        if name == "disassemble":
            return window_text
        if name == "register_usage":
            import json
            return json.dumps({"register": "rsi", "accesses": stack_accesses})
        return "{}"
    return ct


def test_unsigned_direct_movzx_on_slot():
    acc = ["0x101010: movzx eax, byte ptr [rbp + -0x1c]"]
    win = "0x101010    movzx eax, byte ptr [rbp + -0x1c]\n"
    facts = SG.signedness_facts(_fake_tools(acc, win), Q)
    assert ("V1", "uint32_t") in [(f[0], f[1]) for f in facts]


def test_signed_evidence_vetoes():
    acc = ["0x101010: movzx eax, byte ptr [rbp + -0x1c]",
           "0x101020: sar dword ptr [rbp + -0x1c],0x2"]
    win = ("0x101010    movzx eax, byte ptr [rbp + -0x1c]\n"
           "0x101020    sar dword ptr [rbp + -0x1c],0x2\n")
    assert SG.signedness_facts(_fake_tools(acc, win), Q) == []


def test_store_back_walk_finds_shr_before_store():
    acc = ["0x101020: mov dword ptr [rbp + -0x1c],eax"]
    win = ("0x101018    shr eax,0x2\n"
           "0x101020    mov dword ptr [rbp + -0x1c],eax\n")
    facts = SG.signedness_facts(_fake_tools(acc, win), Q)
    assert [(f[0], f[1]) for f in facts if f[0] == "V1"] == [("V1", "uint32_t")]


def test_walk_stops_at_register_redefinition():
    # the shr belongs to a PREVIOUS value of eax: `mov eax, <other>` between it and the store
    acc = ["0x101020: mov dword ptr [rbp + -0x1c],eax"]
    win = ("0x101010    shr eax,0x2\n"
           "0x101018    mov eax,ebx\n"
           "0x101020    mov dword ptr [rbp + -0x1c],eax\n")
    assert SG.signedness_facts(_fake_tools(acc, win), Q) == []


def test_register_variable_pointee_movzx_not_attributed():
    # `movzx eax, byte ptr [rsi]` extends the POINTEE, not rsi: must not claim V2 unsigned
    acc = ["0x101010: movzx eax, byte ptr [rsi]"]
    win = "0x101010    movzx eax, byte ptr [rsi]\n"
    facts = SG.signedness_facts(_fake_tools(acc, win), Q)
    assert all(f[0] != "V2" for f in facts)


def test_only_sized_integers_considered():
    q = "function at vaddr 0x101000.\nV9  stack -0x30  16\n"     # 16B: no integer width
    acc = ["0x101010: movzx eax, byte ptr [rbp + -0x28]"]
    win = "0x101010    movzx eax, byte ptr [rbp + -0x28]\n"
    assert SG.signedness_facts(_fake_tools(acc, win), q) == []


def test_sign_idiom_not_counted_as_unsigned():
    """`(x > 0) - (x < 0)` on a SIGNED int, transcribed from sort/diff_reversed at 0x10951b.
    Both `movzx` instructions widen a one-bit boolean and the `shr` extracts the sign bit, so
    none of the three is evidence about the variable. Before the vetoes this claimed uint32_t
    on ground truth `int` and cost the function 83.33 -> 75.00."""
    acc = ["0x10951b: mov eax,dword ptr [rbp + -0x4]",
           "0x109524: cmp dword ptr [rbp + -0x4],0x0"]
    win = ("0x10951b    mov eax,dword ptr [rbp + -0x4]\n"
           "0x10951e    shr eax,0x1f\n"
           "0x109521    movzx eax,al\n"
           "0x109524    cmp dword ptr [rbp + -0x4],0x0\n"
           "0x109528    setg dl\n"
           "0x10952b    movzx edx,dl\n"
           "0x10952e    sub eax,edx\n")
    q = "function at vaddr 0x109505.\nV1  stack -0x4  4\n"
    assert SG.signedness_facts(_fake_tools(acc, win), q) == []


def test_signbit_extract_predicate():
    assert SG._is_signbit_extract("shr", "eax,0x1f")
    assert SG._is_signbit_extract("shr", "rax,0x3f")
    assert not SG._is_signbit_extract("shr", "eax,0x2")     # a real division
    assert not SG._is_signbit_extract("sar", "eax,0x1f")


def test_ordinary_shr_still_counts():
    """The veto must not silence a genuine unsigned division."""
    acc = ["0x101020: mov dword ptr [rbp + -0x1c],eax"]
    win = ("0x101018    shr eax,0x2\n"
           "0x101020    mov dword ptr [rbp + -0x1c],eax\n")
    facts = SG.signedness_facts(_fake_tools(acc, win), Q)
    assert [(f[0], f[1]) for f in facts if f[0] == "V1"] == [("V1", "uint32_t")]


def test_oracle_wrapper_mode_sign():
    acc = ["0x101010: movzx eax, byte ptr [rbp + -0x1c]"]
    win = "0x101010    movzx eax, byte ptr [rbp + -0x1c]\n"
    out = SG._oracle_signedness(_fake_tools(acc, win), Q)
    (f,) = [x for x in out if x["vid"] == "V1"]
    assert f["mode"] == "sign" and f["ctype"] == "uint32_t"
    assert "IS UNSIGNED" in f["claim"]
