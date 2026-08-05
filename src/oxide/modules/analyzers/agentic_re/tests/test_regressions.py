"""Named regression guards.

Each test here pins a bug that was actually shipped and measured, so a future change that
re-introduces it fails by name rather than as a mysterious score drift. Keep the docstrings --
they are the only record of what the number cost.
"""
import pytest

from agentic import certify as CF
from agentic.tasks.type_recovery import common as C
from agentic.tasks.type_recovery import interproc as I
from agentic.tasks.type_recovery import libc_abi as L
from agentic.tools import registry as R


# ---- 2026-08-04, fix #1 -------------------------------------------------------------------------
def test_vid_sizes_accepts_the_live_tool_path_format():
    """`_vid_sizes` was TAB-only while 112/112 measured verifier oracle calls pass SPACES, so on the
    live tool path it returned {} -- signedness abstained on every variable and interproc's
    realizability guard never ran. Both formats must parse."""
    tabs = "V1\tregister 0x38\t8\n"
    spaces = "V1  register 0x38  8\n"
    assert C._vid_sizes(tabs) == C._vid_sizes(spaces) == {"V1": 8}


def test_signedness_reachable_with_space_separated_variables():
    """End-to-end consequence of the above: the oracle must produce a fact from a space-separated
    question, which pre-fix it never could."""
    import json
    from agentic.tasks.type_recovery import signedness as SG

    def ct(name, args):
        if name == "stack_var":
            return json.dumps({"found": True,
                               "accesses": ["0x101010: movzx eax, byte ptr [rbp + -0x1c]"]})
        if name == "disassemble":
            return "0x101010    movzx eax, byte ptr [rbp + -0x1c]\n"
        return "{}"

    q = "function at vaddr 0x101000.\nV1  stack -0x24  4\n"
    assert [f[0] for f in SG.signedness_facts(ct, q)] == ["V1"]


# ---- 2026-08-04, fix #2 -------------------------------------------------------------------------
def test_signedness_tool_registration_is_keyword_shaped():
    """`@_tool("signedness", "desc...")` bound the description to `group` and left params empty, so
    the tool was the only oracle outside group 'oracle' and declared no schema."""
    import agentic.tasks.type_recovery  # noqa: F401
    spec = R.REGISTRY["signedness"]
    assert spec.group == "oracle"
    params = spec.schema["function"]["parameters"]
    assert set(params["properties"]) == {"addr", "variables"}
    assert set(params["required"]) == {"addr", "variables"}


# ---- 2026-08-04, fix #3 -------------------------------------------------------------------------
def test_nested_call_does_not_shift_argument_positions():
    """`_CALL_ARGS` admits one nesting level but consumers split on every comma, so in
    `FUN_a(FUN_b(x, y), p)` the value `p` was read as argument 3 and the walk followed the callee's
    WRONG parameter -- a route to a confidently wrong certification."""
    assert C._split_args("FUN_b(x, y), param_1") == ["FUN_b(x, y)", "param_1"]
    caller = ("void FUN_00101b00(undefined8 param_1)\n{\n"
              "  FUN_00102000(FUN_00103000(a, b),param_1);\n}\n")
    callee = "void FUN_00102000(long p1,char *param_2)\n{\n  *param_2 = 0;\n}\n"
    ct = lambda n, a: {"0x101b00": caller, "0x102000": callee}.get(a.get("addr"), "(no)")  # noqa: E731
    facts = I.interprocedural_param_usage_facts(ct, "function at vaddr 0x101b00.\nV1  register 0x38  8\n")
    assert facts and facts[0][3] == "param_2"


# ---- 2026-08-04, fix #4 -------------------------------------------------------------------------
def test_callee_signature_sees_cast_arguments():
    """A flat `\\(([^()]*)\\)` call matcher could not match `strcmp((char *)p, q)` -- Ghidra's
    dominant idiom -- so the oracle silently missed every cast call site under AGENTIC_LIBC=1."""
    dec = ("undefined8 FUN_00101a00(char *param_1,long param_2)\n{\n"
           "  iVar1 = strcmp((char *)param_1,(char *)param_2);\n}\n")
    q = "function at vaddr 0x101a00.\nV1\tregister 0x38\t8\n"
    assert ("V1", "char *", "strcmp", 1) in L.callee_type_recall_facts(lambda n, a: dec, q)


# ---- earlier shipped bugs (from the project record) ---------------------------------------------
def test_size_guard_blocks_pointer_on_small_slot(oxide_stub):
    """fdb09ab: the 'sound-by-construction' oracles certified 8-byte pointers onto 4-byte slots,
    overriding a verifier that was correct (chroot/mgetgroups 86.11 -> 93.52 once guarded)."""
    q = ("function at vaddr 0x101000.\nV1\tregister 0x38\t8\nV2\tregister 0x30\t4\n")
    facts = CF._collect_oracle_facts("testoid", q, {})
    assert "V2" not in facts, "a pointer was certified onto a 4-byte slot"


def test_undef_rescue_never_downgrades_a_specific_type(msg):
    """do_encode V2: the verifier overwrote the worker's `char *` with `undefined8 *`. The rescue is
    monotone -- it may only replace a non-answer, never rewrite one concrete type as another."""
    msgs = [msg(type="tool", content="V1: char *\n", tool_call_id="t")]
    assert "FILE *" in CF._rescue_undefined(msgs, "V1: FILE *\n")


def test_floor_defers_to_any_model_pointer(monkeypatch):
    """ginstall/hash_rehash 45.10 -> 37.25 when the floor rule was made depth-aware: a pointee-unknown
    fact's sound content is '>= pointer', so ANY model pointer satisfies it regardless of depth."""
    monkeypatch.setattr(CF, "_collect_oracle_facts", lambda *a: {"V1": ("void **", "o", "floor")})
    out = CF._certified_trailer("oid", "V1\tregister 0x38\t8\n", "V1: Hash_table *\n", {})
    assert "ORACLE-CERTIFIED" not in out


def test_size_coercion_narrows_but_never_widens():
    """comm/readlinebuffer_delim V7 (GT char *): coercing int -> long on an 8-byte slot cost 6.9
    points, while the three narrowing rewrites gained 25.0, 11.9 and 1.8."""
    q = "function at vaddr 0x1.\nV1\tstack -0x20\t8\nV2\tregister 0x38\t4\n"
    out = CF._coerce_sizes(q, "V1: int\nV2: char *\n")
    assert "V1: int" in out                       # 4-byte type on 8-byte slot: ambiguous, keep
    assert "V2: int" in out                       # pointer on 4-byte slot: impossible, narrow


def test_array_rule_for_oversized_slot():
    """date/posix_time_parse V4: GT `int[6]` in a 24-byte slot reported `int *` scored 1/6, failing
    the metric's first rule. A slot wider than a pointer cannot hold one."""
    q = "function at vaddr 0x1.\nV1\tstack -0x40\t24\n"
    assert "V1: int[6]" in CF._coerce_sizes(q, "V1: int *\n")


def test_delegations_do_not_count_against_the_tool_cap(monkeypatch):
    """sha384sum/sha512_process_block (179 vars): counting `task` against the loop cap ceilinged
    fan-out at 10 delegations, covering V1-V57 and scoring 25.64% of max."""
    from agentic import deepagent as D

    class _AI:
        type = "ai"

        def __init__(self):
            self.tool_calls = [{"name": "task", "id": "x"}]

    monkeypatch.setenv("AGENTIC_MAX_TOOL_TURNS", "3")
    msgs = [_AI() for _ in range(30)]
    out_msgs, out_kw = D._cap_tool_loop(msgs, {"tools": [{"name": "task"}]})
    assert out_msgs is msgs and "tools" in out_kw


def test_group_size_scales_with_variable_count():
    """Same function: a constant group size of 6 needs ~30 delegations. The rule must grow the group
    so any function fits in ~6 delegations, while leaving small functions at exactly 6."""
    from agentic import deepagent as D
    small = "".join(f"V{i}\tstack -0x{i:x}\t8\n" for i in range(1, 7))
    big = "".join(f"V{i}\tstack -0x{i:x}\t8\n" for i in range(1, 180))
    assert D._group_size(small) == 6
    assert D._group_size(big) == 30


def test_worker_never_holds_the_decompiler_lens():
    """The two-lens split is enforced by ROSTERS, not by prompt wording: giving the assembly worker
    any decompiler-fed tool collapses the split and the verifier's independent evidence."""
    from agentic import deepagent as D
    assert not (D.WORKER_TOOLS & {"decompile", "value_usage"})


def test_libc_table_is_off_by_default(monkeypatch):
    """AGENTIC_LIBC defaults OFF (measured null over n=376) so the external-knowledge objection is
    removed. This suite sets it to 1; production must not."""
    import importlib
    monkeypatch.delenv("AGENTIC_LIBC", raising=False)
    mod = importlib.reload(importlib.import_module("agentic.tasks.type_recovery.common"))
    assert mod._LIBC_SIG == {}
    monkeypatch.setenv("AGENTIC_LIBC", "1")
    importlib.reload(mod)                          # restore for the rest of the session
