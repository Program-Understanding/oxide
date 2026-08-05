"""Deterministic post-passes: size coercion, undefined-rescue, the certified trailer's claim-mode
semantics, and an offline end-to-end run of _collect_oracle_facts (incl. the size guard)."""
import pytest

from agentic import certify as CF


# ---- _type_width ----
def test_type_width():
    assert CF._type_width("char *") == 8
    assert CF._type_width("void **") == 8
    assert CF._type_width("int") == 4
    assert CF._type_width("unsigned long") == 8
    assert CF._type_width("struct foo") is None


# ---- _coerce_sizes ----
Q = ("function at vaddr 0x101000.\n"
     "V1\tregister 0x38\t4\nV2\tstack -0x20\t8\nV3\tstack -0x40\t24\n")


def test_coerce_pointer_on_4byte_slot_narrows():
    ans = 'V1: char *\n{"V1": "char *"}'
    out = CF._coerce_sizes(Q, ans)
    assert "V1: int" in out and '"V1": "int"' in out


def test_coerce_unsigned_family_preserved():
    out = CF._coerce_sizes(Q, "V1: size_t\n")
    assert "V1: uint" in out


def test_coerce_never_widens():
    out = CF._coerce_sizes(Q, "V2: int\n")            # int on an 8B slot: ambiguous, keep
    assert "V2: int" in out


def test_coerce_aggregate_slot_to_array():
    out = CF._coerce_sizes(Q, "V3: int *\n")
    assert "V3: int[6]" in out


def test_coerce_disabled_by_env(monkeypatch):
    monkeypatch.setenv("AGENTIC_NO_SIZE_COERCE", "1")
    assert CF._coerce_sizes(Q, "V1: char *\n") == "V1: char *\n"


# ---- _rescue_undefined ----
def _msgs(msg, worker_text):
    return [msg(type="tool", content=worker_text, tool_call_id="t1")]


def test_rescue_restores_specific_over_undefined(msg):
    out = CF._rescue_undefined(_msgs(msg, "V1: char *\n"), "V1: undefined8\n")
    assert "V1: char *" in out


def test_rescue_appends_absent_entity(msg):
    out = CF._rescue_undefined(_msgs(msg, "V1: char *\nV2: int\n"), "V1: long\n")
    assert "V1: long" in out                           # specific answer untouched
    assert "V2: int" in out                            # absent -> appended


def test_rescue_keeps_concrete_final_answer(msg):
    out = CF._rescue_undefined(_msgs(msg, "V1: char *\n"), "V1: FILE *\n")
    assert "V1: FILE *" in out and "char *" not in out


def test_rescue_disabled_by_env(msg, monkeypatch):
    monkeypatch.setenv("AGENTIC_NO_UNDEF_RESCUE", "1")
    out = CF._rescue_undefined(_msgs(msg, "V1: char *\n"), "V1: undefined8\n")
    assert out == "V1: undefined8\n"


def test_rescue_rewrites_json_form_too(msg):
    out = CF._rescue_undefined(_msgs(msg, "V1: char *\n"),
                               'V1: undefined8\n{"V1": "undefined8"}')
    assert '"V1": "char *"' in out


# ---- _certified_trailer claim modes (oracle facts monkeypatched in) ----
def _trailer(monkeypatch, facts, answer, question=Q):
    monkeypatch.setattr(CF, "_collect_oracle_facts", lambda oid, q, o: facts)
    return CF._certified_trailer("oid", question, answer, {})


def test_trailer_exact_overrides(monkeypatch):
    out = _trailer(monkeypatch, {"V2": ("FILE *", "o", "exact")}, "V2: long\n")
    assert "ORACLE-CERTIFIED" in out and "- V2: FILE *" in out


def test_trailer_floor_defers_to_model_pointer(monkeypatch):
    out = _trailer(monkeypatch, {"V2": ("void *", "o", "floor")}, "V2: char *\n")
    assert "ORACLE-CERTIFIED" not in out


def test_trailer_floor_applies_to_scalar_answer(monkeypatch):
    out = _trailer(monkeypatch, {"V2": ("void *", "o", "floor")}, "V2: long\n")
    assert "- V2: void *" in out


def test_trailer_shape_defers_to_named_pointee(monkeypatch):
    shape = "struct t1 { int field_0; } *"
    out = _trailer(monkeypatch, {"V2": (shape, "o", "shape")}, "V2: Hash_table *\n")
    assert "ORACLE-CERTIFIED" not in out


def test_trailer_shape_replaces_shapeless(monkeypatch):
    shape = "struct t1 { int field_0; } *"
    for weak in ("void *", "struct *", "long"):
        out = _trailer(monkeypatch, {"V2": (shape, "o", "shape")}, f"V2: {weak}\n")
        assert f"- V2: {shape}" in out


def test_trailer_scalar_only_demotes_pointers(monkeypatch):
    out = _trailer(monkeypatch, {"V2": ("long", "o", "scalar")}, "V2: char *\n")
    assert "- V2: long" in out
    out = _trailer(monkeypatch, {"V2": ("long", "o", "scalar")}, "V2: size_t\n")
    assert "ORACLE-CERTIFIED" not in out              # model already has an integer -> defer


def test_trailer_sign_applies_only_to_scalars(monkeypatch):
    out = _trailer(monkeypatch, {"V2": ("uint64_t", "o", "sign")}, "V2: long\n")
    assert "- V2: uint64_t" in out
    for skip in ("char *", "int[6]"):
        out = _trailer(monkeypatch, {"V2": ("uint64_t", "o", "sign")}, f"V2: {skip}\n")
        assert "ORACLE-CERTIFIED" not in out


def test_trailer_reads_final_json_over_lines(monkeypatch):
    # the LAST JSON object is the synthesized answer; the floor must see the pointer there
    ans = 'V2: long\n{"V2": "char *"}'
    out = _trailer(monkeypatch, {"V2": ("void *", "o", "floor")}, ans)
    assert "ORACLE-CERTIFIED" not in out


def test_trailer_no_facts_no_change(monkeypatch):
    assert _trailer(monkeypatch, {}, "V2: long\n") == "V2: long\n"


# ---- offline end-to-end _collect_oracle_facts (real oracles, FakeApi datastore) ----
def test_collect_oracle_facts_end_to_end(oxide_stub, q_tabs):
    facts = CF._collect_oracle_facts("testoid", q_tabs, {})
    # decompiler_pointer reads `char *param_1` from the fake decompilation for V1 (8B: allowed)
    assert facts.get("V1") == ("char *", "decompiler_pointer", "exact")
    # ...and `char *param_2` for V2 -- but V2 is a 4-BYTE slot: the size guard must drop it
    assert "V2" not in facts


def test_collect_oracle_facts_size_guard_disabled(oxide_stub, q_tabs, monkeypatch):
    monkeypatch.setenv("AGENTIC_NO_SIZE_GUARD", "1")
    facts = CF._collect_oracle_facts("testoid", q_tabs, {})
    assert facts.get("V2", ("",))[0] == "char *"        # guard off -> unsound fact passes


def test_no_certify_flag_semantics(monkeypatch):
    monkeypatch.delenv("AGENTIC_NO_CERTIFY", raising=False)
    assert CF._no_certify() is True                    # default: reviewer applies oracles
    monkeypatch.setenv("AGENTIC_NO_CERTIFY", "0")
    assert CF._no_certify() is False


def test_verifier_oracles_flag_semantics(monkeypatch):
    monkeypatch.delenv("AGENTIC_VERIFIER_ORACLES", raising=False)
    assert CF._verifier_oracles() is True
    monkeypatch.setenv("AGENTIC_VERIFIER_ORACLES", "0")
    assert CF._verifier_oracles() is False


def test_oracle_tool_hint_matches_roster():
    hint = CF._oracle_tool_hint("oid", "0x1", {"decompile", "signedness", "callee_signature"})
    assert "callee_signature" in hint
    assert "decompiler_pointer" not in hint            # not in roster -> not described
    # NOTE: signedness has no _ORACLE_TOOL_BLURB entry, so the hint never describes it even when
    # rostered (the model still sees its MCP description). Documented behavior, not an endorsement.
    assert "signedness" not in hint
    assert CF._oracle_tool_hint("oid", "0x1", {"decompile"}) == ""
