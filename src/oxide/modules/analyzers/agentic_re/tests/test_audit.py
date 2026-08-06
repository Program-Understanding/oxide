"""The evidence audit: agreement semantics, labelling, and the retroactive run pass.

Every row of the paper's agreement column is pinned here. Agreement is NOT the override rule, and
the tests that assert the difference (`test_shape_agrees_with_any_pointer_though_it_would_override`,
`test_sign_agrees_with_any_unsigned_scalar`) are the ones that would catch a future refactor
collapsing the two readings.
"""
import json

import pytest

from agentic.tasks.type_recovery import audit as A


# ---- type predicates ----
def test_is_pointer():
    assert A.is_pointer("char *") and A.is_pointer("void **") and A.is_pointer("FILE*")
    assert not A.is_pointer("int") and not A.is_pointer("") and not A.is_pointer("int[6]")


def test_is_array():
    assert A.is_array("int[6]") and A.is_array("char [12]")
    assert not A.is_array("int") and not A.is_array("char *")


def test_is_unsigned_scalar():
    for t in ("unsigned int", "uint32_t", "size_t", "ulong", "uchar", "unsigned long"):
        assert A.is_unsigned_scalar(t), t
    for t in ("int", "long", "char", "char *", "unsigned char[4]", ""):
        assert not A.is_unsigned_scalar(t), t


# ---- agree(): one test per row of the agreement column ----
def test_exact_agrees_only_with_the_same_type():
    assert A.agree("exact", "char *", "char *") is True
    assert A.agree("exact", "char *", "char*") is True          # spacing is not a disagreement
    assert A.agree("exact", "char *", "FILE *") is False
    assert A.agree("exact", "int", "long") is False


def test_floor_agrees_with_any_pointer():
    assert A.agree("floor", "void *", "char *") is True
    assert A.agree("floor", "void *", "Hash_table *") is True   # not depth- or pointee-aware
    assert A.agree("floor", "void *", "long") is False


def test_shape_agrees_with_any_pointer_though_it_would_override():
    """A shape claim OVERRIDES a shapeless pointer but AGREES with it: the audit records
    violations, not missed refinements. This is the case where the two columns differ."""
    shape = "struct t1 { int field_0; } *"
    assert A.agree("shape", shape, "void *") is True
    assert A.agree("shape", shape, "Hash_table *") is True
    assert A.agree("shape", shape, "long") is False


def test_scalar_agrees_with_any_non_pointer():
    assert A.agree("scalar", "long", "int") is True
    assert A.agree("scalar", "long", "size_t") is True
    assert A.agree("scalar", "long", "char *") is False


def test_sign_agrees_with_any_unsigned_scalar():
    """Also a differing-columns case: sign refines an unsigned answer of the wrong width, but
    agrees with it."""
    assert A.agree("sign", "uint64_t", "unsigned int") is True
    assert A.agree("sign", "uint64_t", "size_t") is True
    assert A.agree("sign", "uint64_t", "long") is False
    assert A.agree("sign", "uint64_t", "char *") is False


def test_agree_abstains_on_empty_answer_and_unknown_mode():
    assert A.agree("exact", "int", "") is None
    assert A.agree("exact", "int", None) is None
    assert A.agree("nonsense_mode", "int", "int") is None


# ---- audit() ----
def test_unsupported_when_no_claim():
    out = A.audit({}, {"V1": "int"})
    assert out["V1"]["label"] == "unsupported" and out["V1"]["claims"] == []


def test_corroborated_when_all_claims_agree():
    facts = {"V1": [["void *", "decompiler_pointer", "floor"],
                    ["char *", "callee_signature", "exact"]]}
    out = A.audit(facts, {"V1": "char *"})
    assert out["V1"]["label"] == "corroborated" and out["V1"]["disagreeing"] == []


def test_contradicted_when_any_claim_disagrees():
    facts = {"V1": [["void *", "decompiler_pointer", "floor"],
                    ["FILE *", "callee_signature", "exact"]]}
    out = A.audit(facts, {"V1": "char *"})
    assert out["V1"]["label"] == "contradicted"
    assert [d["oracle"] for d in out["V1"]["disagreeing"]] == ["callee_signature"]


def test_accepts_the_single_claim_record_shape():
    """`_collect_oracle_facts` writes {vid: [ctype, oracle, mode]} (first-wins). The audit must read
    that shape too, so it can run retroactively over already-completed runs."""
    out = A.audit({"V1": ["void *", "decompiler_pointer", "floor"]}, {"V1": "char *"})
    assert out["V1"]["label"] == "corroborated"


def test_unanswered_variable_is_labelled_not_dropped():
    out = A.audit({"V9": ["void *", "spilled_param", "floor"]}, {})
    assert "V9" in out and out["V9"]["label"] == "corroborated"   # empty answer never disagrees


def test_variables_absent_from_facts_are_unsupported():
    out = A.audit({"V1": ["int", "o", "exact"]}, {"V1": "int", "V2": "long"})
    assert out["V1"]["label"] == "corroborated"
    assert out["V2"]["label"] == "unsupported"


# ---- summarize() ----
def test_summarize_counts_and_reach():
    labels = A.audit({"V1": ["char *", "o", "exact"], "V2": ["int", "o", "exact"]},
                     {"V1": "char *", "V2": "long", "V3": "int"})
    s = A.summarize(labels)
    assert (s["n"], s["corroborated"], s["contradicted"], s["unsupported"]) == (3, 1, 1, 1)
    assert s["reached_pct"] == pytest.approx(66.67, abs=0.01)


def test_summarize_empty():
    assert A.summarize({})["n"] == 0


# ---- audit_run() over a run directory ----
def test_audit_run_writes_a_record(tmp_path):
    (tmp_path / "oracle_claims_f.json").write_text(json.dumps(
        {"V1": [["char *", "callee_signature", "exact"]], "V2": [["void *", "spilled", "floor"]]}))
    (tmp_path / "pred_f.json").write_text(json.dumps({"V1": "char *", "V2": "long", "V3": "int"}))
    rec = A.audit_run(str(tmp_path), "f")
    assert rec["summary"]["corroborated"] == 1
    assert rec["summary"]["contradicted"] == 1
    assert rec["summary"]["unsupported"] == 1
    on_disk = json.loads((tmp_path / "audit_f.json").read_text())
    assert on_disk["variables"]["V2"]["label"] == "contradicted"


def test_audit_run_falls_back_to_the_oracles_dump(tmp_path):
    """Older runs have only `oracles_<fn>.json`; the audit must still work on them.
    `claims_<fn>.json` is deepagent's PER-AGENT ledger and must never be read as oracle facts."""
    (tmp_path / "oracles_f.json").write_text(json.dumps({"V1": ["char *", "cs", "exact"]}))
    (tmp_path / "pred_f.json").write_text(json.dumps({"V1": "char *"}))
    assert A.audit_run(str(tmp_path), "f")["summary"]["corroborated"] == 1


def test_audit_run_tolerates_missing_files(tmp_path):
    assert A.audit_run(str(tmp_path), "nothing")["summary"]["n"] == 0
