"""Tool registry + dispatch: schemas, name mangling tolerance, memoization, output capping,
and the oracle tool wrappers' registration shape."""
import pytest

from agentic.tools import registry as R


def test_registry_populated():
    for name in ("decompile", "disassemble", "stack_var", "register_usage", "value_usage",
                 "xrefs_to", "read_values", "struct_shape"):
        assert name in R.REGISTRY, name


def test_schema_shape():
    spec = R.REGISTRY["stack_var"]
    fn = spec.schema["function"]
    assert spec.schema["type"] == "function"
    assert fn["name"] == "stack_var"
    assert "addr" in fn["parameters"]["properties"]
    assert fn["parameters"]["required"] == ["addr"]
    assert fn["description"]


def test_all_schemas_matches_registry():
    assert len(R.all_schemas()) == len(R.REGISTRY)


# ---- every oracle tool must be registered uniformly (the fix for `signedness`) ----
ORACLE_TOOLS = ["static_type_oracles", "callee_signature", "decompiler_pointer",
                "spilled_param", "interprocedural_param_usage", "signedness"]


@pytest.mark.parametrize("name", ORACLE_TOOLS)
def test_oracle_tool_registered_in_oracle_group(name):
    import agentic.tasks.type_recovery  # noqa: F401  registers the oracle tool wrappers
    spec = R.REGISTRY[name]
    assert spec.group == "oracle", f"{name} group={spec.group!r}"


@pytest.mark.parametrize("name", ORACLE_TOOLS)
def test_oracle_tool_declares_params(name):
    import agentic.tasks.type_recovery  # noqa: F401
    props = R.REGISTRY[name].schema["function"]["parameters"]
    assert {"addr", "variables"} <= set(props["properties"]), name
    assert {"addr", "variables"} <= set(props["required"]), name


@pytest.mark.parametrize("name", ORACLE_TOOLS)
def test_oracle_tool_has_description(name):
    import agentic.tasks.type_recovery  # noqa: F401
    desc = R.REGISTRY[name].schema["function"]["description"]
    assert desc and len(desc) > 40 and "\n" not in desc.strip()[:1], name


def test_oracle_group_selectable():
    import agentic.tasks.type_recovery  # noqa: F401
    from agentic import tools as T
    names = {s["function"]["name"] for s in T.schemas(groups=["oracle"])}
    assert set(ORACLE_TOOLS) <= names          # a groups=["oracle"] roster must include them all


# ---- resolve_tool_name ----
@pytest.mark.parametrize("given,want", [
    ("decompile", "decompile"),
    ("Decompile", "decompile"),
    ("gemma_decompile", "decompile"),
    ("decompile__function", "decompile"),
    ("functions_stack_var", "stack_var"),
])
def test_resolve_tool_name(given, want):
    assert R.resolve_tool_name(given) == want


def test_resolve_tool_name_unknown():
    assert R.resolve_tool_name("") is None
    assert R.resolve_tool_name("totally_unrelated_zzz") is None


# ---- dispatch behavior ----
def test_call_tool_unknown_tool(call_tool):
    assert "no such tool" in call_tool("nope_zzz", {})


def test_call_tool_bad_args_reported(call_tool):
    out = call_tool("stack_var", {"bogus_kwarg": 1})
    assert "tool arg error" in out or "error" in out


def test_call_tool_drops_binary_path(call_tool):
    # legacy arg some prompts still emit; must be stripped rather than raise
    out = call_tool("decompile", {"addr": "0x101000", "binary_path": "/x"})
    assert "tool arg error" not in out


def test_memoize_returns_repeat_stub(fake_api):
    from agentic import tools as T
    _s, ct = T.build_tools(fake_api, "oid", memoize=True)
    first = ct("stack_var", {"addr": "0x101000"})
    second = ct("stack_var", {"addr": "0x101000"})
    assert "REPEAT CALL" in second and "REPEAT CALL" not in first


def test_no_memoize_returns_full_output_twice(fake_api):
    from agentic import tools as T
    _s, ct = T.build_tools(fake_api, "oid", memoize=False)
    assert ct("stack_var", {"addr": "0x101000"}) == ct("stack_var", {"addr": "0x101000"})


def test_out_cap_truncates(fake_api, monkeypatch):
    monkeypatch.setenv("AGENTIC_OUT_CAP", "20")
    from agentic import tools as T
    _s, ct = T.build_tools(fake_api, "oid", memoize=False)
    assert len(ct("stack_var", {"addr": "0x101000"})) <= 20


def test_out_cap_zero_is_unlimited(fake_api, monkeypatch):
    monkeypatch.setenv("AGENTIC_OUT_CAP", "0")
    from agentic import tools as T
    _s, ct = T.build_tools(fake_api, "oid", memoize=False)
    assert len(ct("stack_var", {"addr": "0x101000"})) > 20


def test_build_tools_group_filter(fake_api):
    from agentic import tools as T
    schemas, _ct = T.build_tools(fake_api, "oid", groups=["elf"], memoize=False)
    names = {s["function"]["name"] for s in schemas}
    assert "read_values" in names and "decompile" not in names


# ---- grounding registry ----
def test_domain_oracles_registered():
    import agentic.tasks.type_recovery  # noqa: F401
    from agentic import grounding as G
    for n in ("callee_signature", "decompiler_pointer", "spilled_param",
              "interprocedural_param_usage", "signedness", "struct_shape"):
        assert n in G.DOMAIN_ORACLES, n


def test_resolve_domain_oracles_order_and_forms():
    import agentic.tasks.type_recovery  # noqa: F401
    from agentic import grounding as G
    got = [n for n, _fn in G.resolve_domain_oracles("spilled_param,callee_signature")]
    assert got == ["spilled_param", "callee_signature"]        # order is significant
    assert [n for n, _ in G.resolve_domain_oracles(["signedness"])] == ["signedness"]
    assert [n for n, _ in G.resolve_domain_oracles("nonexistent_zzz")] == []
    assert len(G.resolve_domain_oracles("auto")) >= 6


def test_default_oracles_excludes_signedness_and_struct_shape():
    # both are opt-in (reviewer-selected tools), NOT in the in-process default set
    from agentic.tasks.type_recovery import DEFAULT_ORACLES
    assert "signedness" not in DEFAULT_ORACLES and "struct_shape" not in DEFAULT_ORACLES
