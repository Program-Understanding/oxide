"""MCP server helpers (mcp_agentic.py): argument normalization, memoization/logging, and import
masking. Imported WITHOUT starting the server or Oxide -- the module's Oxide imports are stubbed."""
import json
import sys
import types

import pytest


@pytest.fixture
def mcp(monkeypatch, fake_api):
    """Import mcp_agentic with its Oxide/FastMCP imports satisfied by stubs."""
    import os
    # argparse in the module reads sys.argv
    monkeypatch.setattr(sys, "argv", ["mcp_agentic.py", "--oxidepath=/nonexistent"])

    ox = types.ModuleType("oxide")
    core = types.ModuleType("oxide.core")
    oxo = types.ModuleType("oxide.core.oxide")
    oxo.api = fake_api
    core.oxide = oxo
    ox.core = core
    for name, mod in (("oxide", ox), ("oxide.core", core), ("oxide.core.oxide", oxo)):
        monkeypatch.setitem(sys.modules, name, mod)

    sys.modules.pop("mcp_agentic", None)
    path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "agentic")
    if path not in sys.path:
        sys.path.insert(0, path)
    import importlib
    m = importlib.import_module("mcp_agentic")
    m._CT_CACHE.clear()
    m._TOOL_RESULT_CACHE.clear()
    m._SEEN.clear()
    m._IMPORT_MASK.clear()
    yield m
    sys.modules.pop("mcp_agentic", None)


def test_norm_addr(mcp):
    assert mcp._norm_addr("0x00103108") == "0x103108"
    assert mcp._norm_addr("103108") == "0x103108"
    assert mcp._norm_addr("0X103108") == "0x103108"
    assert mcp._norm_addr("funcA") == "funcA"
    assert mcp._norm_addr(None) is None


def test_norm_off(mcp):
    assert mcp._norm_off("-0x08") == "-0x8"
    assert mcp._norm_off("0x20") == "0x20"
    assert mcp._norm_off("") == ""
    assert mcp._norm_off("weird") == "weird"


def test_as_json(mcp):
    assert mcp._as_json('{"a": 1}') == {"a": 1}
    assert mcp._as_json("not json") == "not json"


def test_call_memoizes_identical_args(mcp):
    a = mcp._call("testoid", "stack_var", {"addr": "0x101000"})
    b = mcp._call("testoid", "stack_var", {"addr": "0x101000"})
    assert a == b
    assert len(mcp._TOOL_RESULT_CACHE) == 1


def test_call_normalized_addresses_share_cache_key(mcp):
    mcp._call("testoid", "stack_var", {"addr": mcp._norm_addr("0x00101000")})
    mcp._call("testoid", "stack_var", {"addr": mcp._norm_addr("0x101000")})
    assert len(mcp._TOOL_RESULT_CACHE) == 1


def test_call_tracks_seen_offsets(mcp):
    mcp._call("testoid", "stack_var", {"addr": "0x101000", "offset": "-0x20"})
    assert "-0x20" in mcp._SEEN["testoid"]["offsets"]


def test_tool_log_records_calls(mcp, tmp_path, monkeypatch):
    p = tmp_path / "tools.jsonl"
    monkeypatch.setenv("AGENTIC_TOOL_LOG", str(p))
    mcp._call("testoid", "stack_var", {"addr": "0x101000"})
    mcp._call("testoid", "stack_var", {"addr": "0x101000"})
    rows = [json.loads(l) for l in p.read_text().splitlines()]
    assert [r["cached"] for r in rows] == [False, True]
    assert all(r["tool"] == "stack_var" for r in rows)


def test_tool_log_absent_when_unset(mcp, monkeypatch):
    monkeypatch.delenv("AGENTIC_TOOL_LOG", raising=False)
    mcp._call("testoid", "stack_var", {"addr": "0x101000"})     # must not raise


def test_repeat_breaker_appends_hint(mcp, monkeypatch):
    monkeypatch.setenv("AGENTIC_REPEAT_BREAKER", "1")
    mcp._call("testoid", "stack_var", {"addr": "0x101000"})
    second = mcp._call("testoid", "stack_var", {"addr": "0x101000"})
    assert "[REPEAT]" in str(second)


def test_repeat_breaker_off_by_default(mcp, monkeypatch):
    monkeypatch.delenv("AGENTIC_REPEAT_BREAKER", raising=False)
    mcp._call("testoid", "stack_var", {"addr": "0x101000"})
    assert "[REPEAT]" not in str(mcp._call("testoid", "stack_var", {"addr": "0x101000"}))


def test_mask_imports_replaces_names(mcp, monkeypatch):
    monkeypatch.setenv("AGENTIC_MASK_IMPORTS", "1")
    out = str(mcp._mask_imports("testoid", "call strlen ; then return"))
    assert "strlen" not in out and "EXT_" in out


def test_mask_imports_off_by_default(mcp, monkeypatch):
    monkeypatch.delenv("AGENTIC_MASK_IMPORTS", raising=False)
    assert mcp._mask_imports("testoid", "call strlen") == "call strlen"


def test_mask_imports_keeps_runtime_scaffolding(mcp, monkeypatch):
    monkeypatch.setenv("AGENTIC_MASK_IMPORTS", "1")
    out = str(mcp._mask_imports("testoid", "call __stack_chk_fail"))
    assert "__stack_chk_fail" in out


def test_published_tool_set(mcp):
    """The server must publish exactly the tools the agent rosters name."""
    published = {n for n in dir(mcp)
                 if not n.startswith("_") and callable(getattr(mcp, n, None))}
    for t in ("decompile", "disassemble", "stack_var", "register_usage", "value_usage",
              "xrefs_to", "read_values", "static_type_oracles", "callee_signature",
              "decompiler_pointer", "spilled_param", "interprocedural_param_usage", "signedness"):
        assert t in published, t


def test_roster_names_are_all_published(mcp):
    from agentic import deepagent as D
    published = {n for n in dir(mcp) if not n.startswith("_")}
    wanted = D.WORKER_TOOLS | D.VERIFIER_TOOLS | D.ORACLE_TOOLS | D.ORACLE_TOOLS_INDIVIDUAL
    assert wanted <= published, sorted(wanted - published)
