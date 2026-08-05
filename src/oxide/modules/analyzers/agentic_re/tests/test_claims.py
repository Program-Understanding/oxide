"""Per-stage claim capture (claims.py): extraction from tool results and per-agent attribution."""
from agentic import claims as CL


def test_claims_from_messages_lines_and_json(msg):
    msgs = [
        msg(type="ai", content="delegating"),
        msg(type="tool", content="V1: char *\n- V2: int\nnoise line\n"),
        msg(type="tool", content='done. {"V3": "FILE *", "not_a_vid": "x"}'),
    ]
    out = CL._claims_from_messages(msgs)
    assert out == [{"V1": "char *", "V2": "int"}, {"V3": "FILE *"}]


def test_claims_strips_backticks_and_parenthetical(msg):
    msgs = [msg(type="tool", content="V1: `char *`\nV2: int (spilled from esi)\n")]
    assert CL._claims_from_messages(msgs) == [{"V1": "char *", "V2": "int"}]


def test_claims_ignores_overlong_types(msg):
    msgs = [msg(type="tool", content=f"V1: {'x' * 60}\n")]
    assert CL._claims_from_messages(msgs) == []


def test_claims_by_agent_attribution(msg):
    task_call = {"name": "task", "id": "call_1",
                 "args": {"subagent_type": "type_worker", "description": "types for V1..V2"}}
    msgs = [
        msg(type="ai", tool_calls=[task_call]),
        msg(type="tool", content="V1: char *\n", tool_call_id="call_1"),
        msg(type="tool", content="V2: int\n", tool_call_id="call_unknown"),
    ]
    out = CL._claims_by_agent(msgs)
    assert out[0]["agent"] == "type_worker"
    assert out[0]["brief"] == "types for V1..V2"
    assert out[0]["claims"] == {"V1": "char *"}
    assert out[1]["agent"] == "?"                     # unmatched tool result still captured


def test_dump_tool_calls_disabled_is_silent(msg, capsys, monkeypatch):
    monkeypatch.delenv("AGENTIC_DUMP_TOOLCALLS", raising=False)
    CL._dump_tool_calls([msg(type="ai", tool_calls=[{"name": "decompile", "id": "x"}])])
    assert capsys.readouterr().out == ""


def test_dump_tool_calls_counts(msg, capsys, monkeypatch):
    monkeypatch.setenv("AGENTIC_DUMP_TOOLCALLS", "1")
    CL._dump_tool_calls([
        msg(type="ai", tool_calls=[{"name": "decompile", "id": "x"},
                                   {"name": "decompile", "id": "y"}]),
    ])
    assert "{'decompile': 2}" in capsys.readouterr().out


def test_log_claims_writes_file(msg, tmp_path, monkeypatch):
    p = tmp_path / "claims.json"
    monkeypatch.setenv("AGENTIC_CLAIM_LOG", str(p))
    task_call = {"name": "task", "id": "c1", "args": {"subagent_type": "verifier"}}
    CL._log_claims([msg(type="ai", tool_calls=[task_call]),
                    msg(type="tool", content="V1: long\n", tool_call_id="c1")])
    import json
    data = json.loads(p.read_text())
    assert data[0]["agent"] == "verifier" and data[0]["claims"] == {"V1": "long"}
