"""Driver-side helpers in deepagent.py that need no model and no graph: tool-call salvage, channel
stripping, prose-tool-call detection, roster filtering, the loop cap, and the scaling rules."""
import pytest

from agentic import deepagent as D


# ---- _strip_channel ----
def test_strip_channel_paired_block():
    assert D._strip_channel("<|channel|>thinking hard<|channel|>V1: char *") == "V1: char *"


def test_strip_channel_residual_tokens():
    assert D._strip_channel("<|start|>V1: int<|end|>") == "V1: int"


def test_strip_channel_bare_thought_line():
    assert D._strip_channel("thought\nV1: int") == "V1: int"


def test_strip_channel_passthrough():
    assert D._strip_channel("V1: char *") == "V1: char *"
    assert D._strip_channel("") == ""
    assert D._strip_channel(None) is None


# ---- _parse_call_args ----
def test_parse_call_args_python_style():
    assert D._parse_call_args('oid="abc", addr="0x1000"') == {"oid": "abc", "addr": "0x1000"}


def test_parse_call_args_numeric_and_bool():
    got = D._parse_call_args('addr="0x1", n_instructions=128, signed=True')
    assert got == {"addr": "0x1", "n_instructions": 128, "signed": True}


def test_parse_call_args_regex_fallback():
    # unparseable as Python -> regex path still recovers the pairs
    got = D._parse_call_args('oid=abc123, addr=0x1000')
    assert got["oid"] == "abc123" and got["addr"] == "0x1000"


# ---- _salvage_message ----
def test_salvage_converts_raw_text_toolcall():
    """The PIPELESS delimiter form, which survives channel stripping and is salvaged."""
    msg = D._salvage_message(_ai('<tool_call>call:decompile(oid="o", addr="0x1")</tool_call>'))
    assert [tc["name"] for tc in msg.tool_calls] == ["decompile"]
    assert msg.tool_calls[0]["args"] == {"oid": "o", "addr": "0x1"}


def test_gemma_regex_matches_the_piped_form_in_isolation():
    """_GEMMA_TC_RE itself handles the piped syntax its docstring documents..."""
    raw = '<|tool_call>call:decompile(oid="o", addr="0x1")<tool_call|>'
    assert D._GEMMA_TC_RE.search(raw)


@pytest.mark.xfail(reason="LATENT BUG found 2026-08-04 by this suite: _salvage_message runs "
                          "_strip_channel FIRST, whose `<\\|[^>]*>|<[^>]*\\|>` rule deletes the "
                          "pipe-wrapped delimiters, so _GEMMA_TC_RE can never match the exact "
                          "`<|tool_call>...<tool_call|>` syntax its own docstring cites as the "
                          "observed model output. Only the pipeless form is salvageable today. "
                          "Fix = run the tool-call parse BEFORE the channel strip (or have "
                          "_strip_channel preserve tool_call delimiters).",
                   strict=False)
def test_salvage_converts_piped_raw_text_toolcall():
    msg = D._salvage_message(_ai('<|tool_call>call:decompile(oid="o", addr="0x1")<tool_call|>'))
    assert [tc["name"] for tc in msg.tool_calls] == ["decompile"]


def test_salvage_keeps_structured_calls_and_cleans_text():
    m = _ai("<|channel|>x<|channel|>ok", tool_calls=[{"name": "decompile", "args": {},
                                                     "id": "1", "type": "tool_call"}])
    out = D._salvage_message(m)
    assert out.content == "ok" and len(out.tool_calls) == 1


def test_salvage_noop_on_clean_message():
    m = _ai("V1: char *")
    assert D._salvage_message(m) is m


def _ai(content, tool_calls=None):
    from langchain_core.messages import AIMessage
    return AIMessage(content=content, tool_calls=tool_calls or [])


# ---- _text_toolcall_name ----
class _M:
    def __init__(self, content, tool_calls=None):
        self.content = content
        self.tool_calls = tool_calls or []


def test_text_toolcall_detected_when_offered():
    m = _M("call:task{description: recover types for V1}")
    assert D._text_toolcall_name(m, {"task"}) == "task"


def test_text_toolcall_ignored_when_not_offered():
    m = _M("call:write_todos{...}")
    assert D._text_toolcall_name(m, {"task"}) is None


def test_text_toolcall_ignored_when_structured_call_present():
    m = _M("call:task{...}", tool_calls=[{"name": "task"}])
    assert D._text_toolcall_name(m, {"task"}) is None


def test_text_toolcall_requires_line_start():
    assert D._text_toolcall_name(_M("I would call:task{x}"), {"task"}) is None


# ---- roster filtering ----
def test_name_of_both_shapes():
    assert D._name_of({"function": {"name": "decompile"}}) == "decompile"
    assert D._name_of({"name": "stack_var"}) == "stack_var"


def test_restrict_tools_drops_unlisted():
    kwargs = {"tools": [{"function": {"name": "task"}}, {"function": {"name": "write_todos"}}]}
    out = D._restrict_tools(kwargs, {"task"})
    assert [D._name_of(t) for t in out["tools"]] == ["task"]


def test_restrict_tools_noop_when_all_allowed():
    kwargs = {"tools": [{"function": {"name": "task"}}]}
    assert D._restrict_tools(kwargs, {"task"}) is kwargs


def test_restrict_tools_keeps_all_when_filter_would_empty():
    kwargs = {"tools": [{"function": {"name": "task"}}]}
    out = D._restrict_tools(kwargs, {"nonexistent"})
    assert len(out["tools"]) == 1                       # never send a request with zero tools


def test_tool_names():
    assert D._tool_names({"tools": [{"function": {"name": "a"}}, {"name": "b"}]}) == {"a", "b"}


def test_forced_kwargs():
    kw = D._forced_kwargs({"tools": []}, "task")
    assert kw["tool_choice"] == {"type": "function", "function": {"name": "task"}}


# ---- _cap_tool_loop ----
class _AI:
    type = "ai"

    def __init__(self, names):
        self.tool_calls = [{"name": n, "id": "x"} for n in names]


def test_cap_not_reached(monkeypatch):
    monkeypatch.setenv("AGENTIC_MAX_TOOL_TURNS", "10")
    msgs = [_AI(["disassemble"])] * 3
    out_msgs, out_kw = D._cap_tool_loop(msgs, {"tools": [{"name": "disassemble"}]})
    assert out_msgs is msgs and "tools" in out_kw


def test_cap_strips_tools_and_injects_directive(monkeypatch):
    monkeypatch.setenv("AGENTIC_MAX_TOOL_TURNS", "3")
    msgs = [_AI(["disassemble"])] * 3
    out_msgs, out_kw = D._cap_tool_loop(msgs, {"tools": [{"name": "disassemble"}]})
    assert "tools" not in out_kw
    assert len(out_msgs) == 4
    assert "Do NOT call any more tools" in out_msgs[-1].content


def test_cap_excludes_delegations(monkeypatch):
    # `task` turns are fan-out, not looping: 20 delegations must NOT trip a cap of 3
    monkeypatch.setenv("AGENTIC_MAX_TOOL_TURNS", "3")
    msgs = [_AI(["task"])] * 20
    out_msgs, out_kw = D._cap_tool_loop(msgs, {"tools": [{"name": "task"}]})
    assert out_msgs is msgs and "tools" in out_kw


def test_cap_noop_without_tools():
    msgs = [_AI(["disassemble"])] * 50
    out_msgs, out_kw = D._cap_tool_loop(msgs, {})
    assert out_msgs is msgs


# ---- group-size / grouping-rule / inventory scaling ----
def _q(n):
    head = "function at vaddr 0x1000.\n"
    return head + "".join(f"V{i}\tstack -0x{i:x}\t8\n" for i in range(1, n + 1))


def test_group_size_small_function_constant():
    assert D._group_size(_q(6)) == 6
    assert D._group_size(_q(36)) == 6


def test_group_size_scales_above_threshold():
    assert D._group_size(_q(180)) == 30                # ceil(180/6) -> ~6 delegations
    assert D._group_size(_q(60)) == 10


def test_grouping_rule_wording():
    assert D._grouping_rule(_q(6)) == "into groups of up to 6."
    assert D._grouping_rule(_q(180)) == "into groups of up to 30."


def test_inventory_parses_variables_block():
    q = "function at vaddr 0x1.\nV1\tregister 0x38\t8\nV2\tstack -0x20\t4\n"
    assert D._inventory(q) == [("V1", "register 0x38", "8"), ("V2", "stack -0x20", "4")]


# ---- prompt/config plumbing ----
def test_verifier_prompt_switches_on_flag(monkeypatch):
    monkeypatch.delenv("AGENTIC_VERIFIER_ABI", raising=False)
    assert D._verifier_prompt() is D.VERIFIER_PROMPT
    monkeypatch.setenv("AGENTIC_VERIFIER_ABI", "1")
    assert D._verifier_prompt() is D.VERIFIER_PROMPT_ABI


def test_coordinator_prompt_formats():
    txt = D.COORDINATOR_PROMPT.format(oid="o", vaddr="0x1", grouping_rule="into groups of up to 6.")
    assert "0x1" in txt and "into groups of up to 6." in txt and "{" not in txt.split("e.g.")[0]


def test_worker_and_verifier_prompts_format():
    assert "0x1" in D.TYPE_WORKER_PROMPT.format(oid="o", vaddr="0x1")
    assert "0x1" in D.VERIFIER_PROMPT.format(oid="o", vaddr="0x1")
    assert "register 0x38 = RDI" in D.VERIFIER_PROMPT_ABI.format(oid="o", vaddr="0x1")


def test_mcp_env_passthrough(monkeypatch):
    for k in ("AGENTIC_TOOL_LOG", "AGENTIC_REPEAT_BREAKER", "AGENTIC_DISASM_PAGING_HINT",
              "AGENTIC_MASK_IMPORTS", "AGENTIC_LIBC"):
        monkeypatch.delenv(k, raising=False)
    assert D._mcp_env() is None
    monkeypatch.setenv("AGENTIC_TOOL_LOG", "/tmp/x.jsonl")
    env = D._mcp_env()
    assert env is not None and env["AGENTIC_TOOL_LOG"] == "/tmp/x.jsonl"


def test_default_oracles_comes_from_task_module():
    assert D._DEFAULT_ORACLES() == (
        "callee_signature,decompiler_pointer,interprocedural_param_usage,spilled_param")


def test_worker_roster_excludes_decompiler_lens():
    # the two-lens split: the assembly worker must never hold decompile/value_usage
    assert "decompile" not in D.WORKER_TOOLS and "value_usage" not in D.WORKER_TOOLS
    assert "decompile" in D.VERIFIER_TOOLS and "value_usage" in D.VERIFIER_TOOLS


def test_combined_oracle_excluded_from_individual_roster():
    assert "static_type_oracles" not in D.ORACLE_TOOLS_INDIVIDUAL
    assert "static_type_oracles" not in D._VERIFIER_TOOLS_ORACLE
