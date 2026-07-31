"""deepagents-based multi-agent driver for agentic RE.

Replaces the custom pipeline.py orchestration (planner/worker/verify/synthesize) with a LangChain
`deepagents` multi-agent: a coordinator that delegates to specialist subagents. All tools — the
fine-grained analysis tools AND the deterministic oracle tools — come from the Oxide MCP server
(`oxide/mcp_server.py`), loaded via langchain-mcp-adapters. The model is any OpenAI-compatible
server (local vLLM) via ChatOpenAI.

P2 scope: coordinator + `type_worker` only. The `verifier` subagent and the deterministic
ORACLE-CERTIFIED trailer are added in P3 (see deepagent_trailer / run below).
"""
from __future__ import annotations

import asyncio
import contextlib
import json
import os
import re
import sys

from agentic import config as C
# Extracted to sibling modules 2026-07-30. Re-imported here so `deepagent.<name>` remains the stable
# public surface every existing caller uses (run_trex_one, characterize.py, mcp_agentic).
from agentic.claims import (_claims_from_messages, _claims_by_agent,  # noqa: F401
                            _dump_tool_calls, _log_claims)
from agentic.certify import (_ORACLE_SUFFIX, _ORACLE_TOOL_BLURB, _UNDEF_RE,  # noqa: F401
                             _oracle_tool_hint, _oracle_brief, _verifier_oracles, _no_certify,
                             _collect_oracle_facts, _rescue_undefined, _type_width, _coerce_sizes,
                             _certified_trailer)

# The tools the agent may call — all ADDRESS-based (they take the function's 0x vaddr), so they work
# on a stripped binary where the function has no symbol name (the earlier loop was caused by the LLM
# guessing function names for name-based tools like disasm_and_info_for_func). Includes the two
# deterministic oracle tools (the hybrid trust layer).
WORKER_TOOLS = {
    "disassemble", "stack_var", "xrefs_to", "read_values", "register_usage",
}
# `compute` (exact integer/bitwise arithmetic) was REMOVED 2026-07-30: it was selected 0 times in
# 321 tool calls across this session and 0 times in the earlier 1049-call audit. The arithmetic it
# existed to make safe -- converting a ground-truth frame offset to an rbp offset -- is done inside
# `stack_var` itself (`frame_delta`), so the model never needed a calculator to reach a slot.
# `register_usage` added 2026-07-27: the worker had NO tool answering "how is this REGISTER used?"
# (`stack_var` covers stack slots only), so on register groups it queried stack offsets that cannot
# exist — measured on mv/set_char_quoting: 9 calls, 6 `NOT found`, zero registers examined.
# It reads the INSTRUCTION STREAM only. Its decompiler-based counterpart `value_usage` is deliberately
# NOT here: that one calls decompile() internally, so giving it to the worker would hand the assembly
# lens the reviewer's evidence (including the function signature) through a side door and collapse the
# two-lens split. `value_usage` belongs to the reviewer, which already holds that lens.
# `compute` is never actually selected (0 calls out of 1049 over 30 functions x 2 prompt regimes —
# the only such tool; xrefs_to 17 and read_values 7 ARE used, just rarely). Dropping it from the menu
# was TRIED and REVERTED on 2026-07-26: paired 30-function A/B gave mean −0.32 (95% CI −4.54..+3.91),
# i.e. no measurable gain — while still swinging 13 of 30 functions, one by 50 points (seq/xsum3
# 66.67->16.67), purely from perturbing a prompt-fragile model with a change it never acts on. Not
# worth re-rolling every benchmark number for zero benefit. That null A/B is also the cleanest
# NOISE-FLOOR measurement we have: sigma ~= 11.8 per function, so at n=30 nothing below ~+-4.3 is
# resolvable. See [[agent-tool-selection-audit]].

COORDINATOR_PROMPT = """You are the COORDINATOR of a type-recovery team for a STRIPPED x86-64 binary \
(oid `{oid}`, target function at virtual address `{vaddr}`). You do NOT analyze code yourself — you \
PLAN and DELEGATE to the `type_worker` subagent.

Do exactly this:
1. Split the variables into groups: put ALL register parameters in one group, and split the stack \
locals {grouping_rule} Keep this plan in mind; do NOT write it down anywhere.
2. For EACH variable group, call `task` to delegate to the `type_worker` subagent. In the task \
description give it: the oid `{oid}`, the function vaddr `{vaddr}`, and the EXACT variables in that \
group (each as `V<n>  <register 0x..|stack -0x..>  <size>`). The worker returns `<id>: <C type>` \
findings for that group.
3. After every group is done, call `task` ONCE to delegate to the `verifier` subagent. Give it the \
oid `{oid}`, the vaddr `{vaddr}`, the FULL list of candidate `<id>: <C type>` claims from the workers, \
AND the original variable list (each `V<n>  <register 0x..|stack -0x..>  <size>`, copied verbatim). \
The verifier returns the adjudicated types — prefer these over the raw worker claims.
4. Output the combined answer using the verifier's adjudicated types: one `<id>: <C type>` line per \
variable, then on the VERY LAST line a single JSON object mapping every id to its type, e.g. \
{{"V1": "char *", "V2": "int"}}. Exactly one type per id; unknown => "undefined".

Your ONLY tool is `task`. Delegate groups to `type_worker`, then the candidates to \
`verifier`, then write the answer yourself. Do NOT call decompile, the oracle tools, or any analysis tool yourself."""

TYPE_WORKER_PROMPT = """You are a type-recovery specialist working from the ASSEMBLY of a STRIPPED \
x86-64 binary (oid `{oid}`, function at virtual address `{vaddr}`). You do NOT have the decompiled C \
code — infer each variable's type from the machine code alone.

For the variables you are assigned: use `disassemble(oid, addr="{vaddr}")` to read the instructions, \
`stack_var(oid, addr="{vaddr}", offset="-0x..")` to see how a stack slot is accessed, and \
`register_usage(oid, addr="{vaddr}", reg="0x..")` to see how a REGISTER PARAMETER is used \
(dereferenced? used as an address? passed to which callee?) — pass the register offset from the \
task verbatim, e.g. `reg="0x38"`; `stack_var` does NOT work for registers. Use \
`xrefs_to`/`read_values` (addr="{vaddr}") as needed. From the instruction-level evidence — \
operand widths, sign-extension (`movsx` vs `movzx`), dereferences (`mov reg,[reg]`), and the calls a \
value flows into — infer the C type. The byte size constrains it (a pointer is 8 bytes).

Report EXACTLY one `<id>: <C type>` line per assigned variable. Report ONLY your assigned ids. Do not \
re-call a tool with identical arguments; finish promptly."""

# --- candidate proposal (opt-in, AGENTIC_TOPK=N) --------------------------------------------------
# Under a SELECT-FROM-CANDIDATES architecture the agent's job changes: a downstream deterministic
# objective picks among proposals, so what matters is whether the correct type is present at all
# (recall), not whether the first guess is right (precision). Measured 2026-07-28 over 224 variables:
# the worker emits |K| = 1.0 candidates, and a fixed 8-type lattice therefore lifts recall by +26 pp
# purely by trying more things. Asking the same model, on the same evidence, for its runners-up is the
# cheapest way to turn a committing agent into a proposing one. A wrong alternative costs nothing --
# it simply loses on the objective -- which is why the instruction says so explicitly.
_TOPK_SUFFIX = """

ADDITIONALLY, for each assigned variable, give up to {n} ALTERNATIVE types you seriously considered \
but did not choose, most plausible first, on their own line:
    ALTS <id>: <type> | <type>
A later stage TESTS each alternative mechanically against the binary and keeps whichever fits best, \
so a wrong alternative costs nothing and a missing one cannot be recovered. Offer alternatives \
whenever the evidence is not decisive; do not repeat the type you chose."""


def _topk() -> int:
    """N alternatives to request per entity; 0 disables (the default, committing behaviour)."""
    try:
        return max(0, int(os.environ.get("AGENTIC_TOPK", "0")))
    except ValueError:
        return 0


def _with_topk(prompt: str) -> str:
    k = _topk()
    return prompt + _TOPK_SUFFIX.format(n=k) if k else prompt

# TOOL-SELECTION EXPERIMENT, SETTLED 2026-07-26 — two alternative worker prompts were tried and
# REMOVED. `even` gave all five tools identical fully-formed call syntax; `neutral` dropped the recipe
# entirely and told the model to pick from the tools' own MCP descriptions. Across 3 regimes / 204 tool
# calls, `xrefs_to`+`read_values`+`compute` were selected ZERO times in every one, and `neutral` lost a
# paired 30-function A/B (mean -2.08, 5 better / 12 worse / 13 tied). Conclusion: tool selection is not
# reachable through the prompt surface or the tool descriptions on this model — do not retry it here.
# See [[agent-tool-selection-audit]].

# the deterministic oracle tool exposed on the MCP server. The oracles' VALUES are applied in-process by
# the certified trailer (_collect_oracle_facts), not by the LLM — this is only what the server publishes.
ORACLE_TOOLS = {"static_type_oracles"}

# the verifier subagent's tools: the DECOMPILATION lens (the evidence the worker could not see) plus
# the deterministic finding-checker. The oracles are DELIBERATELY excluded — an A/B showed that letting
# the LLM verifier call static_type_oracles/runtime_type_probe cratered version_etc_ar 86.46->70.83
# (the 12B mis-applies the runtime-probe `void *` floor and downgrades specific pointers, even with an
# explicit "never downgrade" instruction). The oracles' *values* are still applied — but SOUNDLY, by
# the deterministic ORACLE-CERTIFIED trailer (`_certified_trailer` / `_collect_oracle_facts`), which is
# monotone and never corrupts a correct answer. The verifier's job is only its independent decomp lens.
VERIFIER_TOOLS = {"decompile", "value_usage"}
# Each oracle is its own tool so the reviewer can pick the one whose EVIDENCE fits the function it is
# looking at; `static_type_oracles` remains as the run-everything call. Exposing them individually is
# only meaningful now that the roster is clean -- while deepagents was injecting seven filesystem tools
# into every subagent, nothing here was selectable in practice.
ORACLE_TOOLS_INDIVIDUAL = {"callee_signature", "decompiler_pointer", "spilled_param",
                           "interprocedural_param_usage", "signedness"}
# The combined `static_type_oracles` is deliberately EXCLUDED. Offered alongside the four, the model
# calls it and stops -- measured across three functions, it consulted an individual oracle only when
# the combined call came back nearly empty, so selection was reacting to a thin result rather than to
# the evidence in the function. Removing it makes the choice real. It remains reachable through
# AGENTIC_VERIFIER_TOOLS when the combined sweep is wanted.
_VERIFIER_TOOLS_ORACLE = (VERIFIER_TOOLS | ORACLE_TOOLS_INDIVIDUAL)


VERIFIER_PROMPT = """You are a type-recovery reviewer with access to the DECOMPILED C code of a \
STRIPPED x86-64 binary (oid `{oid}`, function at virtual address `{vaddr}`). A first-pass worker typed \
the variables from the ASSEMBLY only — WITHOUT the decompilation. Your job is to REFINE its candidate \
types using the higher-level C code it could not see.

1. Call `decompile(oid, addr="{vaddr}")` to read the function's C code — the signature (parameter \
types) and the declared locals.
2. For each candidate `<id>: <C type>`: map the id to the decompiler parameter/local at its storage \
slot, and CORRECT the type when the decompilation shows a more accurate one (pointer levels, a \
specific pointee like `char *`/`FILE *`/`T *`, struct pointers, integer width/signedness). KEEP the \
worker's candidate when the C code agrees with it or is silent — do not change a type without \
evidence.

Report the final adjudicated `<id>: <C type>` line for EVERY variable you were given. Do not re-call a \
tool with identical arguments; finish promptly."""

# Enhanced verifier prompt (opt-in via AGENTIC_VERIFIER_ABI=1). Adds two deterministic rules that
# tracing showed the plain verifier getting wrong on register-heavy functions (do_encode 55.88):
#   (1) an explicit register-slot -> System V AMD64 ABI argument-position map, so a variable located in
#       `register 0x38` is recognised as RDI = the 1st parameter and takes the decompiler's param_1
#       type. The plain verifier had the correct C signature in hand (it decompiled) but still emitted
#       `size_t` for `FILE *`/pointer params because it never aligned the register slot to a param slot.
#   (2) a `void *` guard: never widen a value with no dereference to a pointer — an index/counter used
#       only in arithmetic/comparison is an integer, not `void *`.
VERIFIER_PROMPT_ABI = """You are a type-recovery reviewer with access to the DECOMPILED C code of a \
STRIPPED x86-64 binary (oid `{oid}`, function at virtual address `{vaddr}`). A first-pass worker typed \
the variables from the ASSEMBLY only — WITHOUT the decompilation. Your job is to REFINE its candidate \
types using the higher-level C code it could not see.

1. Call `decompile(oid, addr="{vaddr}")` to read the function's C signature (parameter types) and the \
declared locals. If a variable's role is still unclear, `value_usage(oid, addr="{vaddr}", \
var="param_N"|"local_NN")` reports how it is used (dereferenced at which offsets, indexed, which \
callees receive it).
2. MAP REGISTER PARAMETERS TO ABI POSITIONS. A variable whose location is `register <off>` is an \
incoming argument passed in a System V AMD64 integer register. Translate the register slot to the \
parameter position, then assign it the decompiler's type for THAT parameter:
     register 0x38 = RDI = 1st parameter (param_1)
     register 0x30 = RSI = 2nd parameter (param_2)
     register 0x10 = RDX = 3rd parameter (param_3)
     register 0x8  = RCX = 4th parameter (param_4)
     register 0x80 = R8  = 5th parameter (param_5)
     register 0x88 = R9  = 6th parameter (param_6)
   e.g. if the signature is `f(FILE *param_1, char *param_2, ...)` then the `register 0x38` variable is \
`FILE *` and the `register 0x30` variable is `char *`. A decompiler `undefined8 *`/`void *`/`long *` \
param is still a POINTER — keep it a pointer (prefer the worker's specific pointee if it had one); \
never collapse a pointer parameter to `size_t`/`int`.
3. For every remaining variable (stack locals), map the id to the decompiler local at its slot and \
CORRECT the type when the C code shows a more accurate one (pointer level, specific pointee like \
`char *`/`FILE *`/`T *`, integer width/signedness). KEEP the worker's candidate when the C code agrees \
or is silent.
4. NEVER emit `void *` for a value that is not dereferenced. A variable used only in arithmetic, \
counting, or comparison (an index, length, column, sum) is an INTEGER (`int`/`long`/`size_t`/`idx_t`), \
NOT a pointer — type it as the integer the code shows, never `void *`.

Report the final adjudicated `<id>: <C type>` line for EVERY variable you were given. Do not re-call a \
tool with identical arguments; finish promptly."""









def _force_turns() -> int:
    """Turns for which the reviewer must call SOME tool (0 = off). See `_require_tool_turns`."""
    try:
        return max(0, int(os.environ.get("AGENTIC_VERIFIER_FORCE_TURNS", "0")))
    except ValueError:
        return 0


def _force_oracle() -> bool:
    """Pin the reviewer's first tool call to the oracle (AGENTIC_VERIFIER_FORCE_ORACLE=1)."""
    return str(os.environ.get("AGENTIC_VERIFIER_FORCE_ORACLE", "")).strip().lower() in ("1", "true", "yes")








def _verifier_prompt() -> str:
    """Pick the verifier prompt: the ABI-mapping variant when AGENTIC_VERIFIER_ABI is truthy, else the
    plain reviewer prompt (the validated two-lens baseline)."""
    if str(C.cfg_get("verifier_abi", "")).strip().lower() in ("1", "true", "yes", "on"):
        return VERIFIER_PROMPT_ABI
    return VERIFIER_PROMPT


def _repo_root() -> str:
    """The Oxide repo root that holds mcp_server.py — found by walking up from this file (robust to
    wherever this package lives in the tree)."""
    d = os.path.dirname(os.path.abspath(__file__))
    for _ in range(12):
        if os.path.exists(os.path.join(d, "mcp_server.py")):
            return d
        parent = os.path.dirname(d)
        if parent == d:
            break
        d = parent
    return os.path.dirname(os.path.abspath(__file__))  # fallback (shouldn't hit)


def _mcp_server_path(opts) -> str:
    # the agent's OWN tool server, a sibling of this file — NOT Oxide's default oxide/mcp_server.py
    return opts.get("mcp_server_path") or C.cfg_get("mcp_server_path") \
        or os.path.join(os.path.dirname(os.path.abspath(__file__)), "mcp_agentic.py")


def _oxidepath(opts) -> str:
    return opts.get("oxidepath") or C.cfg_get("oxidepath") or _repo_root()


# ------------------------------------------------------------------------------------------------
#  Tool-call salvage. Under the heavy deepagents context, gemma-4 occasionally emits a tool call as
#  RAW TEXT — e.g. `<|tool_call>call:decompile(oid="..", addr="0x..")<tool_call|>` — instead of a
#  structured tool_call, which langchain/langgraph then treats as a (near-empty) final message. This
#  is the same small-model output fragility the old pipeline salvaged. We wrap ChatOpenAI so that
#  whenever a response has no structured tool_calls but its text contains gemma tool-call syntax, we
#  parse it into proper tool_calls before deepagents sees the message.
# ------------------------------------------------------------------------------------------------
import ast as _ast

_GEMMA_TC_RE = re.compile(
    r"<\|?tool_call\|?>\s*(?:call:)?\s*([A-Za-z_]\w*)\s*\((.*?)\)\s*<\|?/?tool_call\|?>", re.S)


def _parse_call_args(argstr: str) -> dict:
    """Parse `k1="v1", k2=0x10, ...` (Python-call style) into a dict, robustly."""
    try:
        node = _ast.parse(f"_f({argstr})", mode="eval").body
        return {kw.arg: _ast.literal_eval(kw.value) for kw in node.keywords}
    except Exception:  # noqa: BLE001
        args = {}
        for km in re.finditer(r'([A-Za-z_]\w*)\s*=\s*(?:"([^"]*)"|\'([^\']*)\'|([^,)]+))', argstr):
            args[km.group(1)] = (km.group(2) if km.group(2) is not None
                                 else km.group(3) if km.group(3) is not None
                                 else (km.group(4) or "").strip())
        return args


def _strip_channel(text: str) -> str:
    """Remove the model's reasoning-channel markup (`<|channel|>thought<|channel|>…`) that this served
    model wraps around EVERY response — `enable_thinking:False` does NOT suppress it. This MUST run on
    every turn (not just the final answer): if a worker/verifier turn's channel-polluted content stays
    in the ReAct history, the model mimics its own `<|channel|>thought` pattern and never emits a
    terminal answer, looping on tool calls until it exhausts iterations (the observed hang)."""
    if not isinstance(text, str) or not text:
        return text
    t = re.sub(r"<\|?channel\|?>.*?<\|?/?channel\|?>", "", text, flags=re.S)  # paired channel block
    t = re.sub(r"<\|[^>]*>|<[^>]*\|>", "", t)                                 # any residual <|..>/<..|>
    t = re.sub(r"(?im)^\s*thought\s*$", "", t)                                # bare 'thought' label line
    return t.strip()


def _salvage_message(msg):
    """Normalize one model response: (1) strip reasoning-channel markup from its content on EVERY turn
    (see `_strip_channel`) so channel tokens never accumulate in the ReAct history, and (2) if it has
    no structured tool_calls but its text encodes gemma raw-text tool calls, convert those to structured
    tool_calls. Returns a new AIMessage when anything changed, else `msg` unchanged."""
    from langchain_core.messages import AIMessage
    text = msg.content if isinstance(msg.content, str) else ""
    cleaned = _strip_channel(text)

    def _rebuild(content, tool_calls):
        return AIMessage(content=content, tool_calls=tool_calls, id=getattr(msg, "id", None),
                         usage_metadata=getattr(msg, "usage_metadata", None),
                         response_metadata=getattr(msg, "response_metadata", {}) or {})

    # Already has structured tool_calls (vLLM parsed them): keep them, just clean channel residue.
    if getattr(msg, "tool_calls", None):
        return _rebuild(cleaned, msg.tool_calls) if cleaned != text else msg
    # No structured tool_calls: look for gemma raw-text tool calls in the cleaned text.
    matches = list(_GEMMA_TC_RE.finditer(cleaned))
    if not matches:
        return _rebuild(cleaned, []) if cleaned != text else msg
    tcs = [{"name": m.group(1), "args": _parse_call_args(m.group(2)),
            "id": f"salvage_{i}", "type": "tool_call"} for i, m in enumerate(matches)]
    residual = _GEMMA_TC_RE.sub("", cleaned).strip()
    return _rebuild(residual, tcs)


def _salvage_result(result):
    from langchain_core.outputs import ChatGeneration
    for i, gen in enumerate(result.generations):
        new_msg = _salvage_message(gen.message)
        if new_msg is not gen.message:
            result.generations[i] = ChatGeneration(message=new_msg)
    return result


# A tool call the model serialized as PROSE, in the bare brace form: `call:task{description:...}`.
# `_GEMMA_TC_RE` cannot see this -- it requires <tool_call> delimiters AND python parenthesis syntax,
# and `_strip_channel` has already deleted the pipe-wrapped delimiters by the time it runs.
_BARE_TC_RE = re.compile(r"(?:\A|\n)\s*call:\s*([A-Za-z_]\w*)\s*[{(]")


def _text_toolcall_name(msg, offered):
    """The tool this message MEANT to call but emitted as text, or None.

    When it happens langgraph sees a message with no `tool_calls`, treats it as the FINAL ANSWER, and
    the graph ends -- so no subagent runs and no variable is ever typed. Measured over n=100 functions:
    3 functions derailed this way and they held 26% of all variables. Worst case
    `sha384sum/sha512_process_block`, where the coordinator emitted `call:write_todos{...}` as text on
    its FIRST turn: 0 agents ran, 0 of 179 variables answered, 0.0% against TRex's 98.6%.

    Deliberately does NOT try to parse the arguments. They are unquoted pseudo-JSON whose string values
    contain commas and colons (`{description:Recover the precise C types...\\nVariables:\\nV1 ...}`), so
    any splitting heuristic would silently truncate a delegation prompt. The caller instead re-issues
    the request with `tool_choice` naming this tool, which makes the SERVER emit a well-formed call.

    `offered` guards against false positives: only a name the request actually offered is treated as an
    intended call, so prose that happens to contain `call:something{` is left alone."""
    if getattr(msg, "tool_calls", None):
        return None
    text = msg.content if isinstance(msg.content, str) else ""
    if not text:
        return None
    for m in _BARE_TC_RE.finditer(text):
        if m.group(1) in offered:
            return m.group(1)
    return None


def _forced_kwargs(kwargs, name):
    """Same request, but the API must emit a call to exactly `name`."""
    kw = dict(kwargs)
    kw["tool_choice"] = {"type": "function", "function": {"name": name}}
    return kw


_ORACLE_TOOL = "static_type_oracles"


def _tool_names(kwargs) -> set:
    """Names of the tools in an outgoing request, tolerant of both shapes langchain emits."""
    return {n for n in (_name_of(t) for t in (kwargs.get("tools") or [])) if n}


def _restrict_tools(kwargs, allow):
    """Drop every tool the subagent was not designed to have from the OUTGOING request.

    deepagents prepends a fixed middleware stack to every subagent (`TodoListMiddleware`,
    `FilesystemMiddleware`, ...) and there is no spec flag to disable it -- `spec["middleware"]` only
    appends. The result is that a subagent we configured with 3 tools was actually being offered 10:
    `edit_file, glob, grep, ls, read_file, write_file, write_todos` on top of ours. Every
    tool-selection measurement in this project was taken under that confound, including the audit
    that concluded this model "cannot select tools" -- on a 2-tool roster it picks the oracle
    unprompted, with no tool_choice at all.

    Filtering here rather than in middleware keeps it independent of the framework's internals: this
    is the last point before the request leaves for the server."""
    tools = kwargs.get("tools")
    if not tools:
        return kwargs
    keep = [t for t in tools if _name_of(t) in allow]
    if not keep or len(keep) == len(tools):
        return kwargs
    kwargs = dict(kwargs)
    kwargs["tools"] = keep
    return kwargs


def _name_of(t):
    if isinstance(t, dict):
        return ((t.get("function") or {}).get("name")) or t.get("name")
    return getattr(t, "name", None)


def _force_oracle_call(messages, kwargs):
    """Pin the reviewer's tool choice to the oracle until it has actually called it once.

    `tool_choice="required"` was not enough: compelled to act, the model spent both forced turns on
    `decompile` and `value_usage` -- the tools it already favours -- and never reached the oracle
    (6 experiments, same outcome; not a wiring bug, the tool is published, allowlisted and invocable).
    Naming the function in `tool_choice` removes the choice: the API must emit a call to exactly this
    tool. The pin releases as soon as one call has been made, so the rest of the conversation is the
    model's own -- it reads the certified facts, then decompiles and reasons as usual."""
    names = _tool_names(kwargs)
    if _ORACLE_TOOL not in names:
        print(f"[force-oracle] NOT pinning: oracle absent from request tools={sorted(names)}")
        return messages, kwargs
    already = any(
        (tc.get("name") if isinstance(tc, dict) else getattr(tc, "name", None)) == _ORACLE_TOOL
        for m in messages
        for tc in (getattr(m, "tool_calls", None) or []))
    if already:
        return messages, kwargs
    kwargs = dict(kwargs)
    kwargs["tool_choice"] = {"type": "function", "function": {"name": _ORACLE_TOOL}}
    print(f"[force-oracle] pinned -> static_type_oracles; request carries {len(names)} tools: {sorted(names)}")
    return messages, kwargs


def _require_tool_turns(messages, kwargs, n):
    """Require a tool call for a conversation's first `n` turns (`tool_choice="required"`).

    This does NOT choose the tool -- the model still picks from its roster, so what it selects is a
    function of the context it is in. The requirement only removes the option of answering without
    looking, which is the actual observed failure: the reviewer answers after a single `decompile`
    and never reaches for anything else, so a tool it was explicitly instructed to call went unused
    in 5 separate experiments (verified NOT to be a wiring bug -- registry, MCP publication, agent
    allowlist and a live MCP invocation all check out).

    Spanning two turns is deliberate. Turn 1 is habitually `decompile`; forcing only turn 1 would
    change nothing. Turn 2 puts the model in a state where it has already read the C code and must
    still act, which is the point at which consulting the certified oracles is the sensible move."""
    if not kwargs.get("tools") or n <= 0:
        return messages, kwargs
    turns = sum(1 for m in messages
                if getattr(m, "type", None) == "ai" and getattr(m, "tool_calls", None))
    if turns < n:
        kwargs = dict(kwargs)
        kwargs["tool_choice"] = "required"
    return messages, kwargs


def _cap_tool_loop(messages, kwargs):
    """Per-conversation ReAct loop breaker. deepagents runs every subagent with a hardcoded
    recursion_limit of 9_999 (graph.py) — effectively unbounded — and this small model can spin on the
    same tool indefinitely without ever emitting findings (observed: 50+ `disassemble` calls). Once a
    conversation has made >= AGENTIC_MAX_TOOL_TURNS tool-call turns, drop the tools from the request and
    inject a directive so the model MUST return text. Counting is per-conversation (the `messages` of a
    single agent), so the coordinator's delegations and each worker's tool loop are bounded independently."""
    try:
        cap = int(os.environ.get("AGENTIC_MAX_TOOL_TURNS", "10"))
    except (ValueError, TypeError):
        cap = 10
    if not kwargs.get("tools"):
        return messages, kwargs
    # DELEGATIONS ARE NOT LOOPING. `task` is how the coordinator fans work out to subagents, so
    # counting it against this cap ceilings the fan-out at `cap` groups -- and with the prompt's
    # "groups of up to 6" that silently ceilings COVERAGE at ~6*cap variables regardless of how many
    # the function has. Measured on `sha384sum/sha512_process_block` (179 vars): the coordinator issued
    # 10 delegations covering V1-V57, ran out of turns, never reached the verifier, and the remaining
    # 122 entities were default-filled `undefined` -- 25.64% of max. The cap exists to stop a WORKER
    # spinning on one analysis tool (50+ `disassemble` calls observed); that rationale does not apply
    # to handing work to another agent, so `task` turns are excluded from the count.
    def _is_delegation(m):
        tcs = getattr(m, "tool_calls", None) or []
        return bool(tcs) and all((tc.get("name") if isinstance(tc, dict) else
                                  getattr(tc, "name", None)) == "task" for tc in tcs)

    n = sum(1 for m in messages
            if getattr(m, "type", None) == "ai" and getattr(m, "tool_calls", None)
            and not _is_delegation(m))
    if n < cap:
        return messages, kwargs
    from langchain_core.messages import HumanMessage
    kwargs = dict(kwargs)
    kwargs.pop("tools", None)
    kwargs.pop("tool_choice", None)
    directive = HumanMessage(content=(
        f"You have already called tools {n} times — that is enough. Do NOT call any more tools. Using "
        f"the tool results already in this conversation, output ONLY your final answer NOW: one "
        f"`<id>: <C type>` line per assigned variable, then the final JSON object on the last line.\n"
        f"CRITICAL — honor each variable's byte SIZE (given in the task):\n"
        f"  * 8 bytes  -> a POINTER (`T *`, `char *`, `FILE *`, `void *`, a struct pointer) OR a 64-bit "
        f"integer (`long`/`size_t`/`unsigned long`). NEVER `int` — `int` is only 4 bytes.\n"
        f"  * 4 bytes  -> `int` / `unsigned int` (or `float`).\n"
        f"  * 2 bytes  -> `short`;  1 byte -> `char` / `signed char` / `_Bool`.\n"
        f"If an 8-byte value is dereferenced, holds an address, stores a pointer returned by a call, or "
        f"is passed where a struct/FILE/handle/array is expected, it IS a pointer — prefer the pointer "
        f"type over a bare integer when unsure. Do NOT lazily default 8-byte variables to `int`."))
    return list(messages) + [directive], kwargs


def _make_salvaging_class():
    from langchain_openai import ChatOpenAI

    class SalvagingChatOpenAI(ChatOpenAI):
        """ChatOpenAI that (1) bounds each conversation's tool-call loop (see `_cap_tool_loop`),
        (2) converts gemma's raw-text tool calls + strips channel markup (see `_salvage_result`), and
        (3) re-issues a turn whose tool call was emitted as PROSE (see `_text_toolcall_name`), which
        otherwise silently ends the graph with no work done."""

        def _narrated_tool(self, res, kwargs):
            """The tool this turn narrated instead of calling, or None. See `_text_toolcall_name`."""
            offered = _tool_names(kwargs)
            if not offered or kwargs.get("tool_choice"):     # already pinned: nothing to disambiguate
                return None
            gens = getattr(res, "generations", None) or []
            if not gens:
                return None
            name = _text_toolcall_name(gens[0].message, offered)
            if name:
                print(f"[text-toolcall] turn narrated `call:{name}{{...}}` instead of calling it — "
                      f"re-issuing with tool_choice={name}")
            return name

        @staticmethod
        def _keep_better(res, res2):
            """Use the forced retry only if it actually produced a structured call, so this can add
            work but never remove an answer."""
            g2 = getattr(res2, "generations", None) or []
            if g2 and getattr(g2[0].message, "tool_calls", None):
                return res2
            print("[text-toolcall] retry produced no structured call — keeping the original turn")
            return res

        def _shape(self, messages, kwargs):
            """Per-subagent request policy hook. No-op here; subclasses override THIS and nothing
            else, so the salvage/retry pipeline below is written once rather than re-implemented in
            every wrapper (it previously was, in three classes x two entry points)."""
            return messages, kwargs

        def _generate(self, messages, stop=None, run_manager=None, **kwargs):
            messages, kwargs = self._shape(messages, kwargs)
            messages, kwargs = _cap_tool_loop(messages, kwargs)
            res = _salvage_result(super()._generate(messages, stop=stop, run_manager=run_manager,
                                                   **kwargs))
            name = self._narrated_tool(res, kwargs)
            if not name:
                return res
            try:
                res2 = _salvage_result(super()._generate(
                    messages, stop=stop, run_manager=run_manager, **_forced_kwargs(kwargs, name)))
            except Exception as e:  # noqa: BLE001  a failed repair must not fail the turn
                print(f"[text-toolcall] retry failed — {str(e)[:100]}")
                return res
            return self._keep_better(res, res2)

        async def _agenerate(self, messages, stop=None, run_manager=None, **kwargs):
            messages, kwargs = self._shape(messages, kwargs)
            messages, kwargs = _cap_tool_loop(messages, kwargs)
            res = _salvage_result(await super()._agenerate(messages, stop=stop,
                                                          run_manager=run_manager, **kwargs))
            name = self._narrated_tool(res, kwargs)
            if not name:
                return res
            try:
                res2 = _salvage_result(await super()._agenerate(
                    messages, stop=stop, run_manager=run_manager, **_forced_kwargs(kwargs, name)))
            except Exception as e:  # noqa: BLE001
                print(f"[text-toolcall] retry failed — {str(e)[:100]}")
                return res
            return self._keep_better(res, res2)

    return SalvagingChatOpenAI


def _scoped_model(opts, allow, label, pin_oracle=False, n_turns=0):
    """A per-subagent model that enforces `allow` on every outgoing request.

    `SubAgent` accepts a `model`, so each subagent can carry its own roster policy. The COORDINATOR now
    uses this too, with `allow={"task"}`: it needs nothing else, and leaving it on the unrestricted model
    handed it ~21 tools including `write_todos`, the tool it narrated as prose instead of calling."""
    base = _make_salvaging_class()
    reported = {"done": False}

    class _Scoped(base):                                    # noqa: N801
        def _shape(self, messages, kwargs):
            before = _tool_names(kwargs)
            kwargs = _restrict_tools(kwargs, allow)
            after = _tool_names(kwargs)
            if not reported["done"] and before != after:
                print(f"[roster] {label}: dropped {sorted(before - after)} -> offering {sorted(after)}")
                reported["done"] = True
            if pin_oracle:
                messages, kwargs = _force_oracle_call(messages, kwargs)
            elif n_turns:
                messages, kwargs = _require_tool_turns(messages, kwargs, n_turns)
            return messages, kwargs


    return _model(opts, cls=_Scoped)
def _model(opts, cls=None):
    """A salvaging ChatOpenAI bound to the OpenAI-compatible endpoint, greedy + seeded for determinism.
    Passing a pre-initialized model (not an 'openai:' string) keeps us on chat-completions."""
    cfg = C.resolve_config(opts)
    model_id = opts.get("worker_model") or opts.get("model") or cfg["worker_model"]
    return (cls or _make_salvaging_class())(
        model=model_id,
        base_url=cfg["endpoint"],
        api_key=os.environ.get("OPENAI_API_KEY") or "EMPTY",
        temperature=0,
        seed=C._seed(),
        max_tokens=C.max_tokens(),
        timeout=C.req_timeout(),
        streaming=False,                                   # force _agenerate so salvage always runs
        extra_body={"chat_template_kwargs": {"enable_thinking": False}},
    )


def _mcp_env():
    """Extra environment for the MCP server subprocess.

    The MCP stdio client does NOT inherit our environment — it builds a minimal one (HOME/PATH/USER/
    ...), so no `AGENTIC_*` setting reaches the server. Pass through only the server-side knobs we
    explicitly want: `AGENTIC_TOOL_LOG` (tool-call audit log) and `AGENTIC_REPEAT_BREAKER`. Forwarding
    the rest would silently change the server's behaviour: it `setdefault`s `AGENTIC_OUT_CAP=0`
    (uncapped tool output) and trex_env.sh exports 40000, so a blanket pass-through would start
    truncating every tool result. Returns None when none are set, so the client keeps its exact
    default environment."""
    # EVERY knob read inside the MCP server process must be listed here or it is SILENTLY DEAD: the
    # client builds a minimal child environment, so an unlisted flag never arrives, and an A/B that
    # toggles it runs two identical arms. `AGENTIC_DISASM_PAGING_HINT` (read in tools/ghidra.py, which
    # executes in the server) was dead from the day it was added for exactly this reason, and a later
    # experiment burned 20 runs before the byte-identical tool counts gave it away. When adding a flag
    # read anywhere under tools/ or mcp_agentic.py, add it here in the same change.
    #   mcp_agentic.py   : AGENTIC_TOOL_LOG, AGENTIC_REPEAT_BREAKER
    #   tools/ghidra.py  : AGENTIC_DISASM_PAGING_HINT
    passthru = {k: os.environ[k] for k in ("AGENTIC_TOOL_LOG", "AGENTIC_REPEAT_BREAKER",
                                           "AGENTIC_DISASM_PAGING_HINT", "AGENTIC_MASK_IMPORTS")
                if os.environ.get(k)}
    if not passthru:
        return None
    from mcp.client.stdio import get_default_environment
    return {**get_default_environment(), **passthru}


def _DEFAULT_ORACLES():
    """The task module owns the default oracle set; the library must not hardcode task knowledge."""
    from agentic.tasks import type_recovery
    return type_recovery.DEFAULT_ORACLES


def _collect_evidence(oid: str, question: str, opts: dict) -> str:
    """Run the task's deterministic EVIDENCE GATHERERS in-process and return the text to prepend to the
    worker's prompt (empty string when disabled or when nothing is found).

    Unlike `_collect_oracle_facts` (which runs AFTER the agents and OVERRIDES them), this is a genuine
    PRE-pass whose output the worker reads. The two are complementary: an oracle answers a variable
    outright; a gatherer supplies evidence for the ~75% no oracle can certify.

    Opt-in via AGENTIC_EVIDENCE_BUNDLE=1 — it changes what the model sees, and model-facing changes
    have a poor record here, so it ships off until an A/B says otherwise."""
    if os.environ.get("AGENTIC_EVIDENCE_BUNDLE", "") not in ("1", "true", "yes"):
        return ""
    from oxide.core.oxide import api
    from agentic import tools as T, grounding as G
    from agentic.tasks import type_recovery  # noqa: F401 registers the gatherer
    _s, ct = T.build_tools(api, oid, memoize=False)
    out = []
    for name, fn in G.resolve_domain_evidence(opts.get("domain_evidence") or "auto"):
        try:
            txt = fn(ct, question)
        except Exception as e:  # noqa: BLE001  a gatherer must never break the run
            print(f"[evidence] {name} failed: {e}")
            continue
        if txt:
            out.append(txt)
    return "\n\n".join(out)
























@contextlib.contextmanager
def _root_run_span_cm(oid: str, vaddr: str, name: str):
    """One root OpenInference span. Tagging it AGENT + session.id makes Phoenix render a single connected
    tree and group same-function runs under one session, instead of the dozens of orphan traces langgraph
    emits by default. Two roots are used per run: `type_recovery` (the LLM agent graph) and
    `oracle_certification` (the deterministic trailer) — mirroring the two layers of the architecture."""
    try:
        from opentelemetry import trace as _otel
        tracer = _otel.get_tracer("oxide-agentic-deepagents")
    except Exception:  # noqa: BLE001
        yield None
        return
    with tracer.start_as_current_span(f"{name} {vaddr}") as sp:
        try:
            sp.set_attribute("openinference.span.kind", "AGENT")
            sp.set_attribute("session.id", f"{oid[:12]}:{vaddr}")
            sp.set_attribute("input.value", f"{name} for function {vaddr}")
        except Exception:  # noqa: BLE001
            pass
        yield sp


def _root_run_span(enabled: bool, oid: str, vaddr: str, name: str = "type_recovery"):
    """Root-span context manager when tracing is on, else a no-op context."""
    return _root_run_span_cm(oid, vaddr, name) if enabled else contextlib.nullcontext()



def _roster(all_tools, wanted, who):
    """Filter `all_tools` to `wanted`, and report what was actually granted vs asked for.

    An allowlist naming a tool the server never published yields a SILENTLY smaller roster: the agent
    simply never has the capability and its absence looks like the model declining to use it. That
    failure has occurred repeatedly here (tool registry / MCP publication / agent allowlist are three
    separate gates), so the mismatch is printed rather than inferred."""
    got = [t for t in all_tools if getattr(t, "name", "") in wanted]
    missing = sorted(set(wanted) - {getattr(t, "name", "") for t in got})
    if missing:
        print(f"[roster] {who}: NOT PUBLISHED BY THE SERVER -> {missing}")
    print(f"[roster] {who}: {sorted(getattr(t, 'name', '?') for t in got)}")
    return got


def _group_size(question: str) -> int:
    """How many entities the coordinator should put in one delegation.

    A CONSTANT "groups of up to 6" is wrong at both ends. Each group costs one `task` delegation and
    several graph super-steps, so on a large function the fan-out hits a ceiling and the run is
    truncated mid-way: `sha384sum/sha512_process_block` (179 entities) needs ~30 delegations, was cut
    off at 10 by the tool-loop cap, covered only V1-V57 and scored 25.64% of max. The one time it
    scored 96.06% the coordinator had ignored the rule and batched V4-V179 into a SINGLE delegation --
    which is the evidence that a worker handles a large group perfectly well.

    So scale the group with the workload: keep small functions at 6 (where the careful, one-group-at-a-
    time behaviour was tuned) and grow it so a big function still fits in a handful of delegations."""
    n = len(re.findall(r"(?m)^\s*V\d+\s+(?:register|stack)\s", question or ""))
    if n <= 36:
        return 6
    return max(6, -(-n // 6))              # ceil(n/6) groups -> ~6 delegations at any size


def _grouping_rule(question: str) -> str:
    """The grouping sentence for the coordinator prompt.

    Below the threshold this is the ORIGINAL wording, byte for byte: adding fan-out pressure to small
    functions measurably hurt them (stty/printf_fetchargs, 6 entities, 70.59 -> 60.78), because there
    the careful one-group-at-a-time behaviour is what the prompt was tuned for and the extra clause
    just perturbs it. The pressure is added only where the fan-out ceiling is a real risk."""
    n = len(re.findall(r"(?m)^\s*V\d+\s+(?:register|stack)\s", question or ""))
    if n <= 36:
        return "into groups of up to 6."
    # Keep the sentence structurally IDENTICAL to the small-function form and change only the number.
    # A longer variant that added scarcity framing ("every extra group costs a delegation, and your
    # delegations are limited") made the coordinator restructure: instead of delegating every group and
    # then calling the verifier ONCE as step 3 instructs, it interleaved a verifier call after each
    # group. Measured 4/4 on the threshold -- 18 and 13 entities stayed compliant (1 verifier call),
    # 40 and 43 interleaved (3 and 5 calls) -- which doubles the delegations and, worse, means the
    # verifier never sees the full claim list and so cannot catch cross-variable inconsistencies.
    return f"into groups of up to {_group_size(question)}."


async def run_deep_agent(oid: str, question: str, opts: dict) -> str:
    """Build the deepagents multi-agent (coordinator + type_worker + verifier), run it on `question`,
    then append the deterministic ORACLE-CERTIFIED trailer. Returns the final per-variable answer."""
    from deepagents import create_deep_agent

    # Phoenix tracing (opt-in): enable via `phoenix` opt / AGENTIC_PHOENIX=1 / `[agentic]` config.
    # Endpoint via phoenix_endpoint / AGENTIC_PHOENIX_ENDPOINT / config. Must run BEFORE the model and
    # agent graph are built so the LangChain instrumentor patches langgraph's callback manager — that
    # is what makes the coordinator -> worker -> verifier delegation, LLM turns, and tool calls show
    # up as nested spans in the local Phoenix UI (http://localhost:6006).
    _phoenix_on = False
    if str(C._opt(opts, "phoenix") or "").strip().lower() in ("1", "true", "yes", "on"):
        from agentic.extras import trace as _TR
        _ep = C._opt(opts, "phoenix_endpoint") or "http://localhost:6006/v1/traces"
        _phoenix_on = _TR.setup_phoenix(_ep, project_name="oxide-agentic-deepagents")

    # Optional run-flow recorder (AGENTIC_FLOW_DIAGRAM=1): a callback handler that records the actual
    # decompose -> delegate -> tool-calls -> verify -> deterministic-certify flow so it can be drawn as a
    # Mermaid figure for visual inspection. No-op (recorder stays None) unless the flag is set.
    _flow_rec = None
    if str(C._opt(opts, "flow_diagram") or "").strip().lower() in ("1", "true", "yes", "on"):
        try:
            from agentic.extras.flow_recorder import FlowRecorder
            _flow_rec = FlowRecorder()
        except Exception:  # noqa: BLE001
            _flow_rec = None

    # Warm the on-disk analysis cache in THIS process first, so the MCP subprocess (which shares the
    # datastore) reads cached Ghidra results on its first tool call instead of re-running analysis.
    from oxide.core.oxide import api as _api
    for _mod in ("ghidra_disasm", "function_extract"):
        try:
            _api.retrieve(_mod, oid)
        except Exception:  # noqa: BLE001
            pass

    from langchain_mcp_adapters.client import MultiServerMCPClient
    from langchain_mcp_adapters.tools import load_mcp_tools

    # The function's virtual address — the agent references the function by this (stripped: no symbol
    # name). Telling it the vaddr up front is what makes its addr-based tool calls succeed first-try
    # instead of guessing function names and looping.
    _m = re.search(r"(0x[0-9a-fA-F]+)", question)
    vaddr = _m.group(1) if _m else ""

    # The coordinator is offered ONLY `task`. deepagents injects seven framework tools into every
    # agent (`write_todos, edit_file, glob, grep, ls, read_file, write_file`) and `spec["middleware"]`
    # cannot remove them, so the coordinator was being handed ~21 tools for a job that needs exactly
    # one. `write_todos` in particular is pure bookkeeping here AND was the specific tool the model
    # serialized as prose (`call:write_todos{...}`) on its FIRST turn -- which ended the graph before
    # any subagent ran and returned `undefined` for all 179 variables of sha512_process_block. A tool
    # that is not offered cannot be narrated: `_text_toolcall_name` only matches names in the offered
    # set, and the repair-by-retry it triggers proved unreliable (forced `tool_choice` still returned
    # no structured call in 4 of 4 runs). Removing the tool removes the failure mode outright.
    model = _scoped_model(opts, {"task"}, "coordinator")
    client = MultiServerMCPClient({"oxide": {
        "command": sys.executable,
        "args": [_mcp_server_path(opts), f"--oxidepath={_oxidepath(opts)}"],
        "transport": "stdio",
        "env": _mcp_env(),
    }})
    user = f"oid: {oid}   function vaddr: {vaddr}\n\n{question}"
    # langgraph counts SUPER-STEPS (each LLM turn + each tool node), which is unrelated to the old
    # pipeline's per-worker `max_iter`. Use a dedicated knob with a sane default (a sound run is ~6
    # LLM calls ~= 12-14 super-steps; 40 leaves headroom without letting a loop run away).
    recursion_limit = int(opts.get("recursion_limit") or C.cfg_int("recursion_limit", 40))
    # ...but the default cannot be a CONSTANT, because the coordinator's work scales with the number
    # of entities: its prompt says to delegate stack locals in groups of up to 6, so an N-entity
    # function needs ~N/6 delegations, and each costs several super-steps. At 40 the graph dies on any
    # large function. Measured on `sha384sum/sha512_process_block` (179 entities): the coordinator
    # needs ~30 delegations and raised `GraphRecursionError: Recursion limit of 40 reached`, after the
    # tool-loop cap stopped truncating it at 10. Scale the floor with the entity count and keep the
    # configured value as a lower bound, so small functions are unaffected.
    _n_vars = len(re.findall(r"(?m)^\s*V\d+\s+(?:register|stack)\s", question or ""))
    if _n_vars > 36:                       # ~6 groups; below this the constant default is ample
        _needed = 3 * ((_n_vars + 5) // 6) + 20
        if _needed > recursion_limit:
            print(f"[recursion] {_n_vars} entities -> raising graph limit "
                  f"{recursion_limit} -> {_needed}")
            recursion_limit = _needed

    # ONE persistent MCP session (subprocess) for the whole run — otherwise every tool call respawns
    # mcp_server.py (~3.6s oxide init each) and defeats the server-side caches (the original hang).
    async with client.session("oxide") as session:
        all_tools = await load_mcp_tools(session)
        # The agent GENUINELY investigates via the Oxide/Ghidra MCP tools (decompile, disassemble,
        # stack_var, xrefs, ...) plus the oracle tools. All are addr-based so they work on the stripped
        # function. The deterministic trailer still pins the certified facts as a final guarantee.
        tools = [t for t in all_tools if getattr(t, "name", "") in WORKER_TOOLS]
        # Deterministic pre-gathered evidence (opt-in). Appended to the worker's system prompt so the
        # facts are present WITHOUT the worker having to decide to go and get them — it never does.
        _evidence = _collect_evidence(oid, question, opts)
        _worker_sys = _with_topk(TYPE_WORKER_PROMPT.format(oid=oid, vaddr=vaddr))
        if _evidence:
            _worker_sys = f"{_worker_sys}\n\n{_evidence}"
            print(f"[evidence] injected {len(_evidence)} chars into the type_worker prompt")
        _worker_model = _scoped_model(opts, WORKER_TOOLS, "type_worker")
        type_worker = {
            "name": "type_worker",
            "description": "Recovers the precise C type of a group of variables by decompiling and "
                           "analysing the function at the given vaddr, and consulting the oracle tools.",
            "system_prompt": _worker_sys,
            "tools": tools,
            "model": _worker_model,
        }
        # A genuine verifier AGENT: re-types the workers' candidate claims against the DECOMPILATION —
        # the evidence the assembly-only worker never saw. The ORACLE-CERTIFIED trailer still runs
        # afterward as the final deterministic guarantee.
        # NOTE: the `description` below still says "verify_finding" (a tool deleted in the Phase-2
        # simplification). It is left as-is ON PURPOSE: `description` is passed into the `task` tool
        # schema the COORDINATOR model reads, so editing it perturbs a prompt on a model measured to be
        # prompt-fragile (see the reverted subagent-tool-stripping A/B: -21.8 on hash_do_for_each).
        # Fix it only together with an A/B.
        # Resolve the roster FIRST: it decides both what is advertised and what the prompt describes.
        _vtools = _VERIFIER_TOOLS_ORACLE if _verifier_oracles() else VERIFIER_TOOLS
        _ov = os.environ.get("AGENTIC_VERIFIER_TOOLS", "").strip()
        if _ov:                                            # explicit roster, for roster-size A/Bs
            _vtools = {t.strip() for t in _ov.split(",") if t.strip()}
        verifier = {
            "name": "verifier",
            "description": "Adjudicates candidate variable-type claims against the deterministic "
                           "oracles and verify_finding; corrects claims that conflict with certified types.",
            "system_prompt": _with_topk(_verifier_prompt().format(oid=oid, vaddr=vaddr)
                                       + (_oracle_tool_hint(oid, vaddr, _vtools)
                                          if _verifier_oracles() else "")),
            "tools": _roster(all_tools, _vtools, "verifier"),
        }
        verifier["model"] = _scoped_model(opts, _vtools, "verifier",
                                          pin_oracle=_force_oracle(), n_turns=_force_turns())
        # Neuter the auto-added general-purpose subagent. deepagents injects a `general-purpose`
        # subagent that has ALL of the main agent's tools (every MCP analysis tool + the built-in
        # filesystem tools ls/read_file/write_file/glob/grep/execute). Tracing showed the coordinator
        # occasionally delegates a vague "map the variables" task to it, and it then thrashes —
        # re-running decompile/stack_var and calling `ls /` — because it is the ONLY agent holding all
        # of those tools at once. Providing our own subagent NAMED `general-purpose` overrides the
        # default (deepagents only auto-adds one when none is supplied); ours has NO tools, so the
        # coordinator is forced down the intended type_worker -> verifier path instead of a
        # do-everything escape hatch. The two-lens split (worker=assembly, verifier=decompilation) and
        # the deterministic trailer are unaffected.
        general_purpose = {
            "name": "general-purpose",
            "description": "Disabled. Do NOT delegate to this agent — use type_worker and verifier.",
            "system_prompt": "You have no tools and no role in this pipeline. Immediately reply "
                             "'delegate to type_worker or verifier instead' and return control.",
            "tools": [],
        }
        # Coordinator gets NO analysis tools — only the built-in write_todos (plan) and task
        # (delegate). This forces genuine plan-then-delegate multi-agent behaviour; the worker holds
        # the analysis + oracle tools, and the verifier adjudicates the results.
        # AGENTIC_NEUTER_GP=1 overrides deepagents' default all-tools general-purpose subagent with a
        # no-tool stub. DEFAULT OFF: an A/B showed the stub HELPS some functions (do_decode +3.17) but
        # HANGS others (version_etc_ar spun 18+ min) — the coordinator re-delegates in a loop when the
        # stub replies "delegate elsewhere". Off by default is the safe behaviour (all functions
        # converge); leave it as an opt-in experiment until the re-delegation loop is guarded.
        _subagents = [type_worker, verifier]
        if str(C._opt(opts, "neuter_gp") or "0").strip().lower() in ("1", "true", "yes", "on"):
            _subagents.append(general_purpose)
        agent = create_deep_agent(
            model=model,
            tools=[],
            system_prompt=COORDINATOR_PROMPT.format(oid=oid, vaddr=vaddr,
                                                    grouping_rule=_grouping_rule(question)),
            subagents=_subagents,
        )
        # Wrap the whole run in ONE root span (+ a session id) so Phoenix shows a single connected tree
        # grouped coordinator -> task -> worker/verifier, instead of the dozens of orphan traces langgraph
        # otherwise emits (its async subagent/tool nodes each start a fresh OTel root, fragmenting the
        # trace). asyncio tasks copy the current context at creation, so with this span current when
        # ainvoke runs, the langgraph model/tool/subagent spans nest under it.
        _cfg = {"recursion_limit": recursion_limit}
        if _flow_rec is not None:
            _cfg["callbacks"] = [_flow_rec]
        with _root_run_span(_phoenix_on, oid, vaddr):
            result = await agent.ainvoke(
                {"messages": [{"role": "user", "content": user}]},
                _cfg,
            )
        answer = result["messages"][-1].content

    # clean gemma special tokens (thinking/channel markup) so only the answer text (+ its final JSON
    # line) remains. Same helper the per-turn salvage uses, applied once more to the final answer.
    answer = _strip_channel(answer)
    # Undo verifier degeneration (specific type -> `undefinedN`) BEFORE the oracle trailer, so the
    # oracles adjudicate against a concrete answer rather than a contentless one.
    _msgs = result.get("messages") if isinstance(result, dict) else None
    _dump_tool_calls(_msgs)
    _log_claims(_msgs)                                       # per-stage record, before any revision
    try:
        answer = _rescue_undefined(_msgs, answer)
    except Exception as e:  # noqa: BLE001  never let a post-pass break the run
        print(f"[undef-rescue] skipped — {str(e)[:120]}")
    # The deterministic oracle trailer gets its OWN root span so its (main-process) decompile/stack_var
    # oracle calls collapse into one `oracle_certification` tree instead of ~60 orphan traces.
    with _root_run_span(_phoenix_on, oid, vaddr, name="oracle_certification"):
        final = answer if _no_certify() else _certified_trailer(oid, question, answer, opts)
    # Last: enforce the one constraint the question states outright. Runs AFTER certification so an
    # oracle fact is coerced too if it somehow contradicts the declared size.
    final = _coerce_sizes(question, final)

    if _flow_rec is not None:
        _emit_flow_diagram(_flow_rec, oid, vaddr, question, final, opts)
    return final


# Stash of the last run's flow data so the harness can RE-render the diagrams after it has scored the
# prediction (adding ground-truth match + mean score to the Output node). Keeps the library generic —
# it only DISPLAYS a scoring dict the harness computes; it never knows about TREX ground truth itself.
_LAST_FLOW: dict = {}


def _emit_flow_diagram(recorder, oid: str, vaddr: str, question: str, answer: str, opts: dict) -> None:
    """Build the Mermaid run-flow figures from the recorded events + deterministic oracle facts, and write
    them next to the run outputs. Best-effort: a failure here never affects the returned answer."""
    try:
        from agentic.extras import flow_recorder as _FR
        oracle_facts = _collect_oracle_facts(oid, question, opts)
        # the FULL list of deterministic oracles that were CONSULTED (mirrors _collect_oracle_facts'
        # resolution) so the diagram can show which ran-and-abstained (e.g. runtime_type_probe) vs which
        # certified — an oracle producing no fact must not look like it was skipped.
        _which = (opts.get("domain_oracles")
                   or os.environ.get("AGENTIC_DOMAIN_ORACLES")
                   or _DEFAULT_ORACLES())
        consulted = [x.strip() for x in str(_which).split(",") if x.strip()]
        variables = _FR.input_vars_from_question(question)
        meta = {"vaddr": vaddr, "nvars": len(variables) or len(set(re.findall(r"\bV\d+\b", question))),
                "oracles_consulted": consulted, "variables": variables,
                # Whether the deterministic trailer actually APPLIED these facts. The recorder
                # recomputes them purely to display, so without this the diagram drew a
                # "certification" stage on runs where certification was switched off and the reviewer
                # consulted the oracles itself -- showing two appliers where there was one.
                "certified_by_code": not _no_certify()}
        out_dir = C.cfg_get("flow_dir") or opts.get("flow_dir") or os.getcwd()
        base = os.path.join(out_dir, f"agentic_flow_{vaddr.replace('0x', '')}")
        _LAST_FLOW.clear()
        _LAST_FLOW.update({"recorder": recorder, "meta": meta, "oracle_facts": oracle_facts,
                           "answer": answer, "base": base})
        _render_flow(scoring=opts.get("flow_scoring"))
    except Exception as e:  # noqa: BLE001
        print(f"[flow] diagram skipped — {str(e)[:120]}")


def _render_flow(scoring=None) -> None:
    """Render the 3 views (flowchart, turn sequence, markdown) from _LAST_FLOW, optionally with a scoring
    dict {ground_truth:{vid:type}, score:float} that adds the ground-truth match + mean score to Output."""
    from agentic.extras import flow_recorder as _FR
    F = _LAST_FLOW
    if not F:
        return
    rec, meta, facts, answer, base = F["recorder"], F["meta"], F["oracle_facts"], F["answer"], F["base"]
    # (1) overview flowchart. (2) sequence diagram, then compose ONE figure = input panel + the sequence
    # image + output panel (final answer + score). (3) markdown log.
    _, png_path = _FR.render(_FR.to_mermaid(rec, meta, facts, answer, scoring), base)
    _, seq_png = _FR.render(_FR.to_sequence(rec, meta, facts, answer, scoring), base + "_turns")
    if seq_png:
        _FR.compose_sequence_figure(seq_png, meta, answer, scoring, base + "_turns.png")
    with open(base + ".md", "w") as fh:
        fh.write(_FR.to_markdown(rec, meta, facts, answer, scoring))
    tag = "  (+ ground-truth & score)" if scoring else ""
    print(f"[flow] run-flow diagrams -> {base}.{{mmd,svg,png}} (flowchart) + {base}_turns.png "
          f"(input + sequence + output) + {base}.md{tag}"
          + ("" if png_path else "  (npx @mermaid-js/mermaid-cli for PNGs)"))


def write_flow_scoring(ground_truth: dict, score: float, per_var: dict = None) -> None:
    """Public hook the HARNESS calls AFTER scoring: re-renders the last run's diagrams with the Output node
    showing predicted-vs-ground-truth and the mean score. No-op if no flow run was recorded."""
    if _LAST_FLOW:
        try:
            _render_flow(scoring={"ground_truth": ground_truth or {}, "score": score,
                                  "per_var": per_var or {}})
        except Exception as e:  # noqa: BLE001
            print(f"[flow] scoring overlay skipped — {str(e)[:120]}")


def run_sync(oid: str, question: str, opts: dict) -> str:
    """Sync entry (for the analyzer module's results()). Runs the async agent on a fresh event loop;
    if called from within a running loop, offloads to a worker thread (asyncio.run cannot nest)."""
    try:
        asyncio.get_running_loop()
    except RuntimeError:
        return asyncio.run(run_deep_agent(oid, question, opts))
    import concurrent.futures
    with concurrent.futures.ThreadPoolExecutor(1) as ex:
        return ex.submit(lambda: asyncio.run(run_deep_agent(oid, question, opts))).result()
