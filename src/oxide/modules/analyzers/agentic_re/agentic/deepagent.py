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
locals into groups of up to 6. Keep this plan in mind; do NOT write it down anywhere.
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


# --- ORACLES-IN-THE-LOOP experiment (opt-in, AGENTIC_VERIFIER_ORACLES=1) --------------------------
# The architecture's central claim is that certification must be applied BY CODE, after the agents,
# and never shown to them -- because a fact a model has seen becomes indistinguishable from a fact the
# model produced. This flag tests that claim head-on by inverting it: the reviewer is given the oracle
# tool and asked to apply the certified facts ITSELF, and the deterministic trailer is switched off so
# the oracles fire exactly once. The comparison is therefore "same facts, applied by a 12B model" vs
# "same facts, applied by code".
#
# NOT the same as the earlier A/B recorded above: that one left the trailer ON, so the oracles were
# applied twice and the model could only corrupt what code then re-fixed (version_etc_ar 86.46->70.83).
# Here the model is the only consumer, which is the configuration the design argument is about.
# The facts are INJECTED, not fetched. Offering the oracle as a TOOL was tried first and the reviewer
# never called it -- verified not to be a wiring bug (registry, MCP publication, allowlist and a live
# MCP invocation all check out; the roster printed the tool and a direct call returned certifications).
# It is the fifth instance of this model declining a tool it was explicitly instructed to use, matching
# the tool-selection audit's finding that `xrefs_to`/`read_values`/`compute` were chosen 0 times in
# 1049 calls. Appending the tool instructions also REDUCED its tool use (decompile x1 + value_usage x3
# -> decompile x1 only). Injection removes tool selection from the experiment so that the only variable
# left is the one under test: can the model APPLY certified facts as well as code applies them?
_ORACLE_SUFFIX = """

CERTIFIED FACTS for this function — deterministic, re-derived from the binary and public ABI \
knowledge. These are NOT guesses and they outrank your own reading of the decompilation:
{facts}

How to apply each kind:
  - EXACT — replace your type for that id, unconditionally.
  - FLOOR — asserts only "this id holds a pointer", pointee unknown. Use it when your type is NOT a \
pointer; KEEP your own more specific pointer when it already is one (never overwrite `char *` with \
`void *`).
  - SHAPE — a field layout with no source-level name. Use it unless you already have a NAMED pointee.
Ignore any fact whose type is wider than that id's declared byte size. For every id not listed above, \
use your own decompilation-based judgement."""


# Tool-mode hint (used with AGENTIC_VERIFIER_FORCE_TURNS): the reviewer picks the tool itself.
_ORACLE_TOOL_BLURB = {
    # Peer descriptions: each names the EVIDENCE it reads, none claims to subsume the others.
    # The combined oracle previously advertised itself as "runs all of the above at once", which made
    # the other four unselectable in practice -- the model called it and stopped every time.
    "callee_signature": "a parameter handed to a libc function whose ABI fixes that argument's type "
                        "— use when the function calls libc",
    "decompiler_pointer": "the decompiler's own recovered pointer declarations — use when you suspect "
                          "a pointer but the assembly does not settle it",
    "spilled_param": "the prologue store that copies an argument register into a stack slot — use when "
                     "stack locals mirror the parameters",
    "interprocedural_param_usage": "a parameter forwarded into another local function until it reaches "
                                   "a fixed-type library position — use when a parameter is passed on",
    "static_type_oracles": "all four at once — use when several kinds of evidence are present, or you "
                           "have no specific hypothesis about where a type would come from",
}


def _oracle_tool_hint(oid: str, vaddr: str, roster) -> str:
    """Describe ONLY the oracle tools this reviewer actually has.

    Built from the roster rather than hard-coded because naming a tool in the prompt is itself a way
    of calling it: the model will copy a call out of the instructions even when that tool was filtered
    out of the request, and langgraph's executor runs it anyway. A hard-coded list therefore silently
    defeats any roster-level experiment -- what looked like the reviewer SELECTING the combined oracle
    was it reciting the one example the prompt spelled out."""
    have = [t for t in ("callee_signature", "decompiler_pointer", "spilled_param",
                        "interprocedural_param_usage", "static_type_oracles") if t in roster]
    if not have:
        return ""
    lines = "\n".join(f"  {i}. `{t}(oid=\"{oid}\", addr=\"{vaddr}\", variables=...)` — "
                      f"{_ORACLE_TOOL_BLURB[t]}." for i, t in enumerate(have, 1))
    return f"""

You also have DETERMINISTIC ORACLES. They read the binary directly and return CERTIFIED facts — \
derived, not guessed — as [{{{{vid, ctype, floor, oracle}}}}]. Each takes \
`(oid="{oid}", addr="{vaddr}", variables=<the variable list you were given, verbatim>)`:
{lines}
Consult the ones whose EVIDENCE matches what you can see in this function — several may apply, and \
each certifies entities the others miss, so calling more than one is normal. They are deterministic \
and cheap; the only cost of consulting one that does not apply is that it abstains.

Apply what they return as authoritative: a fact with `floor: false` replaces your type for that id; a \
fact with `floor: true` asserts only "this is a pointer", so use it when your type is NOT a pointer \
but keep your own more specific pointer when it already is one; ignore any fact wider than the id's \
declared byte size."""



def _force_turns() -> int:
    """Turns for which the reviewer must call SOME tool (0 = off). See `_require_tool_turns`."""
    try:
        return max(0, int(os.environ.get("AGENTIC_VERIFIER_FORCE_TURNS", "0")))
    except ValueError:
        return 0


def _force_oracle() -> bool:
    """Pin the reviewer's first tool call to the oracle (AGENTIC_VERIFIER_FORCE_ORACLE=1)."""
    return str(os.environ.get("AGENTIC_VERIFIER_FORCE_ORACLE", "")).strip().lower() in ("1", "true", "yes")


def _oracle_brief(oid: str, question: str, opts: dict) -> str:
    """The certified facts, rendered for injection into the reviewer's prompt."""
    try:
        facts = _collect_oracle_facts(oid, question, opts)
    except Exception as e:  # noqa: BLE001
        print(f"[verifier-oracles] skipped — {str(e)[:120]}")
        return ""
    if not facts:
        return ""
    kind = {"exact": "EXACT", "floor": "FLOOR", "shape": "SHAPE"}
    lines = [f"  {vid}: {ctype}   [{kind.get(mode, mode)} — {oracle}]"
             for vid, (ctype, oracle, mode) in sorted(facts.items(), key=lambda kv: kv[0])]
    print(f"[verifier-oracles] injected {len(lines)} certified facts into the reviewer prompt")
    return _ORACLE_SUFFIX.format(facts="\n".join(lines))


def _verifier_oracles() -> bool:
    """Is the reviewer given the oracles as TOOLS? Default ON -- this is the shipped architecture.

    The reviewer selects the oracle whose evidence fits the function it is looking at, reads the facts,
    and adjudicates them against the decompilation itself. Set AGENTIC_VERIFIER_ORACLES=0 to withhold
    them, which is the ablation that isolates what the oracles contribute."""
    return str(os.environ.get("AGENTIC_VERIFIER_ORACLES", "1")).strip().lower() \
        not in ("0", "false", "no", "off")


def _no_certify() -> bool:
    """Is the code-applied certification trailer suppressed? Default ON (i.e. no trailer).

    In the shipped architecture the oracles are applied by the REVIEWER, which reads their claims as
    tool results and decides. `_certified_trailer` -- with its first-claim-wins precedence and the five
    claim modes -- is therefore not on the default path; it is retained, and reachable with
    AGENTIC_NO_CERTIFY=0, as the alternative-architecture ablation. Note what still runs
    unconditionally either way: `_rescue_undefined` and `_coerce_sizes`, plus each oracle's own
    physical-realizability guard, so the deterministic layer is reduced but not removed."""
    return str(os.environ.get("AGENTIC_NO_CERTIFY", "1")).strip().lower() \
        not in ("0", "false", "no", "off")


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
    n = sum(1 for m in messages
            if getattr(m, "type", None) == "ai" and getattr(m, "tool_calls", None))
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

        def _generate(self, messages, stop=None, run_manager=None, **kwargs):
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

        def _generate(self, messages, stop=None, run_manager=None, **kwargs):
            messages, kwargs = self._shape(messages, kwargs)
            return super()._generate(messages, stop=stop, run_manager=run_manager, **kwargs)

        async def _agenerate(self, messages, stop=None, run_manager=None, **kwargs):
            messages, kwargs = self._shape(messages, kwargs)
            return await super()._agenerate(messages, stop=stop, run_manager=run_manager, **kwargs)

    return _model(opts, cls=_Scoped)


def _forcing_model(opts, n_turns: int):
    """A model for ONE subagent that must call a tool on its first `n_turns` turns.

    `SubAgent` accepts a per-subagent `model`, so this applies to the reviewer alone and leaves the
    coordinator and workers on the shared model -- otherwise forcing the coordinator to call a tool
    would break its delegate-then-synthesize flow."""
    base = _make_salvaging_class()

    pin = _force_oracle()

    class _Forcing(base):                                   # noqa: N801
        def _shape(self, messages, kwargs):
            if pin:                                         # name the tool -- no choice left
                return _force_oracle_call(messages, kwargs)
            return _require_tool_turns(messages, kwargs, n_turns)

        def _generate(self, messages, stop=None, run_manager=None, **kwargs):
            messages, kwargs = self._shape(messages, kwargs)
            return super()._generate(messages, stop=stop, run_manager=run_manager, **kwargs)

        async def _agenerate(self, messages, stop=None, run_manager=None, **kwargs):
            messages, kwargs = self._shape(messages, kwargs)
            return await super()._agenerate(messages, stop=stop, run_manager=run_manager, **kwargs)

    return _model(opts, cls=_Forcing)


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


def _collect_oracle_facts(oid: str, question: str, opts: dict) -> dict:
    """Run the static type oracles IN-PROCESS and return {vid: (ctype, oracle, floor)} (first oracle
    wins per vid). Reliable because it uses the full question (with the vaddr) — unlike an LLM tool
    call, which was observed to drop the vaddr and get empty results.

    WHEN THIS RUNS: only AFTER the agents finish, from `_certified_trailer` (plus `_emit_flow_diagram`
    for rendering). The oracles are NOT a pre-pass and their facts are NOT injected into any prompt —
    the coordinator/worker/verifier never see them, they only get OVERRIDDEN by them. So the verifier
    re-derives types the oracles already knew. Feeding these facts FORWARD into a prompt is an untested
    lever, not current behaviour (`_collect_evidence` is the opt-in pre-pass that does something like
    it)."""
    from oxide.core.oxide import api
    from agentic import tools as T, grounding as G
    from agentic.tasks import type_recovery  # noqa: F401 registers the 4 static oracles (the default)
    # env is consulted too: the harness/CLI has no opts dict, so without this AGENTIC_DOMAIN_ORACLES
    # was silently inert — which also made the registered `runtime_type_probe` oracle unreachable
    # from run_trex_one.py (it is imported, registered, and then never named).
    which = (opts.get("domain_oracles")
             or os.environ.get("AGENTIC_DOMAIN_ORACLES")
             or type_recovery.DEFAULT_ORACLES)
    # runtime_type_probe is OPT-IN and lives in extras/ (the expensive, ~5%-coverage dynamic angr probe);
    # import it only when named, so the minimal pipeline never pulls angr.
    if "runtime_type_probe" in str(which):
        try:
            from agentic.extras import runtime_probe  # noqa: F401 registers the runtime oracle
        except Exception:  # noqa: BLE001
            pass
    _s, ct = T.build_tools(api, oid, memoize=False)
    # Declared byte size per variable, straight from the question (ground-truth input, not inference).
    sizes = {m.group(1): int(m.group(2))
             for m in re.finditer(r"(?m)^\s*(V\d+)\s+(?:register|stack)\s+\S+\s+(\d+)\s*$", question or "")}
    facts: dict = {}                                         # vid -> (ctype, oname, floor); first wins
    for name, fn in G.resolve_domain_oracles(which, question):
        try:
            for f in fn(ct, question):
                if f["vid"] in facts:
                    continue
                # SOUNDNESS GUARD: never certify a pointer for a slot too small to hold one. The
                # oracles are the AUTHORITATIVE layer (the trailer applies them over the LLM), so an
                # impossible certification is strictly worse than abstaining. Measured on
                # chroot/mgetgroups: callee_signature certified V2 (4B) and spilled_param certified
                # V13 (4B) as `void *` — physically impossible — overriding a verifier that had both
                # correct as `int`. The size is GIVEN ground truth, so this check is exact, not
                # heuristic. Disable with AGENTIC_NO_SIZE_GUARD=1.
                sz = sizes.get(f["vid"])
                if (sz and sz < 8 and "*" in str(f.get("ctype", ""))
                        and os.environ.get("AGENTIC_NO_SIZE_GUARD", "") not in ("1", "true", "yes")):
                    print(f"[size-guard] dropped unsound {name} certification "
                          f"{f['vid']}={f['ctype']!r} on a {sz}-byte slot")
                    continue
                # THREE certification modes (see `_certified_trailer`): `exact` overrides
                # unconditionally, `floor` is a lower bound that defers to any pointer, and `shape`
                # sits between them -- it carries layout but no source-level name.
                mode = f.get("mode") or ("floor" if f.get("floor") else "exact")
                facts[f["vid"]] = (f["ctype"], name, mode)
        except Exception:  # noqa: BLE001
            continue
    return facts


_UNDEF_RE = re.compile(r"^\s*undefined\d*\s*\**\s*$", re.I)


def _claims_from_messages(messages) -> list:
    """Every `V<n>: <type>` claim any subagent returned, in delegation order. Subagent answers come
    back as the CONTENT of the `task` tool results, so this recovers the worker/verifier findings the
    coordinator saw."""
    out = []
    for m in messages or []:
        if getattr(m, "type", None) != "tool":
            continue
        txt = m.content if isinstance(m.content, str) else ""
        d = {}
        for mm in re.finditer(r"(?mi)^\s*-?\s*(V\d+)\s*[:=]\s*(.+?)\s*$", txt):
            t = mm.group(2).strip().strip("`").split("(")[0].split(",")[0].strip()
            if t and len(t) < 40:
                d[mm.group(1)] = t
        for jm in re.finditer(r"\{[^{}]*\}", txt):
            try:
                o = json.loads(jm.group(0))
            except Exception:  # noqa: BLE001
                continue
            if isinstance(o, dict):
                for k, v in o.items():
                    if re.fullmatch(r"V\d+", str(k)) and isinstance(v, str):
                        d[str(k)] = v.strip()
        if d:
            out.append(d)
    return out


def _claims_by_agent(messages) -> list:
    """`[{"agent": "type_worker", "claims": {"V1": "char *", ...}}, ...]` in delegation order.

    Same extraction as `_claims_from_messages`, but each subagent's findings are ATTRIBUTED to the
    subagent that produced them, by matching the `task` tool call that spawned it to the tool result
    it returned. Attribution is what makes a per-stage ablation possible: with it, the assembly
    worker's answer and the decompilation reviewer's revision of that answer can be scored
    separately, from a stored run and with no model re-run -- so a two-lens ablation becomes exact
    rather than noise-limited (§ the certification ablation has this property already; the agent
    stages did not, purely because the intermediate answers were computed and then discarded)."""
    spawned, briefs = {}, {}                                 # tool_call_id -> subagent type / brief
    for m in messages or []:
        for tc in (getattr(m, "tool_calls", None) or []):
            if (tc.get("name") if isinstance(tc, dict) else None) == "task":
                args = tc.get("args") or {}
                spawned[tc.get("id")] = str(args.get("subagent_type") or "?")
                # The DELEGATION BRIEF the coordinator actually wrote. Recorded because what a
                # subagent receives is decided by the coordinator at run time, not by the static
                # prompt: the coordinator is *instructed* to forward the workers' candidate claims to
                # the reviewer, and whether it does is an empirical question about one LLM following
                # another LLM's spec. Without this the two-lens ablation cannot say whether the
                # reviewer was revising candidates or typing the function from scratch.
                briefs[tc.get("id")] = str(args.get("description") or "")[:4000]
    out = []
    for m in messages or []:
        if getattr(m, "type", None) != "tool":
            continue
        txt = m.content if isinstance(m.content, str) else ""
        d = {}
        for mm in re.finditer(r"(?mi)^\s*-?\s*(V\d+)\s*[:=]\s*(.+?)\s*$", txt):
            t = mm.group(2).strip().strip("`").split("(")[0].split(",")[0].strip()
            if t and len(t) < 60:
                d[mm.group(1)] = t
        for jm in re.finditer(r"\{[^{}]*\}", txt):
            try:
                o = json.loads(jm.group(0))
            except Exception:  # noqa: BLE001
                continue
            if isinstance(o, dict):
                for k, v in o.items():
                    if re.fullmatch(r"V\d+", str(k)) and isinstance(v, str):
                        d[str(k)] = v.strip()
        alts = {}                                            # `ALTS V1: void * | long` (AGENTIC_TOPK)
        for am in re.finditer(r"(?mi)^\s*ALTS?\s+(V\d+)\s*[:=]\s*(.+?)\s*$", txt):
            cand = [c.strip().strip("`") for c in am.group(2).split("|")]
            cand = [c for c in cand if c and len(c) < 60]
            if cand:
                alts.setdefault(am.group(1), []).extend(cand)
        if d or alts:
            _tid = getattr(m, "tool_call_id", None)
            out.append({"agent": spawned.get(_tid, "?"), "brief": briefs.get(_tid, ""),
                        "claims": d, "alts": alts})
    return out


def _dump_tool_calls(messages) -> None:
    """Every tool call the models EMITTED, whether or not it reached the server.

    The MCP-side log only records calls that arrived. A call the model emitted with bad arguments is
    rejected before that and looks identical to a call never attempted, which is the difference
    between "the model won't select this tool" and "the model selects it and we drop it"."""
    if not os.environ.get("AGENTIC_DUMP_TOOLCALLS"):
        return
    seen = []
    for m in messages or []:
        for tc in (getattr(m, "tool_calls", None) or []):
            nm = tc.get("name") if isinstance(tc, dict) else getattr(tc, "name", None)
            seen.append(nm)
        inv = getattr(m, "invalid_tool_calls", None) or []
        for tc in inv:
            nm = (tc.get("name") if isinstance(tc, dict) else None) or "?"
            err = (tc.get("error") if isinstance(tc, dict) else "") or ""
            print(f"[toolcalls] INVALID {nm}: {str(err)[:160]}")
    from collections import Counter
    print(f"[toolcalls] emitted: {dict(Counter(seen))}")


def _log_claims(messages) -> None:
    """Persist per-subagent claims to AGENTIC_CLAIM_LOG (opt-in). Cheap, and it is the only record
    of what each stage believed BEFORE the next stage revised it."""
    path = os.environ.get("AGENTIC_CLAIM_LOG", "").strip()
    if not path:
        return
    try:
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        with open(path, "w") as fh:
            json.dump(_claims_by_agent(messages), fh, indent=1)
    except Exception as e:  # noqa: BLE001  never let logging break a run
        print(f"[claim-log] skipped — {str(e)[:120]}")


def _rescue_undefined(messages, answer: str) -> str:
    """Never let a SPECIFIC type be replaced by an `undefinedN` one.

    The verifier always wins arbitration, but its decompilation lens is not strictly superior: when
    Ghidra emits `undefined8` for a slot the assembly worker had already typed concretely, the
    verifier overwrites a CORRECT answer with a contentless one (measured on do_encode V2:
    worker `char *` -> verifier `undefined8 *`, and the same failure is on record for get_8). This
    restores the earlier specific claim whenever the final answer degenerated to `undefined*`.
    Monotone and information-preserving — it can only replace a non-answer with an answer, never
    change one concrete type into a different concrete type. Deterministic (no LLM).
    Disable with AGENTIC_NO_UNDEF_RESCUE=1."""
    if str(os.environ.get("AGENTIC_NO_UNDEF_RESCUE", "")).strip().lower() in ("1", "true", "yes", "on"):
        return answer
    claims = _claims_from_messages(messages)
    if not claims:
        return answer
    rescued = {}
    for vid in {v for d in claims for v in d}:
        cur = None
        m = re.search(rf"(?mi)^\s*-?\s*{re.escape(vid)}\s*[:=]\s*(.+?)\s*$", answer)
        if m:
            cur = m.group(1).strip().strip("`")
        # `cur is None` means the entity is ABSENT from the final answer, not that it is specific --
        # the strongest case for rescue, and it was previously skipped. It happens when the coordinator
        # never synthesized the entity at all: measured on ginstall/vasnprintf, where the coordinator
        # emitted a tool call as literal TEXT, stopped after one worker, and answered 23 of 101
        # variables. The remaining 78 were then default-filled with `undefined` DOWNSTREAM of this
        # pass, so nothing here ever saw an `undefined` to replace. Absent and `undefined` are the
        # same non-answer and both must be rescued.
        if cur is not None and not _UNDEF_RE.match(cur):
            continue                                   # final answer is already specific -> leave it
        for d in claims:                               # earliest specific claim wins
            t = d.get(vid)
            if t and not _UNDEF_RE.match(t):
                rescued[vid] = t
                break
    if not rescued:
        return answer
    appended = []
    for vid, t in rescued.items():                     # rewrite BOTH representations consistently
        pat_line = rf"(?mi)^(\s*-?\s*{re.escape(vid)}\s*[:=]\s*).+?$"
        pat_json = rf'("{re.escape(vid)}"\s*:\s*)"[^"]*"'
        hit = re.search(pat_line, answer) or re.search(pat_json, answer)
        answer = re.sub(pat_line, lambda mo: mo.group(1) + t, answer)
        answer = re.sub(pat_json, lambda mo: mo.group(1) + json.dumps(t), answer)
        if not hit:
            appended.append(f"{vid}: {t}")             # absent entirely -> add it, nothing to rewrite
    if appended:
        answer = answer.rstrip() + "\n" + "\n".join(appended) + "\n"
    print(f"[undef-rescue] restored specific types over `undefined`: {rescued}")
    return answer


# --- size-consistency coercion (deterministic, no model) -----------------------------------------
# The question states each entity's byte SIZE as a given. A reported type whose width contradicts that
# size is a PROVABLE error -- an 8-byte slot cannot hold `int`, a 4-byte slot cannot hold a pointer --
# detectable without ground truth. Measured 2026-07-26 over 30 functions: 17 such variables across
# 11 functions; rewriting each to the same-family type of the DECLARED width scored 3 better / 0 worse
# / 4 tied, mean +5.52 on affected functions (+1.29 amortized). Unlike a prompt change this is a pure
# post-hoc transform of a fixed answer, so the +-11.8 run-to-run noise floor does not apply to it.
_TYPE_WIDTH = {
    "char": 1, "uchar": 1, "byte": 1, "bool": 1, "_bool": 1, "schar": 1, "signed char": 1,
    "unsigned char": 1, "int8_t": 1, "uint8_t": 1, "undefined1": 1,
    "short": 2, "ushort": 2, "unsigned short": 2, "word": 2, "int16_t": 2, "uint16_t": 2,
    "undefined2": 2,
    "int": 4, "uint": 4, "unsigned int": 4, "float": 4, "dword": 4, "int32_t": 4, "uint32_t": 4,
    "undefined4": 4, "wchar_t": 4,
    "long": 8, "ulong": 8, "unsigned long": 8, "size_t": 8, "ssize_t": 8, "double": 8, "qword": 8,
    "longlong": 8, "ulonglong": 8, "uintmax_t": 8, "intmax_t": 8, "off_t": 8, "idx_t": 8,
    "ptrdiff_t": 8, "int64_t": 8, "uint64_t": 8, "undefined8": 8,
}
_UNSIGNED = {"uchar", "byte", "unsigned char", "ushort", "unsigned short", "word", "uint",
             "unsigned int", "dword", "ulong", "unsigned long", "size_t", "qword", "ulonglong",
             "uintmax_t", "uint8_t", "uint16_t", "uint32_t", "uint64_t"}
_WIDTH_TYPE = {8: ("long", "ulong"), 4: ("int", "uint"), 2: ("short", "ushort"), 1: ("char", "uchar")}


def _type_width(t: str):
    """Byte width of a reported type, or None if unknown. Any pointer is 8 on x86-64."""
    t = str(t or "").strip()
    if t.endswith("*"):
        return 8
    return _TYPE_WIDTH.get(t.lower())


def _coerce_sizes(question: str, answer: str) -> str:
    """Rewrite every reported type whose width contradicts the entity's declared size."""
    if os.environ.get("AGENTIC_NO_SIZE_COERCE", "") in ("1", "true", "yes"):
        return answer
    sizes = {m.group(1): int(m.group(2)) for m in re.finditer(
        r"(?m)^\s*(V\d+)\s+(?:register|stack)\s+\S+\s+(\d+)\s*$", question or "")}
    if not sizes:
        return answer
    fixed = {}
    for vid, want in sizes.items():
        m = re.search(rf'(?mi)^\s*-?\s*{re.escape(vid)}\s*[:=]\s*(.+?)\s*$', answer)
        if not m:
            m = re.search(rf'"{re.escape(vid)}"\s*:\s*"([^"]*)"', answer)
        if not m:
            continue
        cur = m.group(1).strip()
        new = None
        # AGGREGATE SLOT. A pointer occupies 8 bytes, so a slot WIDER than that cannot hold one --
        # the slot IS those bytes. A reported `T *` on such a slot means the value is an inline ARRAY
        # of T, which is exactly how the code uses it: `p[i]` compiles identically for `int *p` and
        # `int p[6]`, so the pointer/array distinction is invisible in the instruction stream and the
        # declared size is the only thing that settles it. Observed on date/posix_time_parse V4, GT
        # `int[6]` in a 24-byte slot, reported `int*` -- scored 1/6, halting at `!AgreeIsCPointer`,
        # the earliest and most expensive failure in the metric. Forced rather than chosen: the
        # element type is the model's own pointee and the count is an exact division.
        if want > 8 and cur.endswith("*"):
            el = cur[:-1].strip()
            ew = _type_width(el)
            if el and ew and want % ew == 0:
                new = f"{el}[{want // ew}]"
        if new is None:
            w = _type_width(cur)
            if w is None or want not in _WIDTH_TYPE:
                continue
            # NARROWING ONLY. A type WIDER than the slot is impossible -- a pointer cannot occupy 4
            # bytes -- so rewriting it to an integer of the declared width is forced, not chosen. The
            # reverse is a GUESS: `int` on an 8-byte slot may be `long` OR any pointer, and picking
            # the integer family loses. Measured on comm/readlinebuffer_delim V7 (GT `char *`):
            # coercing int -> long cost 86.21 -> 79.31, while the three narrowing fixes gained
            # +25.00, +11.91 and +1.75.
            if w <= want:
                continue
            signed_t, unsigned_t = _WIDTH_TYPE[want]
            new = unsigned_t if cur.lower() in _UNSIGNED else signed_t
        fixed[vid] = (cur, new)
        answer = re.sub(rf'(?mi)^(\s*-?\s*{re.escape(vid)}\s*[:=]\s*).+?$',
                        lambda mo: mo.group(1) + new, answer)
        answer = re.sub(rf'("{re.escape(vid)}"\s*:\s*)"[^"]*"',
                        lambda mo: mo.group(1) + json.dumps(new), answer)
    if fixed:
        print("[size-coerce] " + ", ".join(f"{v}: {a} -> {b} ({sizes[v]}B slot)"
                                           for v, (a, b) in sorted(fixed.items())))
    return answer


def _certified_trailer(oid: str, question: str, answer: str, opts: dict) -> str:
    """Append the ORACLE-CERTIFIED trailer, computed DETERMINISTICALLY in-process (not via the LLM),
    reproducing pipeline._analyze_oid_impl exactly — including floor semantics. This guarantees the
    certified facts override the model's answer regardless of subagent behaviour, preserving the
    validated +2.65pp / zero-regression property."""
    oracle_facts = _collect_oracle_facts(oid, question, opts)
    if not oracle_facts:
        return answer

    def _synth_ty(vid):
        for _j in reversed(re.findall(r"\{[^{}]*\}", answer)):
            try:
                _o = json.loads(_j)
                if vid in _o:
                    return str(_o[vid])
            except Exception:  # noqa: BLE001
                pass
        _m = re.search(rf"(?mi)^\s*-?\s*{re.escape(vid)}\s*:\s*(.+?)\s*$", answer)
        return _m.group(1) if _m else ""

    from agentic.tasks.type_recovery import is_shapeless_pointer as _shapeless

    lines = []
    for vid, (ctype, _c, _mode) in sorted(oracle_facts.items(), key=lambda kv: kv[0]):
        # A FLOOR is a lower bound — "this is a pointer", pointee unknown — not an exact type, so it
        # defers whenever the model already answered with a pointer.
        #
        # ORDERING CONSTRAINT: any model-driven pass that runs BEFORE this one can preempt a correct
        # certification through exactly this rule. A targeted re-query stage (since removed) upgraded
        # sum/argmatch_to_argument V6 from `int` to `char *`; that pointer then made this floor defer,
        # suppressing a `void *` certification that was exactly right (63.89 -> 61.11). Keep model
        # passes after certification, or have them skip entities an oracle already claims.
        #
        # Deliberately NOT depth-aware. Requiring the model to match the floor's indirection depth was
        # tried and MEASURED WORSE (ginstall/hash_rehash 45.10 -> 37.25): the certifying oracle's depth
        # is itself unreliable. There, GT is `Hash_table *` (one level) while decompiler_pointer
        # certified `void **`; the depth rule trusted that and overrode the model's correctly-shaped
        # `struct *`. For a pointee-unknown fact the sound content is only ">= pointer", never the
        # exact level — so any model pointer satisfies it.
        if _mode == "floor" and "*" in _synth_ty(vid):
            continue
        # A `shape` fact recovers field LAYOUT, never a source-level struct name. It is strictly more
        # informative than a pointee-unknown answer (`void *`, or the tagless `struct *` the model
        # emits when it sees an aggregate it cannot describe), so it replaces those -- but a named
        # pointee the agents produced is a claim this oracle cannot make, so it defers to one.
        if _mode == "shape":
            cur = _synth_ty(vid)
            if "*" in cur and not _shapeless(cur):
                continue
        # A SCALAR fact is the mirror of a floor and the only NEGATIVE claim any oracle makes: its
        # content is "not a pointer", and the integer it carries is the callee's declared type, not a
        # considered choice between `long`/`size_t`/`int`. So it fires only to demote a pointer answer
        # and otherwise defers -- the model's own integer is at least as good, and the scoring rule
        # that matters (`AgreeIsCPointer`) has already been satisfied by any integer at all.
        if _mode == "scalar" and "*" not in _synth_ty(vid):
            continue
        # A SIGN fact carries one bit: "this integer is unsigned". It is orthogonal to the class and the
        # width, so it applies only to an answer that is already a non-pointer, non-array scalar and
        # abstains otherwise -- a pointer answer is a claim this oracle cannot speak to. Measured need:
        # on sha512_process_block 171 of 179 variables had the class, width and pointer-ness all correct
        # and differed from ground truth by the sign alone, scoring 5/6 on the graded metric but 0 on
        # exact match.
        if _mode == "sign":
            _cur = _synth_ty(vid)
            if "*" in _cur or "[" in _cur or not _cur.strip():
                continue
        lines.append(f"- {vid}: {ctype}")
    if lines:
        answer = (answer.rstrip()
                  + "\n\nORACLE-CERTIFIED (deterministic, authoritative — overrides the above):\n"
                  + "\n".join(lines) + "\n")
    return answer


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
            system_prompt=COORDINATOR_PROMPT.format(oid=oid, vaddr=vaddr),
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
