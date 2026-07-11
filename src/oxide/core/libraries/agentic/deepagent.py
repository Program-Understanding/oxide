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
import json
import os
import re
import sys

from oxide.core.libraries.agentic import config as C

# The tools the agent may call — all ADDRESS-based (they take the function's 0x vaddr), so they work
# on a stripped binary where the function has no symbol name (the earlier loop was caused by the LLM
# guessing function names for name-based tools like disasm_and_info_for_func). Includes the two
# deterministic oracle tools (the hybrid trust layer).
WORKER_TOOLS = {
    "decompile", "disassemble", "stack_var", "xrefs_to", "read_values", "compute",
    "static_type_oracles", "runtime_type_probe",
}

COORDINATOR_PROMPT = """You are a type-recovery expert for a STRIPPED x86-64 binary. The oid is \
`{oid}` and the target function is at virtual address `{vaddr}`. Recover the precise C type of each \
variable listed in the user message. Pass oid=`{oid}` to every tool, and use addr=`{vaddr}` (the \
function has NO symbol name — always reference it by this address).

Follow this workflow with the tools — do not skip the tools, and STOP once you output the answer:
1. Call `decompile(oid, addr="{vaddr}")` to read the function's C code.
2. Call `static_type_oracles(oid, vaddr="{vaddr}", variables=<the variable lines>)` and \
`runtime_type_probe(oid, vaddr="{vaddr}", variables=<the variable lines>)`. Any type they CERTIFY is \
AUTHORITATIVE — use it exactly (a "floor" pointer may be made more specific if the code shows the \
pointee).
3. For variables no oracle certified, inspect them with `stack_var` (pass the frame offset, e.g. \
offset="-0x18"), `disassemble`, or `xrefs_to` (all take addr="{vaddr}") and infer the type from usage.
4. Output one `<id>: <C type>` line per variable, then, on the VERY LAST line, a single JSON object \
mapping every id to its type, e.g. {{"V1": "char *", "V2": "int"}}. Exactly one type per id; unknown \
=> "undefined".

Be efficient: do not re-call a tool with identical arguments, and finish promptly."""

TYPE_WORKER_PROMPT = """You are a type-recovery specialist for a STRIPPED x86-64 binary (oid `{oid}`, \
target function at virtual address `{vaddr}` — reference it by this address, it has no symbol name).

For the variables you are assigned: `decompile(oid, addr="{vaddr}")` to read the code, call \
`static_type_oracles`/`runtime_type_probe` (with vaddr="{vaddr}" and the variable lines) for certified \
types, and inspect specifics with `stack_var`/`disassemble`/`xrefs_to` (addr="{vaddr}"). \
Infer pointer levels, arrays, struct/FILE pointers, and integer width/signedness from the usage; the \
byte size constrains the type. Certified oracle types are authoritative.

Report EXACTLY one `<id>: <C type>` line per assigned variable. Report ONLY your assigned ids. Do not \
re-call a tool with identical arguments; finish promptly."""

# the deterministic oracle tools (the hybrid trust layer the worker may consult)
ORACLE_TOOLS = {"static_type_oracles", "runtime_type_probe", "verify_finding"}

# The MCP server exposes ~38 tools; handing all of them (plus deepagents' built-in todo/fs/task
# tools) to a small model causes long, exploratory, non-converging loops. Curate to the type-recovery
# essentials + the oracle tools. This is the single biggest lever on multi-agent latency.
ALLOWED_TOOLS = WORKER_TOOLS | ORACLE_TOOLS

VERIFIER_PROMPT = """You are a deterministic-verification specialist for a stripped x86-64 binary \
with oid = `{oid}` (pass this oid to every tool call, and pass the full variable list as `question`).

Given candidate `<id>: <C type>` claims, adjudicate each variable:
1. FIRST call `static_type_oracles` and `runtime_type_probe`. Any certified fact they return is \
AUTHORITATIVE and settles that variable's type. A runtime `void *` is a lower-bound FLOOR: keep a \
more specific pointer if one is well-supported, otherwise use `void *`.
2. For variables no oracle certified, call `verify_finding` with the claim. AGREE keeps it; DISAGREE \
means the claim is wrong — re-derive it; absence of supporting evidence is INCONCLUSIVE, NEVER a \
refutation.

Report the adjudicated `<id>: <C type>` for every variable."""


def _repo_root() -> str:
    """.../oxide (the repo root that holds mcp_server.py) — 5 levels up from this file's dir."""
    here = os.path.dirname(os.path.abspath(__file__))
    return os.path.abspath(os.path.join(here, "..", "..", "..", "..", ".."))


def _mcp_server_path(opts) -> str:
    return opts.get("mcp_server_path") or C.cfg_get("mcp_server_path") \
        or os.path.join(_repo_root(), "mcp_server.py")


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


def _salvage_message(msg):
    """If `msg` (an AIMessage) has no tool_calls but its text encodes gemma tool calls, return a new
    AIMessage with structured tool_calls; otherwise return `msg` unchanged."""
    if getattr(msg, "tool_calls", None):
        return msg
    text = msg.content if isinstance(msg.content, str) else ""
    matches = list(_GEMMA_TC_RE.finditer(text))
    if not matches:
        return msg
    from langchain_core.messages import AIMessage
    tcs = [{"name": m.group(1), "args": _parse_call_args(m.group(2)),
            "id": f"salvage_{i}", "type": "tool_call"} for i, m in enumerate(matches)]
    residual = _GEMMA_TC_RE.sub("", text).strip()
    return AIMessage(content=residual, tool_calls=tcs, id=getattr(msg, "id", None),
                     usage_metadata=getattr(msg, "usage_metadata", None),
                     response_metadata=getattr(msg, "response_metadata", {}) or {})


def _salvage_result(result):
    from langchain_core.outputs import ChatGeneration
    for i, gen in enumerate(result.generations):
        new_msg = _salvage_message(gen.message)
        if new_msg is not gen.message:
            result.generations[i] = ChatGeneration(message=new_msg)
    return result


def _make_salvaging_class():
    from langchain_openai import ChatOpenAI

    class SalvagingChatOpenAI(ChatOpenAI):
        """ChatOpenAI that converts gemma's raw-text tool calls into structured tool_calls."""

        def _generate(self, messages, stop=None, run_manager=None, **kwargs):
            return _salvage_result(super()._generate(messages, stop=stop, run_manager=run_manager, **kwargs))

        async def _agenerate(self, messages, stop=None, run_manager=None, **kwargs):
            return _salvage_result(await super()._agenerate(messages, stop=stop, run_manager=run_manager, **kwargs))

    return SalvagingChatOpenAI


def _model(opts):
    """A salvaging ChatOpenAI bound to the OpenAI-compatible endpoint, greedy + seeded for determinism.
    Passing a pre-initialized model (not an 'openai:' string) keeps us on chat-completions."""
    cfg = C.resolve_config(opts)
    model_id = opts.get("worker_model") or opts.get("model") or cfg["worker_model"]
    return _make_salvaging_class()(
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


async def _load_mcp_tools(opts):
    from langchain_mcp_adapters.client import MultiServerMCPClient
    client = MultiServerMCPClient({"oxide": {
        "command": sys.executable,
        "args": [_mcp_server_path(opts), f"--oxidepath={_oxidepath(opts)}"],
        "transport": "stdio",
    }})
    return await client.get_tools()


def _collect_oracle_facts(oid: str, question: str, opts: dict) -> dict:
    """Run the static + runtime type oracles IN-PROCESS and return {vid: (ctype, oracle, floor)}
    (first oracle wins per vid). Reliable because it uses the full question (with the vaddr) — unlike
    an LLM tool call, which was observed to drop the vaddr and get empty results. Used both to INJECT
    certified facts into the prompt (so the agent reasons with them) and to build the trailer."""
    from oxide.core.oxide import api
    from oxide.core.libraries.agentic import tools as T, grounding as G
    from oxide.core.libraries.agentic.tasks import type_recovery, runtime_probe  # noqa: F401 register
    which = (opts.get("domain_oracles")
             or "callee_signature,decompiler_pointer,interprocedural_param_usage,spilled_param")
    if "runtime_type_probe" not in which:
        which = which + ",runtime_type_probe"
    _s, ct = T.build_tools(api, oid, memoize=False)
    facts: dict = {}                                         # vid -> (ctype, oname, floor); first wins
    for name, fn in G.resolve_domain_oracles(which, question):
        try:
            for f in fn(ct, question):
                if f["vid"] in facts:
                    continue
                facts[f["vid"]] = (f["ctype"], name, bool(f.get("floor", False)))
        except Exception:  # noqa: BLE001
            continue
    return facts


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

    lines = []
    for vid, (ctype, _c, _floor) in sorted(oracle_facts.items(), key=lambda kv: kv[0]):
        if _floor and "*" in _synth_ty(vid):                 # floor defers to a more specific pointer
            continue
        lines.append(f"- {vid}: {ctype}")
    if lines:
        answer = (answer.rstrip()
                  + "\n\nORACLE-CERTIFIED (deterministic, authoritative — overrides the above):\n"
                  + "\n".join(lines) + "\n")
    return answer


async def run_deep_agent(oid: str, question: str, opts: dict) -> str:
    """Build the deepagents multi-agent (coordinator + type_worker + verifier), run it on `question`,
    then append the deterministic ORACLE-CERTIFIED trailer. Returns the final per-variable answer."""
    from deepagents import create_deep_agent

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

    model = _model(opts)
    client = MultiServerMCPClient({"oxide": {
        "command": sys.executable,
        "args": [_mcp_server_path(opts), f"--oxidepath={_oxidepath(opts)}"],
        "transport": "stdio",
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
        type_worker = {
            "name": "type_worker",
            "description": "Recovers the precise C type of a group of variables by decompiling and "
                           "analysing the function at the given vaddr, and consulting the oracle tools.",
            "system_prompt": TYPE_WORKER_PROMPT.format(oid=oid, vaddr=vaddr),
            "tools": tools,
        }
        agent = create_deep_agent(
            model=model,
            tools=tools,
            system_prompt=COORDINATOR_PROMPT.format(oid=oid, vaddr=vaddr),
            subagents=[type_worker],
        )
        result = await agent.ainvoke(
            {"messages": [{"role": "user", "content": user}]},
            {"recursion_limit": recursion_limit},
        )
        answer = result["messages"][-1].content

    # clean gemma special tokens: the thinking block, then any residual <|..>/<..|> markers + a bare
    # 'thought' channel label, so only the answer text (and its final JSON line) remains.
    answer = re.sub(r"<\|?channel\|?>.*?<\|?/?channel\|?>", "", answer, flags=re.S)
    answer = re.sub(r"<\|[^>]*>|<[^>]*\|>", "", answer)
    answer = re.sub(r"(?im)^\s*thought\s*$", "", answer).strip()
    return _certified_trailer(oid, question, answer, opts)


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
