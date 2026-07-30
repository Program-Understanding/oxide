"""Agent MCP server for the agentic_re analyzer module.

A SEPARATE FastMCP server (stdio) exposing ONLY the fine-grained analysis tools + deterministic oracle
tools the deepagents pipeline uses. Kept OUT of Oxide's default `oxide/mcp_server.py` so that file stays
pristine — `deepagent.py` spawns THIS server. Add or change agent tools here, never in oxide/mcp_server.py.
"""
from mcp.server.fastmcp import FastMCP
from typing import Any, Literal  # noqa: F401
import argparse
import sys
import os
import re
import json  # noqa: F401

parser = argparse.ArgumentParser('oxide agentic MCP server')
parser.add_argument("--oxidepath", type=str, required=False, default="./")
args = parser.parse_args()

# Import Oxide + the agentic package (which lives in this analyzer module).
sys.path.append(args.oxidepath + '/src')
sys.path.append(args.oxidepath + '/src/oxide')
sys.path.append(args.oxidepath + '/src/oxide/modules/analyzers/agentic_re')
from oxide.core import oxide as oxide  # noqa: F401,E402  (initializes Oxide)

mcp = FastMCP("oxide-agentic")

# ============================================================================================
#  Agentic fine-grained analysis tools + deterministic oracle tools.
#  These surface the agentic tool backends (agentic/tools/{ghidra,elf,util}) and the deterministic
#  STATIC type oracles (grounding.py + tasks/type_recovery) through this MCP server, so a deepagents
#  client gets its tools from a single source. The opt-in dynamic runtime probe lives in extras/ and is
#  applied in-process by deepagent's certified trailer, not exposed as an MCP tool.
# ============================================================================================
from oxide.core.oxide import api as _oxapi
from agentic import tools as _agentic_tools
from agentic import grounding as _G
from agentic.tasks import type_recovery as _type_recovery  # noqa: F401 registers the 4 static oracles
os.environ.setdefault("AGENTIC_OUT_CAP", "0")   # tool layer's out_cap() is REQUIRED; safe default


_CT_CACHE: dict = {}      # oid -> call_tool dispatcher (keeps OxideContext + its retrievals warm)
_ORACLE_CACHE: dict = {}  # (kind, oid, ...) -> facts (expensive oracle calls are pure per question)


def _ct(oid: str):
    """Deterministic tool dispatcher bound to an oid (memoize=False so oracles get full output).
    Cached per-oid so OxideContext — and its in-memory Ghidra/ELF retrievals — is built ONCE per
    server process instead of being rebuilt (and re-fetched) on every tool call. This is the fix for
    the per-call re-analysis stall that hung the live run."""
    ct = _CT_CACHE.get(oid)
    if ct is None:
        _schemas, ct = _agentic_tools.build_tools(_oxapi, oid, memoize=False)
        _CT_CACHE[oid] = ct
    return ct


def _as_json(s):
    try:
        return json.loads(s)
    except Exception:  # noqa: BLE001
        return s


# Per-process result memo for the addr-based analysis tools. Keyed on the oid, tool, and NORMALIZED
# args, so calls that differ only in address zero-padding ("0x00103108" vs "0x103108") collapse to one
# key. The tool backends are deterministic pure functions of (oid, args), so serving a repeat from the
# memo returns byte-identical output — determinism is preserved — while skipping the redundant backend
# re-run + re-format. This is the fix for the observed thrashing where the model re-decompiles / re-reads
# the same slot with a differently-formatted address and each variant missed the cache.
_TOOL_RESULT_CACHE: dict = {}


def _norm_addr(a):
    """Canonicalize a hex address so '0x00103108', '0x103108', '103108', '0X103108' map to one form
    ('0x103108'). A non-hex value (e.g. a function name) passes through unchanged."""
    if not isinstance(a, str):
        return a
    s = a.strip()
    try:
        return f"0x{int(s, 16):x}"
    except (ValueError, TypeError):
        return s


def _norm_off(o):
    """Canonicalize a signed hex frame offset ('-0x08' -> '-0x8', '0x20' -> '0x20'). Empty / non-hex
    passes through unchanged (so 'list all slots' and any symbolic offset still work)."""
    if not isinstance(o, str) or not o.strip():
        return o
    s = o.strip()
    neg = s.startswith("-")
    body = s[1:] if neg else s
    try:
        v = int(body, 16)
    except (ValueError, TypeError):
        return o
    return f"-0x{v:x}" if neg else f"0x{v:x}"


def _log_call(tool: str, args: dict, cached: bool, out):
    """Append one JSONL record per tool INVOCATION to $AGENTIC_TOOL_LOG (no-op when unset).

    The agent's tools run in THIS process (the MCP server child), so the client-side trace file never
    sees them — it only records the in-process oracle calls. This log is the only place the agent's
    actual tool SELECTION is observable. Logged before the memo is consulted, so a repeated call is
    recorded as a repeat (`cached: true`) rather than silently absorbed."""
    p = os.environ.get("AGENTIC_TOOL_LOG", "")
    if not p:
        return
    try:
        import time
        with open(p, "a") as fh:
            fh.write(json.dumps({"tool": tool, "args": args, "cached": cached, "t": time.time(),
                                 "out": str(out)[:400]}) + "\n")
    except Exception:  # noqa: BLE001  never let logging break a tool call
        pass


# --- repeat-breaker state (opt-in via AGENTIC_REPEAT_BREAKER) -----------------------------------
# Measured 2026-07-26 over 72 logged agent tool calls: 32% are EXACT repeats (same tool, same args),
# and the repeat rate tracks the score inversely (0%/29%/37%/48% -> 91.67/93.14/70.83/47.44). The
# model's response to uncertainty is not to pick a DIFFERENT tool — it re-calls the same one. The memo
# above hides that from it: a repeat silently returns the identical result, so the model never learns
# it is looping. These helpers make the repeat visible and hand back the concrete unexplored work,
# computed deterministically from the binary — no model judgement involved in deciding what to suggest.
_SEEN: dict = {}       # oid -> {"offsets": set(str), "disas_addrs": set(str)}
_FN_FACTS: dict = {}   # (oid, faddr) -> {"slots": [str], "callees": [str]}
_NOISE_CALLEES = {"__stack_chk_fail", "__assert_fail", "abort", "__errno_location",
                  "__cxa_finalize", "_exit", "exit"}


def _fn_facts(oid: str, addr: str) -> dict:
    """Every rbp stack slot and every callee of the function at `addr`. Uses the raw dispatcher (not
    _call) so building the hint can never recurse back into the memo/repeat path."""
    key = (oid, _norm_addr(addr))
    if key not in _FN_FACTS:
        slots, callees = [], []
        try:
            # _ct returns the tool's TEXT; _as_json is what turns it back into the dict (the same
            # step _call does). Without it `slots` silently stayed empty.
            sv = _as_json(_ct(oid)("stack_var", {"addr": _norm_addr(addr)}))
            if isinstance(sv, str):
                sv = _as_json(sv.replace("'", '"'))
            if isinstance(sv, dict):
                slots = [s["offset"] for s in sv.get("slots", []) if "offset" in s]
        except Exception:  # noqa: BLE001
            pass
        try:
            d = str(_ct(oid)("disassemble", {"addr": _norm_addr(addr), "n_instructions": 8}))
            m = re.match(r"CALLS:\s*([^\n]+)", d)
            if m:
                # Drop the compiler-inserted callees — they take no meaningful argument and pointing
                # the agent at them is a wasted tool turn.
                callees = [c.strip() for c in m.group(1).split(",")
                           if c.strip() and c.strip() not in _NOISE_CALLEES]
        except Exception:  # noqa: BLE001
            pass
        _FN_FACTS[key] = {"slots": slots, "callees": callees}
    return _FN_FACTS[key]


def _repeat_hint(oid: str, tool: str, args: dict) -> str:
    """What the agent has demonstrably NOT looked at yet, as an appendable directive."""
    addr = args.get("addr")
    if not addr:
        return ""
    facts = _fn_facts(oid, addr)
    seen = _SEEN.setdefault(oid, {"offsets": set(), "disas_addrs": set()})
    todo = [s for s in facts["slots"] if s not in seen["offsets"]]
    parts = []
    if todo:
        parts.append("stack slots you have NOT queried yet: "
                     + ", ".join(todo[:12])
                     + "  (call stack_var with one of these offsets)")
    # A callee is "uninspected" while the agent has disassembled nothing but the function itself.
    if facts["callees"] and len(seen["disas_addrs"]) <= 1:
        parts.append("you have not inspected ANY callee; the value may flow into one of: "
                     + ", ".join(facts["callees"][:8]))
    if not parts:
        return ("\n\n[REPEAT] You already made this exact call and the result has not changed. You have "
                "queried every stack slot. Stop calling tools and report your findings now.")
    return ("\n\n[REPEAT] You already made this exact call and the result has not changed. Do NOT repeat "
            "it. " + "  ".join(parts))


# --- import-name masking, for the contamination ablation (AGENTIC_MASK_IMPORTS) -------------------
# Stripping removes LOCAL symbols only. Dynamic imports must survive for the linker, so
# `__fpending`, `ferror_unlocked` etc. remain readable, and `disassemble` puts them at the head of
# every result. A function calling exactly those, in a binary whose strings still say "GNU coreutils",
# is effectively a fingerprint -- so a model that memorised the source could recognise it without ever
# seeing a local name. This masks those names on the AGENT path only: every import becomes a stable
# opaque token (EXT_007), so call structure and arity are preserved while identity is not.
#
# Applied HERE, in the MCP server, precisely because the deterministic oracles do NOT go through it --
# they build their own in-process dispatcher. Their use of the same names is sound DEDUCTION ("arg 1
# of fclose is FILE *"), not recognition, and must not be ablated.
#
# The result bounds contamination in ONE direction. A small drop means neither memorisation nor
# import-based deduction contributes much to the agent's answers, which caps how much memorisation
# could explain. A large drop is ambiguous: it would also be produced by legitimate ABI reasoning.
_IMPORT_MASK: dict = {}


def _mask_imports(oid: str, text):
    if os.environ.get("AGENTIC_MASK_IMPORTS", "") not in ("1", "true", "yes"):
        return text
    m = _IMPORT_MASK.get(oid)
    if m is None:
        try:
            imp = _as_json(_ct(oid)("imports", {}))
            names = imp.get("imports", []) if isinstance(imp, dict) else []
        except Exception:  # noqa: BLE001
            names = []
        # keep the toolchain/runtime scaffolding visible -- it identifies nothing about the function
        skip = {"_ITM_deregisterTMCloneTable", "_ITM_registerTMCloneTable", "__gmon_start__",
                "__libc_start_main", "__cxa_atexit", "__cxa_finalize", "__stack_chk_fail"}
        m = {n: f"EXT_{i:03d}" for i, n in enumerate(sorted(x for x in names if x not in skip))}
        _IMPORT_MASK[oid] = m
    t = str(text)
    for n, ph in m.items():
        t = re.sub(rf"(?<![\w.]){re.escape(n)}(?![\w])", ph, t)
    return t


def _call(oid: str, tool: str, args: dict):
    """Dispatch a tool with per-process memoization on (oid, tool, normalized args). Repeats return the
    cached, byte-identical result instead of re-running the backend."""
    key = (oid, tool, tuple(sorted((k, str(v)) for k, v in args.items())))
    seen = _SEEN.setdefault(oid, {"offsets": set(), "disas_addrs": set()})
    if tool == "stack_var" and str(args.get("offset", "")).strip():
        seen["offsets"].add(_norm_off(args["offset"]))
    if tool in ("disassemble", "decompile") and args.get("addr"):
        seen["disas_addrs"].add(_norm_addr(args["addr"]))
    if key in _TOOL_RESULT_CACHE:
        res = _TOOL_RESULT_CACHE[key]
        if os.environ.get("AGENTIC_REPEAT_BREAKER", "") in ("1", "true", "yes"):
            # Return a STRING so the directive survives; the memo keeps the pristine value.
            res = f"{res}{_repeat_hint(oid, tool, args)}"
        _log_call(tool, args, True, res)
        return res
    res = _mask_imports(oid, _as_json(_ct(oid)(tool, args)))
    _TOOL_RESULT_CACHE[key] = res
    _log_call(tool, args, False, res)
    return res


# ---- fine-grained analysis tools (thin wrappers over the agentic tool backends) ----------------
@mcp.tool()
async def decompile(oid: str, addr: str) -> Any:
    """Ghidra C-like decompilation of the function at `addr` (a 0x virtual address OR a function name).
    Works on stripped binaries — pass the function's virtual address. Start here for type recovery."""
    return _call(oid, "decompile", {"addr": _norm_addr(addr)})


@mcp.tool()
async def disassemble(oid: str, addr: str, n_instructions: int = 128) -> Any:
    """Instruction-level disassembly window (Ghidra) starting at a function name or 0x virtual address.
    Distinct from disasm_and_info_for_func (whole-function): use this for a focused instruction span."""
    return _call(oid, "disassemble", {"addr": _norm_addr(addr), "n_instructions": n_instructions})


@mcp.tool()
async def stack_var(oid: str, addr: str, offset: str = "") -> Any:
    """Stack-frame slot(s) of the function at addr plus the instructions that access them. Give a frame
    offset (e.g. "-0x20") for one slot, or omit offset to list all slots. Key for type recovery."""
    return _call(oid, "stack_var", {"addr": _norm_addr(addr), "offset": _norm_off(offset)})


@mcp.tool()
async def register_usage(oid: str, addr: str, reg: str) -> Any:
    """How a REGISTER PARAMETER is used, read from the ASSEMBLY: where the prologue spills it to its
    home stack slot, every access to that slot, whether the value is DEREFERENCED (and at which byte
    offsets -> it holds an address), whether it is used in address arithmetic, and which callees
    receive it at which argument position. `reg` is the register-space offset from the question
    ("0x38" = 1st arg, "0x30" = 2nd, "0x10" = 3rd, "0x8" = 4th) or a name ("rdi"). `stack_var` does
    NOT work for registers -- use this. Returns INCONCLUSIVE rather than guessing when the value
    cannot be followed across control flow."""
    return _call(oid, "register_usage", {"addr": _norm_addr(addr), "reg": reg})


@mcp.tool()
async def value_usage(oid: str, addr: str, var: str) -> Any:
    """How a REGISTER PARAMETER or named local is USED in the function at `addr`: whether it is
    dereferenced (and at which byte offsets), indexed as an array, used in address vs. scalar
    arithmetic, and which callees receive it at which argument position. `var` is a decompiler
    identifier — a variable at `register 0x38` is `param_1`, `0x30` is `param_2`, `0x10` is `param_3`,
    `0x8` is `param_4`. `stack_var` does NOT work for registers; use this instead. Passing a raw
    register name returns a hint naming the right identifier."""
    return _call(oid, "value_usage", {"addr": _norm_addr(addr), "var": var})


@mcp.tool()
async def xrefs_to(oid: str, addr: str) -> Any:
    """Cross-references (callers / code references) to the address or function `addr`."""
    return _call(oid, "xrefs_to", {"addr": _norm_addr(addr)})


@mcp.tool()
async def read_values(oid: str, addr: str, type: str = "int32", count: int = 16,
                      signed: bool = True, endian: str = "little") -> Any:
    """Read a typed integer array from the binary at a virtual address (type in int8/16/32/64)."""
    return _call(oid, "read_values", {"addr": _norm_addr(addr), "type": type, "count": count,
                                      "signed": signed, "endian": endian})


@mcp.tool()
async def compute(oid: str, expr: str) -> Any:
    """Exact arithmetic/bitwise evaluation of an integer expression (safe AST eval, no code run).
    Use for offset/address math instead of guessing."""
    return _as_json(_ct(oid)("compute", {"expr": expr}))


# ---- deterministic oracle tools (the hybrid trust layer) ---------------------------------------
def _canon_question(vaddr: str, variables: str) -> str:
    """Canonical oracle question 'function at vaddr <va>.\\n<variable lines>' from explicit args, so
    the caller cannot omit the vaddr (which makes the oracles silently return [])."""
    va = vaddr if str(vaddr).startswith("0x") else ("0x" + str(vaddr) if vaddr else "")
    return f"function at vaddr {va}.\n{variables}\n"


@mcp.tool()
async def static_type_oracles(oid: str, addr: str, variables: str, which: str = "") -> Any:
    """CERTIFIED and deterministic — re-derived from the binary and public ABI knowledge, not guessed, so it outranks your own reading of the decompilation.
    EVIDENCE: all four oracles above, in one call; earlier ones win on the same variable.
    USE WHEN: several kinds of evidence are present at once, or you have no specific hypothesis
    about where a variable's type would come from.
    `variables`: the variable list, one `V<n>  <register 0x..|stack -0x..>  <size>` per line."""
    return _call(oid, "static_type_oracles",
                 {"addr": _norm_addr(addr), "variables": variables, "which": which})


@mcp.tool()
async def callee_signature(oid: str, addr: str, variables: str) -> Any:
    """CERTIFIED and deterministic — re-derived from the binary and public ABI knowledge, not guessed, so it outranks your own reading of the decompilation.
    EVIDENCE: a register-passed parameter handed to a C-library function whose ABI fixes that
    argument's type (argument 1 of `fclose` is `FILE *`).
    USE WHEN: the function calls libc.
    `variables`: the variable list, one `V<n>  <register 0x..|stack -0x..>  <size>` per line."""
    return _call(oid, "callee_signature", {"addr": _norm_addr(addr), "variables": variables})


@mcp.tool()
async def decompiler_pointer(oid: str, addr: str, variables: str) -> Any:
    """CERTIFIED and deterministic — re-derived from the binary and public ABI knowledge, not guessed, so it outranks your own reading of the decompilation.
    EVIDENCE: the decompiler's own recovered pointer declarations.
    USE WHEN: you suspect a value is a pointer but the assembly does not settle it.
    `variables`: the variable list, one `V<n>  <register 0x..|stack -0x..>  <size>` per line."""
    return _call(oid, "decompiler_pointer", {"addr": _norm_addr(addr), "variables": variables})


@mcp.tool()
async def spilled_param(oid: str, addr: str, variables: str) -> Any:
    """CERTIFIED and deterministic — re-derived from the binary and public ABI knowledge, not guessed, so it outranks your own reading of the decompilation.
    EVIDENCE: the prologue store that copies an argument register into a stack slot, making that
    slot a copy of the parameter.
    USE WHEN: stack locals mirror the parameters.
    `variables`: the variable list, one `V<n>  <register 0x..|stack -0x..>  <size>` per line."""
    return _call(oid, "spilled_param", {"addr": _norm_addr(addr), "variables": variables})


@mcp.tool()
async def interprocedural_param_usage(oid: str, addr: str, variables: str) -> Any:
    """CERTIFIED and deterministic — re-derived from the binary and public ABI knowledge, not guessed, so it outranks your own reading of the decompilation.
    EVIDENCE: a parameter forwarded through user functions — resolved either by the fixed-type
    library position it eventually reaches, or by the first callee that declared a concrete type for
    that position and whether it is ever dereferenced there. Uniquely among the oracles this can
    return a NEGATIVE result, "V<n> IS NOT A POINTER", for a forwarded length/count/index.
    USE WHEN: a parameter is passed straight into another local function — especially when it has no
    local usage of its own, or when you are unsure whether an 8-byte parameter is a pointer or a size.
    `variables`: the variable list, one `V<n>  <register 0x..|stack -0x..>  <size>` per line."""
    return _call(oid, "interprocedural_param_usage", {"addr": _norm_addr(addr), "variables": variables})


@mcp.tool()
async def signedness(oid: str, addr: str, variables: str) -> Any:
    """CERTIFIED and deterministic — re-derived from the binary and public ABI knowledge, not guessed, so it outranks your own reading of the decompilation.
    EVIDENCE: instructions whose signed and unsigned forms differ, which the compiler is FORCED to
    choose between — `shr` vs `sar`, `movzx` vs `movsx`, `div` vs `idiv`, and rotates (only
    expressible on an unsigned value). Reports "V<n> IS UNSIGNED" and the fixed-width C type.
    USE WHEN: a variable is an integer and you must decide signed vs unsigned — the decompilation
    shows `long`/`int` for both, so it cannot tell you, and this can.
    `variables`: the variable list, one `V<n>  <register 0x..|stack -0x..>  <size>` per line."""
    return _call(oid, "signedness", {"addr": _norm_addr(addr), "variables": variables})




if __name__ == "__main__":
    mcp.run(transport="stdio")
