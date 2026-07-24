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


def _call(oid: str, tool: str, args: dict):
    """Dispatch a tool with per-process memoization on (oid, tool, normalized args). Repeats return the
    cached, byte-identical result instead of re-running the backend."""
    key = (oid, tool, tuple(sorted((k, str(v)) for k, v in args.items())))
    if key in _TOOL_RESULT_CACHE:
        return _TOOL_RESULT_CACHE[key]
    res = _as_json(_ct(oid)(tool, args))
    _TOOL_RESULT_CACHE[key] = res
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
async def static_type_oracles(
        oid: str, vaddr: str, variables: str,
        which: str = "callee_signature,decompiler_pointer,interprocedural_param_usage,spilled_param") -> Any:
    """Run the deterministic STATIC type oracles and return CERTIFIED per-variable facts
    [{vid, ctype, source, claim, reason, floor, oracle}] — ABI/decompiler-certain and AUTHORITATIVE
    (override model guesses). `vaddr`: the function's virtual address, e.g. '0x107d3e'. `variables`:
    the variable list, one per line as `V<n>  <register 0x..|stack -0x..>  <size>`. Earlier oracles
    win on the same variable."""
    question = _canon_question(vaddr, variables)
    key = ("static", oid, which, question)
    if key in _ORACLE_CACHE:
        return _ORACLE_CACHE[key]
    ct = _ct(oid)
    facts, seen = [], set()
    for name, fn in _G.resolve_domain_oracles(which, question):
        try:
            for f in fn(ct, question):
                if f["vid"] in seen:
                    continue
                seen.add(f["vid"])
                facts.append({**f, "oracle": name})
        except Exception as e:  # noqa: BLE001
            print(f"static_type_oracles: {name} skipped: {e}", file=sys.stderr)
    _ORACLE_CACHE[key] = facts
    return facts


if __name__ == "__main__":
    mcp.run(transport="stdio")
