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
#  These surface the existing agentic tool backends (core/libraries/agentic/tools/{ghidra,elf,util})
#  and the deterministic type oracles (grounding.py + tasks/{type_recovery,runtime_probe}) through
#  this MCP server, so a deepagents client can get ALL of its tools from a single source.
# ============================================================================================
from oxide.core.oxide import api as _oxapi
from agentic import tools as _agentic_tools
from agentic import grounding as _G
from agentic.tasks import type_recovery as _type_recovery  # noqa: F401 registers static oracles
from agentic.tasks import runtime_probe as _runtime_probe   # noqa: F401 registers runtime oracle
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
async def value_usage(oid: str, addr: str, var: str) -> Any:
    """How a decompiler variable's value is used across the function at addr (reads/writes/calls it
    flows into) — evidence for its type."""
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


@mcp.tool()
async def file_offset_to_vaddr(oid: str, file_offset: str) -> Any:
    """Convert an ELF file offset to a virtual address (sanctioned coordinate conversion)."""
    return _call(oid, "file_offset_to_vaddr", {"file_offset": _norm_addr(file_offset)})


@mcp.tool()
async def vaddr_to_file_offset(oid: str, vaddr: str) -> Any:
    """Convert a virtual address to an ELF file offset (sanctioned coordinate conversion)."""
    return _call(oid, "vaddr_to_file_offset", {"vaddr": _norm_addr(vaddr)})


@mcp.tool()
async def imports(oid: str) -> Any:
    """Imported (PLT) library symbols of the binary."""
    return _as_json(_ct(oid)("imports", {}))


@mcp.tool()
async def search_bytes(oid: str, hex_pattern: str) -> Any:
    """Find occurrences of a hex byte pattern (e.g. "48 89 e5") in the binary; returns hit locations."""
    return _as_json(_ct(oid)("search_bytes", {"hex_pattern": hex_pattern}))


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


@mcp.tool()
async def runtime_type_probe(oid: str, vaddr: str, variables: str) -> Any:
    """Execution-grounded (angr) type oracle. Drives the function under a controlled emulator and
    certifies a stack slot's representational type from observed runtime behaviour (dereference =>
    pointer, XMM => float/double, movsx/idiv => signed, div => unsigned). Fires ONLY on the residual
    stack slots the static oracles left un-anchored; pointer verdicts are representational FLOORS
    (they defer to a more specific pointer). `vaddr`: function virtual address; `variables`: variable
    list (one 'V<n>  <location>  <size>' per line). Returns certified facts (possibly empty)."""
    question = _canon_question(vaddr, variables)
    key = ("runtime", oid, question)
    if key in _ORACLE_CACHE:
        return _ORACLE_CACHE[key]
    res = _runtime_probe._oracle_runtime_type_probe(_ct(oid), question)
    _ORACLE_CACHE[key] = res
    return res




if __name__ == "__main__":
    mcp.run(transport="stdio")
