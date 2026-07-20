"""
Oxide MCP Server (read-only)

Mirrors the pyghidra-mcp tool surface using Oxide's cached analysis data.
All tools are read-only — no rename, set_type, set_comment, save, or import operations.

Usage:
    python oxide_mcp_server.py --oxidepath /path/to/oxide/
    python oxide_mcp_server.py --oxidepath /path/to/oxide/ --transport streamable-http --port 8001

Add to .mcp.json:
    {
      "mcpServers": {
        "oxide": {
          "command": "python",
          "args": ["<PATH>/oxide_mcp_server.py", "--oxidepath=<PATH>/"]
        }
      }
    }
"""

import sys
import os
import re
import logging
import argparse
from typing import Optional

from pydantic import BaseModel
import networkx as nx
from mcp.server.fastmcp import FastMCP

# ── CLI ───────────────────────────────────────────────────────────────────────

parser = argparse.ArgumentParser("oxide MCP server (read-only)")
parser.add_argument("--oxidepath", type=str, default="./",
                    help="Path to Oxide installation root.")
parser.add_argument("--transport", type=str, default="stdio",
                    choices=["stdio", "streamable-http", "sse"],
                    help="MCP transport (default: stdio).")
parser.add_argument("--host", type=str, default="127.0.0.1")
parser.add_argument("--port", type=int, default=8001)
args, _ = parser.parse_known_args()

sys.path.insert(0, os.path.join(args.oxidepath, "src"))
sys.path.insert(0, os.path.join(args.oxidepath, "src", "oxide"))
from oxide.core import oxide  # noqa: E402

logging.basicConfig(level=logging.WARNING)

mcp = FastMCP("oxide", host=args.host, port=args.port)

# ── Pydantic response models ──────────────────────────────────────────────────


class BinaryInfo(BaseModel):
    oid: str
    names: list[str]
    size: int
    analysis_available: bool


class BinaryMetadata(BaseModel):
    oid: str
    names: list[str]
    arch: Optional[str] = None
    bits: Optional[int] = None
    endian: Optional[str] = None
    format: Optional[str] = None
    size: Optional[int] = None
    num_functions: Optional[int] = None
    num_sections: Optional[int] = None


class FunctionInfo(BaseModel):
    name: str
    offset: int
    num_insns: Optional[int] = None
    complexity: Optional[int] = None
    signature: Optional[str] = None


class DecompiledFunction(BaseModel):
    name: str
    offset: Optional[int] = None
    code: Optional[str] = None
    error: Optional[str] = None


class DisassembleResult(BaseModel):
    offset: int
    count: int
    listing: str


class CallGraphResult(BaseModel):
    function_name: Optional[str] = None
    graph_mermaid: str


class SymbolInfo(BaseModel):
    name: str
    offset: int


class StringResult(BaseModel):
    value: str
    offset: int


class ExportInfo(BaseModel):
    name: str
    offset: int


class ImportInfo(BaseModel):
    name: str
    library: str


class XrefInfo(BaseModel):
    from_function: Optional[str] = None
    from_offset: int
    to_offset: int
    direction: str  # "calls_to" or "calls_from"


class BytesReadResult(BaseModel):
    offset: int
    size: int
    data: str  # hex-encoded
    error: Optional[str] = None


class FunctionSearchResult(BaseModel):
    oid: str
    function_name: str
    offset: int
    code: str
    similarity: float
    search_mode: str  # "semantic" or "literal"
    preview: Optional[str] = None


class FunctionSearchResults(BaseModel):
    results: list[FunctionSearchResult]
    query: str
    search_mode: str
    returned_count: int
    offset: int
    limit: int
    literal_total: int
    semantic_total: int
    total_functions: int


# ── Internal helpers ──────────────────────────────────────────────────────────


def _resolve_oid(name_or_oid: str) -> Optional[str]:
    """Return an OID string. Accepts a 40-char hex OID or a filename."""
    if re.fullmatch(r"[0-9a-f]{40}", name_or_oid, re.IGNORECASE):
        return name_or_oid
    matches = oxide.get_oids_with_name(name_or_oid)
    if matches:
        return next(iter(matches))
    return None


def _resolve_or_error(name_or_oid: str) -> tuple[Optional[str], Optional[str]]:
    """Resolve an OID, returning (oid, None) or (None, error_message)."""
    oid = _resolve_oid(name_or_oid)
    if oid is None:
        return None, f"Binary '{name_or_oid}' not found."
    return oid, None


def _to_offset(value) -> Optional[int]:
    """Parse an offset from an int, decimal string, or hex ('0x..') string.

    Returns None for anything unparseable (including None). Callers decide
    their own fallback (skip / error / 0).
    """
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        try:
            return int(value, 0)
        except ValueError:
            return None
    return None


def _unwrap(result, oid: str):
    """Return a module's payload for a single OID.

    Oxide `retrieve` returns either `{oid: payload}` (the common case) or, for a
    few modules, the payload flat. This normalizes both: the per-OID value if the
    result is keyed by `oid`, else the result itself when it is already flat.
    Returns None for an empty/missing result. (The one genuinely-flat exception is
    `ghidra_disasm` in `disassemble`, which is handled inline there.)
    """
    if not result:
        return None
    if isinstance(result, dict):
        inner = result.get(oid)
        if inner is not None:
            return inner
    return result


def _no_data(oid_or_name: str, what: str) -> str:
    """Actionable 'analysis missing' message naming the next step."""
    return (f"No {what} for '{oid_or_name}'. The required analysis may not have run "
            f"for this binary — ensure it is imported and the Ghidra disassembly has "
            f"completed, then retry.")


def _page_error(limit: int, offset: int) -> Optional[str]:
    """Validate pagination args; return an error string or None."""
    if limit < 0 or offset < 0:
        return "Invalid pagination: 'limit' and 'offset' must be non-negative."
    return None


def _paginate(items: list, offset: int, limit: int) -> dict:
    """Uniform paginated envelope shared by every list/search tool.

    STOP paging when `has_more` is false — that is the last page.
    """
    total = len(items)
    page = items[offset: offset + limit]
    return {
        "items": page,
        "offset": offset,
        "returned": len(page),
        "total": total,
        "has_more": offset + limit < total,
    }


# ── In-process ghidra_disasm cache ─────────────────────────────────────────────
# Cache ghidra_disasm in memory for repeated read-only lookups.
_GHIDRA_DISASM_CACHE: dict = {}

def _get_ghidra_disasm(oid: str) -> dict:
    cached = _GHIDRA_DISASM_CACHE.get(oid)
    if cached is None:
        cached = oxide.retrieve("ghidra_disasm", [oid]) or {}
        _GHIDRA_DISASM_CACHE[oid] = cached
    return cached


def _get_call_mapping(oid: str) -> dict:
    return _unwrap(oxide.retrieve("call_mapping", [oid]), oid) or {}


def _get_offset_to_name(oid: str) -> dict:
    """Build {offset: name} from the (in-memory cached) ghidra_disasm functions."""
    funcs = _get_ghidra_disasm(oid).get("functions", {})
    return {
        off: info.get("name", str(off))
        for off, info in funcs.items()
        if isinstance(off, int) and isinstance(info, dict)
    }


def _resolve_func_name_and_offset(oid: str, name_or_offset: str) -> tuple[Optional[str], Optional[int]]:
    """Return (func_name, offset) by resolving a name or numeric offset string.

    Numeric offsets are the common case (agents pass decompiler offsets): resolve
    the name straight from the cheap in-memory ghidra_disasm functions and skip the
    expensive function_summary computation. Only by-name lookups consult
    function_summary.
    """
    off = _to_offset(name_or_offset)
    if off is not None:
        info = _get_ghidra_disasm(oid).get("functions", {}).get(off)
        name = info.get("name", str(off)) if isinstance(info, dict) else name_or_offset
        return name, off

    summary = oxide.get_field("function_summary", [oid], oid) or {}
    if name_or_offset in summary:
        return name_or_offset, summary[name_or_offset].get("offset")
    return name_or_offset, None


def _decomp_for_function(oid: str, func_name: str) -> Optional[str]:
    """Reconstruct decompiled pseudo-C from ghidra_decmap for a named function."""
    dm = _unwrap(oxide.retrieve("ghidra_decmap", [oid], {"org_by_func": True}), oid)
    if not dm:
        return None
    functions_dict = dm.get("decompile", {}) if isinstance(dm, dict) else {}
    if func_name not in functions_dict:
        return None
    func_dict = functions_dict[func_name]

    decomp_map: dict[int, str] = {}
    for offset_val in func_dict.values():
        for line_str in offset_val.get("line", []):
            split = line_str.find(": ")
            if split == -1:
                continue
            try:
                line_no = int(line_str[:split])
            except ValueError:
                continue
            if line_no not in decomp_map:
                decomp_map[line_no] = line_str[split + 2:]

    if not decomp_map:
        return None

    out = ""
    indent = 0
    for line_no in sorted(decomp_map):
        code = str(decomp_map[line_no])
        if "}" in code:
            indent = max(0, indent - 1)
        out += ("    " * indent) + code + "\n"
        if "{" in code:
            indent += 1
    return out


def _mermaid_id(node: int, name: str) -> str:
    """Generate a safe MermaidJS node reference.

    When the name is already a valid bare identifier (the common case for
    Ghidra labels like FUN_00152210), emit it directly instead of the verbose
    `id["label"]` form — this roughly halves the text per edge endpoint.
    """
    safe = re.sub(r"[^a-zA-Z0-9_]", "_", name)
    if safe == name:
        return safe
    return f'{safe}["{name}"]'


def _nx_to_mermaid(G: nx.DiGraph, offset_to_name: dict) -> str:
    """Convert a networkx DiGraph to a MermaidJS graph TD block."""
    node_ids = {n: _mermaid_id(n, offset_to_name.get(n, str(n))) for n in G.nodes()}
    lines = ["graph TD"]
    edge_nodes: set = set()
    for u, v in G.edges():
        lines.append(f"    {node_ids[u]} --> {node_ids[v]}")
        edge_nodes.add(u)
        edge_nodes.add(v)
    for node in G.nodes():
        if node not in edge_nodes:
            lines.append(f"    {node_ids[node]}")
    return "\n".join(lines)


# ── MCP Tools ─────────────────────────────────────────────────────────────────


@mcp.tool()
async def list_binaries(collection_name: str = None) -> list[dict] | str:
    """
    List all binaries known to Oxide, optionally filtered to a named collection.

    Args:
        collection_name: Optional collection name. If omitted, returns all binaries across all collections.

    Returns:
        List of {oid, names, size, analysis_available} dicts.
    """
    if collection_name:
        cid = oxide.get_cid_from_name(collection_name)
        if not cid:
            return f"Collection '{collection_name}' not found."
        oids = oxide.expand_oids(cid)
    else:
        oids = list({oid for cid in oxide.collection_cids() for oid in oxide.expand_oids(cid)})

    results = []
    for oid in oids:
        names = sorted(oxide.get_names_from_oid(oid) or [])
        size = oxide.get_field("file_meta", oid, "size") or 0
        analysis_available = oxide.exists("ghidra_disasm", oid)
        results.append(BinaryInfo(oid=oid, names=names, size=size,
                                  analysis_available=analysis_available).model_dump())
    return sorted(results, key=lambda b: b["names"][0] if b["names"] else b["oid"])


@mcp.tool()
async def list_collections() -> list[str]:
    """
    List all collection names in Oxide.

    Returns:
        Sorted list of collection name strings.
    """
    return sorted(oxide.collection_names())


@mcp.tool()
async def get_binary_metadata(oid_or_name: str) -> dict | str:
    """
    Get metadata for a binary: architecture, bit-width, endianness, format, size, function count, section count.

    Args:
        oid_or_name: OID (40-char hex) or filename.

    Returns:
        Metadata dict: {oid, names, arch, bits, endian, format, size, num_functions, num_sections}.
    """
    oid, err = _resolve_or_error(oid_or_name)
    if err:
        return err

    names = sorted(oxide.get_names_from_oid(oid) or [])
    size = oxide.get_field("file_meta", oid, "size")

    arch = bits = endian = fmt = None
    header = oxide.get_field("object_header", oid, oid)
    if header:
        fmt = getattr(header, "type", None)
        arch = getattr(header, "machine", None)
        bits = getattr(header, "insn_mode", None)
        endian = {True: "big", False: "little"}.get(getattr(header, "big_endian", None))

    num_functions = num_sections = None
    s = _unwrap(oxide.retrieve("file_stats", [oid]), oid)
    if isinstance(s, dict):
        num_functions = s.get("Number of functions")
        num_sections = s.get("Number of sections")

    return BinaryMetadata(
        oid=oid, names=names, arch=arch, bits=bits, endian=endian,
        format=fmt, size=size, num_functions=num_functions, num_sections=num_sections
    ).model_dump()


@mcp.tool()
async def get_function_list(oid_or_name: str,
                            limit: int = 200, start: int = 0) -> dict | str:
    """
    List functions in a binary with name, offset, instruction count, and cyclomatic complexity.

    Large binaries have thousands of functions, so results are paginated. Use
    search_symbols_by_name for targeted lookup by name instead of paging this list.

    Args:
        oid_or_name: OID or filename.
        limit: Maximum functions to return (default 200).
        start: List index of the first result to return (default 0). This is NOT a byte
            address — it is a position in the sorted function list (0 = first function,
            200 = 201st function). To look up a function by byte address, call
            decompile_function(oid, address) or disassemble(oid, address) directly.

    Returns:
        {items, offset, returned, total, has_more} where `items` is the sliced list
        of {name, offset, num_insns, complexity, signature} dicts sorted by byte offset.
        The `offset` field in each item is a decimal byte address accepted as-is by
        decompile_function() and disassemble(). STOP paging when `has_more` is false.
    """
    oid, err = _resolve_or_error(oid_or_name)
    if err:
        return err
    err = _page_error(limit, start)
    if err:
        return err

    result = oxide.get_field("function_summary", [oid], oid) or {}
    if not result:
        return _no_data(oid_or_name, "function data")

    funcs = [
        FunctionInfo(
            name=name,
            offset=info.get("offset", 0),
            num_insns=info.get("num_insns"),
            complexity=info.get("complexity"),
            signature=info.get("signature"),
        ).model_dump()
        for name, info in result.items()
    ]
    funcs.sort(key=lambda f: f["offset"])
    return _paginate(funcs, start, limit)


@mcp.tool()
async def search_symbols_by_name(oid_or_name: str, query: str,
                                  limit: int = 50, offset: int = 0) -> dict | str:
    """
    Search for functions by name using a regex or substring query (case-insensitive).

    Args:
        oid_or_name: OID or filename.
        query: Regex pattern or plain substring.
        limit: Maximum results (default 50).
        offset: Pagination offset (default 0).

    Returns:
        {items, offset, returned, total, has_more} where `items` is the matching
        {name, offset} dicts sorted by name. STOP paging when `has_more` is false.
    """
    oid, err = _resolve_or_error(oid_or_name)
    if err:
        return err
    err = _page_error(limit, offset)
    if err:
        return err

    stripped_query = query.strip()

    result = oxide.get_field("function_summary", [oid], oid) or {}
    if not result:
        return _no_data(oid_or_name, "function data")

    try:
        pattern = re.compile(query, re.IGNORECASE)
    except re.error:
        pattern = re.compile(re.escape(query), re.IGNORECASE)

    matches = [
        SymbolInfo(name=name, offset=info.get("offset", 0)).model_dump()
        for name, info in result.items()
        if pattern.search(name)
    ]
    matches.sort(key=lambda s: s["name"])
    paginated = _paginate(matches, offset, limit)
    if not matches and re.fullmatch(r"0x[0-9a-fA-F]+|\d+", stripped_query):
        paginated["note"] = (
            f"Query {stripped_query!r} looks like a numeric offset; "
            "search_symbols_by_name matches function names only. "
            "Use decompile_function or disassemble with this offset directly. "
            "If those also fail, verify the offset exists with get_function_list."
        )
    return paginated


@mcp.tool()
async def get_strings(oid_or_name: str,
                      limit: int = 500, offset: int = 0) -> dict | str:
    """
    Get ASCII strings extracted from a binary with their file offsets.

    Binaries can contain thousands of strings, so results are paginated. Use
    search_strings to find specific strings by substring instead of paging all of them.

    Args:
        oid_or_name: OID or filename.
        limit: Maximum strings to return (default 500).
        offset: Pagination offset into the offset-sorted list (default 0).

    Returns:
        {items, offset, returned, total, has_more} where `items` is the sliced list
        of {value, offset} dicts sorted by offset. STOP paging when `has_more` is
        false. Prefer search_strings to find specific strings directly.
    """
    oid, err = _resolve_or_error(oid_or_name)
    if err:
        return err
    err = _page_error(limit, offset)
    if err:
        return err

    data = _unwrap(oxide.retrieve("strings", [oid]), oid)
    if not data:
        return _no_data(oid_or_name, "strings data")

    strings = sorted(
        [StringResult(value=str(v), offset=int(k)).model_dump()
         for k, v in data.items()],
        key=lambda s: s["offset"],
    )
    return _paginate(strings, offset, limit)


@mcp.tool()
async def search_strings(oid_or_name: str, query: str,
                         limit: int = 100, offset: int = 0) -> dict | str:
    """
    Search for strings in a binary that contain a given substring.

    Args:
        oid_or_name: OID or filename.
        query: Substring to search for (case-sensitive).
        limit: Maximum results (default 100).
        offset: Pagination offset into the offset-sorted matches (default 0).

    Returns:
        {items, offset, returned, total, has_more} where `items` is the matching
        {value, offset} dicts sorted by offset. STOP paging when `has_more` is false.
    """
    oid, err = _resolve_or_error(oid_or_name)
    if err:
        return err
    err = _page_error(limit, offset)
    if err:
        return err

    data = _unwrap(oxide.retrieve("strings", [oid]), oid)
    if not data:
        return _no_data(oid_or_name, "strings data")

    matches = sorted(
        [StringResult(value=str(v), offset=int(k)).model_dump()
         for k, v in data.items()
         if query in str(v)],
        key=lambda s: s["offset"],
    )
    return _paginate(matches, offset, limit)


@mcp.tool()
async def disassemble(oid_or_name: str, function_name_or_offset: str,
                      count: int = 30) -> dict | str:
    """
    Disassemble instructions starting at a function entry point (by name or offset).

    Args:
        oid_or_name: OID or filename.
        function_name_or_offset: Function name, decimal offset, or hex offset (e.g. "0x1000").
        count: Max instructions to return (default 30).

    Returns:
        {offset, count, listing} where listing is a text block of "0xADDR  mnemonic operands".
    """
    oid, err = _resolve_or_error(oid_or_name)
    if err:
        return err
    if count <= 0:
        return "Invalid 'count': must be a positive integer."

    func_name, target_offset = _resolve_func_name_and_offset(oid, function_name_or_offset)
    if target_offset is None:
        return f"Function '{function_name_or_offset}' not found in '{oid_or_name}'."

    result = _get_ghidra_disasm(oid)
    if not result:
        return _no_data(oid_or_name, "disassembly")

    blocks = result.get("original_blocks", {})
    all_insns = sorted(
        (insn_off, insn_str)
        for block_info in blocks.values()
        for insn_off, insn_str in block_info.get("members", [])
    )

    lines = []
    started = False
    for insn_off, insn_str in all_insns:
        if insn_off == target_offset:
            started = True
        if started:
            lines.append(f"0x{insn_off:08x}  {insn_str}")
            if len(lines) >= count:
                break

    if not lines:
        return (
            f"No instructions at offset 0x{target_offset:x}. The function may be "
            "missing from the cached instruction blocks; try decompile_function "
            "or verify the function offset with search_symbols_by_name."
        )

    return DisassembleResult(offset=target_offset, count=len(lines),
                             listing="\n".join(lines)).model_dump()


@mcp.tool()
async def decompile_function(oid_or_name: str, function_name_or_offset: str) -> dict | str:
    """
    Decompile a function to pseudo-C using Ghidra's cached decompilation output.

    Args:
        oid_or_name: OID or filename.
        function_name_or_offset: Function name, decimal offset, or hex offset.

    Returns:
        {name, offset, code, error} — code is None and error is set if decompilation unavailable.
    """
    oid, err = _resolve_or_error(oid_or_name)
    if err:
        return err

    func_name, target_offset = _resolve_func_name_and_offset(oid, function_name_or_offset)
    code = _decomp_for_function(oid, func_name)

    if code is None:
        disasm_funcs = _get_ghidra_disasm(oid).get("functions", {})
        if target_offset is not None and target_offset in disasm_funcs:
            error_msg = (
                f"Function '{func_name}' (offset {target_offset}) is in the disassembly "
                "but Ghidra decompilation is not cached for it. "
                "Use disassemble() to see the raw instructions instead."
            )
        else:
            error_msg = (
                f"Function not found at offset '{function_name_or_offset}' in '{oid_or_name}'. "
                "Verify the offset with get_function_list or search_symbols_by_name. "
                "Note: disassembly listings show virtual addresses in hex (e.g. 0x1234); "
                "pass the decimal function offset from get_function_list instead."
            )
        return DecompiledFunction(
            name=func_name, offset=target_offset, code=None, error=error_msg
        ).model_dump()

    return DecompiledFunction(name=func_name, offset=target_offset,
                              code=code, error=None).model_dump()


@mcp.tool()
async def get_call_graph(oid_or_name: str, function_name: str = None,
                         depth: int = 1, max_nodes: int = 200) -> dict | str:
    """
    Get the call graph for a binary as a MermaidJS diagram, centered on a function.

    PREFER THIS over many individual list_xrefs calls when tracing call chains —
    one call returns all direct callers AND callees of the target at once.

    Args:
        oid_or_name: OID or filename.
        function_name: Function name to center the graph on (strongly recommended).
        depth: How many hops out from the center to expand (default 1 = direct
            callers and callees only). Increase to 2+ only when you need a wider
            neighborhood — each extra hop grows the graph dramatically on real
            binaries and may be truncated by max_nodes.
        max_nodes: Hard cap on nodes returned (default 200). Expansion stops once
            this many nodes are reached; the result notes if it was truncated.

    Returns:
        {function_name, graph_mermaid} — graph_mermaid is a "graph TD" MermaidJS
        block showing who calls this function and what this function calls.
        Omitting function_name returns the full graph, which may be very large.
    """
    oid, err = _resolve_or_error(oid_or_name)
    if err:
        return err
    if depth <= 0:
        return "Invalid 'depth': must be a positive integer."
    if max_nodes <= 0:
        return "Invalid 'max_nodes': must be a positive integer."

    G = _unwrap(oxide.retrieve("call_graph", [oid]), oid)
    if not isinstance(G, nx.DiGraph):
        return _no_data(oid_or_name, "call graph")
    name_map: dict = {}
    truncated = False

    if function_name:
        if function_name not in G:
            return f"Function '{function_name}' not found in call graph."
        neighbors = {function_name}
        frontier = {function_name}
        for _ in range(max(1, depth)):
            if len(neighbors) >= max_nodes:
                truncated = True
                break
            nxt: set = set()
            for n in frontier:
                nxt.update(G.predecessors(n))
                nxt.update(G.successors(n))
            new = nxt - neighbors
            if len(neighbors) + len(new) > max_nodes:
                new = set(list(new)[: max_nodes - len(neighbors)])
                truncated = True
            neighbors.update(new)
            frontier = new
            if not frontier:
                break
        G = G.subgraph(neighbors)

    mermaid = _nx_to_mermaid(G, name_map)
    if truncated:
        mermaid = (f"%% NOTE: truncated to {max_nodes} nodes; increase max_nodes "
                   f"or narrow with a smaller depth\n") + mermaid

    return CallGraphResult(function_name=function_name, graph_mermaid=mermaid).model_dump()


@mcp.tool()
async def list_xrefs(oid_or_name: str, function_name_or_offset: str,
                     direction: str = "calls_to") -> dict | str:
    """
    List cross-references for a single function (one hop, one direction).

    Use get_call_graph(oid, function_name) instead when you want to see the full
    2-hop neighborhood in one call — it is much more efficient for tracing call chains.
    Use list_xrefs only when you need precise control over a single hop or direction.

    Args:
        oid_or_name: OID or filename.
        function_name_or_offset: Function name, decimal offset, or hex offset.
        direction:
            "calls_to"   — functions that CALL this function (callers / xrefs-to).
            "calls_from" — functions this function CALLS (callees).
            "both"       — both directions.

    Returns:
        {function, offset, xrefs, num_callers, num_callees, is_entry_point,
         is_leaf, note}. `xrefs` is a list of {from_function, from_offset,
         to_offset, direction} dicts. `is_entry_point` is true when the
         function has no callers and `is_leaf` is true when it has no callees,
         which mark the ends of the call graph in each direction. `note`
         summarizes the caller/callee counts.
    """
    oid, err = _resolve_or_error(oid_or_name)
    if err:
        return err
    if direction not in ("calls_to", "calls_from", "both"):
        return (f"Invalid direction '{direction}'. Use 'calls_to' (callers), "
                "'calls_from' (callees), or 'both'.")

    func_name, target_offset = _resolve_func_name_and_offset(oid, function_name_or_offset)
    if target_offset is None:
        return f"Function '{function_name_or_offset}' not found."

    mapping = _get_call_mapping(oid)
    if not mapping:
        return _no_data(oid_or_name, "call mapping")

    func_data = mapping.get(target_offset, {})
    offset_to_name = _get_offset_to_name(oid)

    xrefs = []
    if direction in ("calls_to", "both"):
        for caller_offset in func_data.get("calls_from", {}):
            xrefs.append(XrefInfo(
                from_function=offset_to_name.get(caller_offset),
                from_offset=caller_offset,
                to_offset=target_offset,
                direction="calls_to",
            ).model_dump())

    if direction in ("calls_from", "both"):
        for callee_offset in func_data.get("calls_to", {}):
            xrefs.append(XrefInfo(
                from_function=offset_to_name.get(target_offset),
                from_offset=target_offset,
                to_offset=callee_offset,
                direction="calls_from",
            ).model_dump())

    callers = func_data.get("calls_from", {})
    callees = func_data.get("calls_to", {})
    is_entry_point = len(callers) == 0
    is_leaf = len(callees) == 0

    if is_entry_point and is_leaf:
        note = "No callers and no callees — this function is isolated in the call graph."
    elif is_entry_point:
        note = "No callers — this function is a top-level entry point in the call graph."
    elif is_leaf:
        note = "No callees — this function is a leaf in the call graph."
    else:
        note = f"{len(callers)} caller(s), {len(callees)} callee(s)."

    return {
        "function": func_name,
        "offset": target_offset,
        "xrefs": xrefs,
        "num_callers": len(callers),
        "num_callees": len(callees),
        "is_entry_point": is_entry_point,
        "is_leaf": is_leaf,
        "note": note,
    }


@mcp.tool()
async def list_imports(oid_or_name: str,
                       limit: int = 500, offset: int = 0) -> dict | str:
    """
    List imported symbols (external library functions) used by a binary.

    Args:
        oid_or_name: OID or filename.
        limit: Maximum results (default 500).
        offset: Pagination offset (default 0).

    Returns:
        {items, offset, returned, total, has_more} where `items` is the
        {name, library} dicts sorted by name. An empty `items` with total 0 means
        the binary has no import table.
    """
    oid, err = _resolve_or_error(oid_or_name)
    if err:
        return err
    err = _page_error(limit, offset)
    if err:
        return err

    header = oxide.get_field("object_header", oid, oid)
    if not header:
        return _no_data(oid_or_name, "object header")

    results = []
    for lib_name, symbols in (getattr(header, "imports", None) or {}).items():
        sym_list = symbols.keys() if isinstance(symbols, dict) else ([symbols] if symbols else [])
        for sym_name in sym_list:
            if sym_name:
                results.append(ImportInfo(name=str(sym_name),
                                          library=lib_name or "unknown").model_dump())
    results.sort(key=lambda x: x["name"])
    return _paginate(results, offset, limit)


@mcp.tool()
async def list_exports(oid_or_name: str,
                       limit: int = 500, offset: int = 0) -> dict | str:
    """
    List exported/dynamic symbols from a binary (ELF dyn_symbols or PE export table).

    Args:
        oid_or_name: OID or filename.
        limit: Maximum results (default 500).
        offset: Pagination offset (default 0).

    Returns:
        {items, offset, returned, total, has_more} where `items` is the
        {name, offset} dicts sorted by name. An empty `items` with total 0 means
        the binary has no export table.
    """
    oid, err = _resolve_or_error(oid_or_name)
    if err:
        return err
    err = _page_error(limit, offset)
    if err:
        return err

    header = oxide.get_field("object_header", oid, oid)
    if not header:
        return _no_data(oid_or_name, "object header")

    symbol_sources = [("dyn_symbols", "value"), ("exports", "offset")]
    exports = []
    for attr, offset_key in symbol_sources:
        sym_dict = getattr(header, attr, None)
        if not sym_dict or not isinstance(sym_dict, dict):
            continue
        for sym_name, sym_info in sym_dict.items():
            if sym_name:
                off = sym_info.get(offset_key, 0) if isinstance(sym_info, dict) else 0
                exports.append(ExportInfo(name=sym_name, offset=off).model_dump())

    exports.sort(key=lambda x: x["name"])
    return _paginate(exports, offset, limit)


@mcp.tool()
async def read_bytes(oid_or_name: str, offset: int | str, size: int = 32) -> dict | str:
    """
    Read raw bytes from a binary at a given file offset.

    Note: Oxide stores raw file bytes. This reads at file offset, not virtual address.

    Args:
        oid_or_name: OID or filename.
        offset: File offset to read from (bytes from start of file). Decimal and 0x-prefixed hex strings are accepted. Do NOT use scientific notation (e.g. use 1510912, not 1.51e+06).
        size: Number of bytes to read (default 32, capped at 4096).

    Returns:
        {offset, size, data, error} where data is a hex string. `error` is set
        when no bytes were read at the requested file offset.
    """
    oid, err = _resolve_or_error(oid_or_name)
    if err:
        return err
    parsed_offset = _to_offset(offset)
    if parsed_offset is None:
        return (
            "Invalid offset: use a file offset as a decimal integer or 0x-prefixed "
            f"hex string, not {offset!r}."
        )
    offset = parsed_offset
    if offset < 0 or size <= 0:
        return "Invalid range: 'offset' must be non-negative and 'size' positive."

    size = min(size, 4096)
    src = oxide.source(oid)
    data = oxide.get_field(src, oid, "data")
    if not data:
        return _no_data(oid_or_name, "raw file data")

    chunk = data[offset: offset + size]
    error_msg = None
    if len(chunk) == 0:
        error_msg = (
            "No bytes read at this file offset; the offset may be past EOF "
            "or outside available raw file data."
        )
    return BytesReadResult(
        offset=offset,
        size=len(chunk),
        data=chunk.hex(),
        error=error_msg,
    ).model_dump()


@mcp.tool()
async def get_control_flow_graph(oid_or_name: str, function_name_or_offset: str) -> dict | str:
    """
    Get the Control Flow Graph (CFG) for a specific function.

    Args:
        oid_or_name: OID or filename.
        function_name_or_offset: Function name, decimal offset, or hex offset.

    Returns:
        CFG dict: {name, nodes: {block_offset: {insn_offset: insn_str}}, edges: {src: [dsts]}}.
    """
    oid, err = _resolve_or_error(oid_or_name)
    if err:
        return err

    func_name, target_offset = _resolve_func_name_and_offset(oid, function_name_or_offset)

    cfgs = _unwrap(oxide.retrieve("mcp_control_flow_graph", [oid]), oid)
    if not cfgs:
        return _no_data(oid_or_name, "control flow graph")

    if target_offset is not None and target_offset in cfgs:
        return cfgs[target_offset]

    for cfg_data in cfgs.values():
        if cfg_data.get("name") == func_name:
            return cfg_data

    return f"Function '{function_name_or_offset}' not found in CFG data."


@mcp.tool()
async def search_functions(
    query: str,
    oid_or_name: str = "",
    collection_name: str = "",
    limit: int = 5,
    offset: int = 0,
    search_mode: str = "semantic",
    include_full_code: bool = True,
    preview_length: int = 500,
    similarity_threshold: float = 0.0,
) -> dict | str:
    """
    Search decompiled functions across one binary, one collection, or all binaries.

    Mirrors the `pyghidra-mcp` `search_code` tool shape, but scopes across Oxide
    binaries instead of a single open program.

    Args:
        query: Natural-language description or literal snippet to search for.
        oid_or_name: Optional — scope search to one binary (OID or filename).
        collection_name: Optional — scope search to a named collection.
        limit: Number of results to return (default 5).
        offset: Pagination offset (default 0).
        search_mode: "semantic" (embedding) or "literal" (substring).
        include_full_code: Include full decompiled code in each result.
        preview_length: Preview size when `include_full_code` is false.
        similarity_threshold: Minimum similarity score 0.0–1.0 (default 0.0).

    Returns:
        A paginated dict matching the `pyghidra-mcp` `search_code` result shape,
        with Oxide-specific `oid` and `offset` fields per result.
    """
    if limit <= 0:
        return "Invalid 'limit': must be a positive integer."
    if offset < 0:
        return "Invalid 'offset': must be a non-negative integer."
    if search_mode not in {"semantic", "literal"}:
        return "Invalid 'search_mode': use 'semantic' or 'literal'."
    if preview_length < 0:
        return "Invalid 'preview_length': must be non-negative."
    if similarity_threshold < 0.0 or similarity_threshold > 1.0:
        return "Invalid 'similarity_threshold': must be between 0.0 and 1.0."

    if oid_or_name:
        oid, err = _resolve_or_error(oid_or_name)
        if err:
            return err
        scope_oids = [oid]
    elif collection_name:
        cid = oxide.get_cid_from_name(collection_name)
        if not cid:
            return f"Collection '{collection_name}' not found."
        scope_oids = list(oxide.expand_oids(cid))
        if not scope_oids:
            return f"Collection '{collection_name}' is empty."
    else:
        scope_oids = list({oid for cid in oxide.collection_cids()
                           for oid in oxide.expand_oids(cid)})
        if not scope_oids:
            return "No binaries found in Oxide."

    result = oxide.retrieve("query_function", scope_oids, {
        "query": query,
        "limit": limit,
        "offset": offset,
        "search_mode": search_mode,
        "include_full_code": include_full_code,
        "preview_length": preview_length,
        "similarity_threshold": similarity_threshold,
    })

    if not result:
        return "No results. query_function analysis may not have run for these binaries."

    candidates = result.get("results", {}).get("candidates", [])
    out = []
    for c in candidates:
        func_offset = (
            _to_offset(c.get("function_addr"))
            or _to_offset(c.get("func_addr"))
            or 0
        )
        out.append(FunctionSearchResult(
            oid=c.get("oid") or "",
            function_name=c.get("function_name") or c.get("func_name") or "",
            offset=func_offset,
            code=c.get("code") or "",
            similarity=float(c.get("similarity", c.get("score", 0.0))),
            search_mode=c.get("search_mode") or c.get("match_type") or search_mode,
            preview=c.get("preview"),
        ))

    return FunctionSearchResults(
        results=out,
        query=result.get("query", query),
        search_mode=result.get("search_mode", search_mode),
        returned_count=int(result.get("returned_count", len(out))),
        offset=int(result.get("offset", offset)),
        limit=int(result.get("limit", limit)),
        literal_total=int(result.get("literal_total", 0)),
        semantic_total=int(result.get("semantic_total", 0)),
        total_functions=int(result.get("total_functions", 0)),
    ).model_dump()


# ── Entry point ───────────────────────────────────────────────────────────────

if __name__ == "__main__":
    mcp.run(transport=args.transport)
