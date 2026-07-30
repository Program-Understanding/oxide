"""ELF/format + raw-byte tools (group: elf). Thin exposures of the `elf` module + stored bytes.

Only three tools remain, each with a live caller:
  * `read_values`  -- published via MCP and in the type_worker's roster (lookup/jump/index tables)
  * `imports`      -- called in-process by `mcp_agentic._fn_facts` for the repeat-breaker hint
  * `info`         -- called by the opt-in runtime probe (`extras/runtime_probe`)

Eight tools were removed as dead code (2026-07-29): `open_binary`, `file_offset_to_vaddr`,
`vaddr_to_file_offset`, `strings`, `exports`, `search_bytes`, `sections`, `relocations`. None was
published via MCP, in any agent roster, or invoked internally -- four of them
(`file_offset_to_vaddr`, `vaddr_to_file_offset`, `imports`, `search_bytes`) had been MCP tools in the
original design and were orphaned when the server's published set shrank. Removing them cannot change
agent behaviour: the model was never offered them, so its tool list is byte-identical either way.
"""
from __future__ import annotations

import struct

from .registry import tool
from .context import _VAL_FMT


@tool(group="elf", params={})
def info(ctx) -> dict:
    """Binary identity: format (elf), arch, bits, endianness, PIE/stripped."""
    fmt = ctx.fmt()
    if fmt == "elf":
        h = ctx._elf().get("elf_header", {})
        return {"format": "elf", "oid": ctx.oid, "arch": h.get("machine"), "class": h.get("class"),
                "bits": h.get("class"), "endian": h.get("data"), "type": h.get("type"),
                "pie": str(h.get("type", "")).lower().startswith("shared")}
    return {"format": fmt, "oid": ctx.oid}


def _is_undefined(info) -> bool:
    """A dynamic symbol is an IMPORT iff it is UNDEFINED (section index 0 / no defining address)."""
    return isinstance(info, dict) and info.get("shndx") in (0, "UND", "UNDEF", "SHN_UNDEF")


@tool(group="elf", params={}, desc="Imported/linked symbols (compact name list) — evidence of "
                                   "capability (e.g. socket/connect/execl/system/dup2).")
def imports(ctx) -> dict:
    elf = ctx._elf()
    names = set()
    for _lib, funcs in (elf.get("imports", {}) or {}).items():
        names.update(funcs or {})
    names.update(elf.get("dyn_imports", {}) or {})
    for nm, info in (elf.get("dyn_symbols", {}) or {}).items():
        if nm and _is_undefined(info):
            names.add(nm)
    names.discard("Unknown")
    names.discard("")
    return {"count": len(names), "imports": sorted(names)}


@tool(group="elf", params={"addr": {"type": "string"}, "type": {"type": "string"},
                           "count": {"type": "integer"}, "signed": {"type": "boolean"},
                           "endian": {"type": "string"}}, required=["addr"],
      desc="Read a memory region as a STRUCTURED array of typed integers "
           "(int8/int16/int32/int64, little/big endian) — for lookup/jump/index tables.")
def read_values(ctx, addr: str, type: str = "int32", count: int = 16,
                signed: bool = True, endian: str = "little") -> dict:
    t = str(type).lower().replace("_t", "").replace("uint", "int")
    fmt1 = _VAL_FMT.get((t, bool(signed)))
    if fmt1 is None:
        return {"error": f"unknown type '{type}' (use int8/int16/int32/int64)"}
    width = struct.calcsize(fmt1)
    n = max(1, min(int(count), 1024))
    raw = ctx.read_at_vaddr(addr, n * width)
    if not raw:
        return {"error": "could not read bytes at addr"}
    raw = raw[:(len(raw) // width) * width]
    e = "<" if str(endian).lower().startswith("l") else ">"
    vals = list(struct.unpack(f"{e}{len(raw)//width}{fmt1}", raw))
    ascii_low = "".join(chr(v & 0xFF) if 32 <= (v & 0xFF) < 127 else "." for v in vals)
    return {"addr": addr, "type": t, "signed": bool(signed), "endian": endian,
            "count": len(vals), "values": vals[:1024], "ascii_low_bytes": ascii_low[:1024]}
