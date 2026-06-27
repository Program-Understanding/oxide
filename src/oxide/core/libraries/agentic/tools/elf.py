"""ELF/format + raw-byte tools (group: elf). Thin exposures of the `elf` module + stored bytes."""
from __future__ import annotations

import struct

from .registry import tool
from .context import addr_list, _VAL_FMT


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


@tool(group="elf", params={})
def open_binary(ctx) -> dict:
    """Open/analyze the binary; returns oid (sha1), detected format, arch."""
    return info(ctx)


@tool(group="elf", params={"file_offset": {"type": "string"}}, required=["file_offset"],
      desc="Convert a FILE OFFSET (or many, comma-separated) to the VIRTUAL ADDRESS other tools "
           "use. Deterministic (ELF section table); converts a whole set in one call.")
def file_offset_to_vaddr(ctx, file_offset: str):
    out = [{"file_offset": hex(o), "vaddr": (hex(v) if (v := ctx.off_to_vaddr(o)) is not None else None)}
           for o in addr_list(file_offset)]
    return out[0] if len(out) == 1 else out


@tool(group="elf", params={"vaddr": {"type": "string"}}, required=["vaddr"],
      desc="Convert a VIRTUAL ADDRESS (or many, comma-separated) to its FILE OFFSET (what SUNS "
           "answers want). Deterministic; pass the whole target set at once.")
def vaddr_to_file_offset(ctx, vaddr: str):
    out = [{"vaddr": hex(v), "file_offset": (hex(o) if (o := ctx.vaddr_to_off(v)) is not None else None)}
           for v in addr_list(vaddr)]
    return out[0] if len(out) == 1 else out


@tool(group="elf", params={"min_len": {"type": "integer"}, "limit": {"type": "integer"}},
      desc="List printable strings (virtual address + value).")
def strings(ctx, min_len: int = 5, limit: int = 300) -> list:
    r = ctx.retrieve_oid("strings") or {}
    out = []
    for off, s in r.items():
        if not isinstance(s, str) or len(s) < min_len:
            continue
        va = ctx.off_to_vaddr(int(off))
        out.append({"addr": hex(va) if va is not None else str(off), "string": s})
        if len(out) >= limit:
            break
    return out


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


@tool(group="elf", params={}, desc="Exported (DEFINED) symbols: name + address.")
def exports(ctx) -> list:
    out = []
    for nm, info in (ctx._elf().get("dyn_symbols", {}) or {}).items():
        if not isinstance(info, dict) or _is_undefined(info):   # skip imports (undefined symbols)
            continue
        out.append({"name": nm, "addr": hex(info.get("value", 0))})
    return out


@tool(group="elf", params={"hex_pattern": {"type": "string"}}, required=["hex_pattern"],
      desc="Search the binary for a hex byte pattern; returns matching virtual addresses.")
def search_bytes(ctx, hex_pattern: str) -> list:
    try:
        pat = bytes.fromhex(hex_pattern.replace(" ", ""))
    except ValueError:
        return []
    data, out, i = ctx._data(), [], 0
    while True:
        j = data.find(pat, i)
        if j < 0:
            break
        va = ctx.off_to_vaddr(j)
        out.append(hex(va) if va is not None else hex(j))
        i = j + 1
        if len(out) >= 256:
            break
    return out


# x86-64 dynamic relocation type names (ELF format knowledge — like decoding section types; not
# analysis logic). 37 = R_X86_64_IRELATIVE (an IFUNC resolver invoked at load/relocation time).
_RELOC_X86_64 = {0: "NONE", 1: "64", 2: "PC32", 5: "COPY", 6: "GLOB_DAT", 7: "JUMP_SLOT",
                 8: "RELATIVE", 9: "GOTPCREL", 16: "DTPMOD64", 17: "DTPOFF64", 18: "TPOFF64",
                 23: "TPOFF32", 24: "PC64", 37: "IRELATIVE", 41: "GOTPCRELX", 42: "REX_GOTPCRELX"}


def _elf_to_agent(ctx, elf_va):
    """ELF link-time vaddr -> the agent's (Ghidra-rebased) vaddr, via the file offset."""
    try:
        o = ctx._elf_vaddr_to_off(int(elf_va))
        return ctx.off_to_vaddr(o) if o is not None else None
    except Exception:  # noqa: BLE001
        return None


@tool(group="elf", params={}, desc="List sections/segments (name, virtual address, file offset, "
      "size) for ELF/PE/Mach-O — like readelf -S / the PE section table.")
def sections(ctx) -> list:
    out = []
    for name, s in (ctx._elf().get("section_table", {}) or {}).items():
        if isinstance(s, dict):
            raw = s.get("addr", 0) or 0
            # Rebase the section vaddr into the UNIFIED Ghidra vaddr space so it is consistent
            # with function/instruction addresses. Otherwise a verifier comparing a function at
            # e.g. 0x1045fb against a raw .text addr of 0x26c0 wrongly concludes "addr invalid".
            va = _elf_to_agent(ctx, raw) if raw else None
            out.append({"name": name, "type": s.get("type"), "flags": s.get("flags"),
                        "addr": hex(va if va is not None else raw), "file_offset": s.get("offset"),
                        "size": s.get("size"), "entsize": s.get("entsize")})
    return out


@tool(group="elf", params={"limit": {"type": "integer"}},
      desc="Decoded dynamic relocations — per entry: section, offset, relocation type, symbol index, "
           "addend, and the resolved target function (where the addend points). Plus a per-type "
           "count. Thin exposure of the ELF .rela.* tables (like readelf -r).")
def relocations(ctx, limit: int = 256) -> dict:
    relsecs = ctx._elf().get("relocations", {}) or {}
    vbn, _, _ = ctx._name_maps()
    name_by_va = {v: n for n, v in vbn.items()}
    by_type, entries = {}, []
    for sname, sec in relsecs.items():
        if not isinstance(sec, dict):
            continue
        data = sec.get("data") or b""
        ent = sec.get("entsize") or 24
        if ent < 24 or not data:
            continue
        for i in range(0, len(data) - 23, ent):
            r_off, r_info, r_add = struct.unpack_from("<QQq", data, i)
            tn = _RELOC_X86_64.get(r_info & 0xffffffff, str(r_info & 0xffffffff))
            by_type[tn] = by_type.get(tn, 0) + 1
            if len(entries) >= limit:
                continue
            agent_off = _elf_to_agent(ctx, r_off)
            agent_tgt = _elf_to_agent(ctx, r_add)
            entries.append({"section": sname,
                            "offset": hex(agent_off) if agent_off is not None else hex(r_off),
                            "type": tn, "sym": r_info >> 32, "addend": hex(r_add),
                            "target": hex(agent_tgt) if agent_tgt is not None else None,
                            "target_fn": name_by_va.get(agent_tgt)})
    return {"by_type": by_type, "total": sum(by_type.values()), "entries": entries}


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
