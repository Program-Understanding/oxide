"""DWARF form decoding logic (v4 + v5 core forms)."""

import constants
import stream
import str_offsets as str_offsets_mod


def _read_offset(reader, dwarf64):
    return reader.read_u64() if dwarf64 else reader.read_u32()


def _resolve_strp(offset: int, debug_sections: dict) -> str:
    """Resolve a byte offset into .debug_str → string."""
    str_data = debug_sections.get(".debug_str", {}).get("data", b"")
    if str_data and offset < len(str_data):
        end = str_data.index(b"\x00", offset) if b"\x00" in str_data[offset:] else len(str_data)
        return str_data[offset:end].decode("utf-8", errors="replace")
    return f"<strp:{offset:#x}>"


def _resolve_line_strp(offset: int, debug_sections: dict) -> str:
    """Resolve a byte offset into .debug_line_str → string."""
    line_str_data = debug_sections.get(".debug_line_str", {}).get("data", b"")
    if line_str_data and offset < len(line_str_data):
        end = (line_str_data.index(b"\x00", offset)
               if b"\x00" in line_str_data[offset:] else len(line_str_data))
        return line_str_data[offset:end].decode("utf-8", errors="replace")
    return f"<line_strp:{offset:#x}>"


def _resolve_strx(index: int, debug_sections: dict, unit_bases: dict, dwarf64: bool) -> str:
    """Resolve a STRX index through .debug_str_offsets → .debug_str."""
    offsets_data = debug_sections.get(".debug_str_offsets", {}).get("data", b"")
    if not offsets_data:
        return f"<strx:{index}>"
    base = unit_bases.get("str_offsets_base", 0)
    str_offset = str_offsets_mod.lookup_str_offset(offsets_data, base, index, dwarf64)
    if str_offset is None:
        return f"<strx:{index}>"
    return _resolve_strp(str_offset, debug_sections)


def decode_form(
    form,
    reader,
    *,
    dwarf64,
    address_size,
    debug_sections,
    unit_bases,
    implicit_const=None,
):
    if form == int(constants.DwarfForm.IMPLICIT_CONST):
        return implicit_const

    if form == int(constants.DwarfForm.INDIRECT):
        form = reader.read_uleb128()
        return decode_form(
            form, reader,
            dwarf64=dwarf64, address_size=address_size,
            debug_sections=debug_sections, unit_bases=unit_bases,
        )

    if form == int(constants.DwarfForm.ADDR):
        return reader.read_u64() if address_size == 8 else reader.read_u32()

    if form == int(constants.DwarfForm.DATA1):
        return reader.read_u8()
    if form == int(constants.DwarfForm.DATA2):
        return reader.read_u16()
    if form == int(constants.DwarfForm.DATA4):
        return reader.read_u32()
    if form == int(constants.DwarfForm.DATA8):
        return reader.read_u64()
    if form == int(constants.DwarfForm.DATA16):
        return reader.read_bytes(16)
    if form == int(constants.DwarfForm.UDATA):
        return reader.read_uleb128()
    if form == int(constants.DwarfForm.SDATA):
        return reader.read_sleb128()
    if form == int(constants.DwarfForm.FLAG):
        return bool(reader.read_u8())
    if form == int(constants.DwarfForm.FLAG_PRESENT):
        return True

    if form == int(constants.DwarfForm.STRING):
        return reader.read_cstring()

    # Direct offset into .debug_str
    if form in (int(constants.DwarfForm.STRP), int(constants.DwarfForm.STRP_SUP)):
        offset = _read_offset(reader, dwarf64)
        return _resolve_strp(offset, debug_sections)

    # Direct offset into .debug_line_str (DWARF5)
    if form == int(constants.DwarfForm.LINE_STRP):
        offset = _read_offset(reader, dwarf64)
        return _resolve_line_strp(offset, debug_sections)

    # Indexed forms: look up via .debug_str_offsets then .debug_str
    if form == int(constants.DwarfForm.STRX):
        index = reader.read_uleb128()
        return _resolve_strx(index, debug_sections, unit_bases, dwarf64)
    if form == int(constants.DwarfForm.STRX1):
        return _resolve_strx(reader.read_u8(), debug_sections, unit_bases, dwarf64)
    if form == int(constants.DwarfForm.STRX2):
        return _resolve_strx(reader.read_u16(), debug_sections, unit_bases, dwarf64)
    if form == int(constants.DwarfForm.STRX3):
        b = reader.read_bytes(3)
        return _resolve_strx(b[0] | (b[1] << 8) | (b[2] << 16), debug_sections, unit_bases, dwarf64)
    if form == int(constants.DwarfForm.STRX4):
        return _resolve_strx(reader.read_u32(), debug_sections, unit_bases, dwarf64)

    # Indexed address forms (return raw index for now; caller can resolve via .debug_addr)
    if form == int(constants.DwarfForm.ADDRX):
        return reader.read_uleb128()
    if form == int(constants.DwarfForm.ADDRX1):
        return reader.read_u8()
    if form == int(constants.DwarfForm.ADDRX2):
        return reader.read_u16()
    if form == int(constants.DwarfForm.ADDRX3):
        b = reader.read_bytes(3)
        return b[0] | (b[1] << 8) | (b[2] << 16)
    if form == int(constants.DwarfForm.ADDRX4):
        return reader.read_u32()

    if form in (
        int(constants.DwarfForm.SEC_OFFSET),
        int(constants.DwarfForm.REF_ADDR),
        int(constants.DwarfForm.REF_SUP4),
        int(constants.DwarfForm.REF_SUP8),
    ):
        if form == int(constants.DwarfForm.REF_SUP4):
            return reader.read_u32()
        if form == int(constants.DwarfForm.REF_SUP8):
            return reader.read_u64()
        return _read_offset(reader, dwarf64)

    if form == int(constants.DwarfForm.REF1):
        return reader.read_u8()
    if form == int(constants.DwarfForm.REF2):
        return reader.read_u16()
    if form == int(constants.DwarfForm.REF4):
        return reader.read_u32()
    if form in (int(constants.DwarfForm.REF8), int(constants.DwarfForm.REF_SIG8)):
        return reader.read_u64()
    if form == int(constants.DwarfForm.REF_UDATA):
        return reader.read_uleb128()

    if form == int(constants.DwarfForm.BLOCK1):
        return reader.read_bytes(reader.read_u8())
    if form == int(constants.DwarfForm.BLOCK2):
        return reader.read_bytes(reader.read_u16())
    if form == int(constants.DwarfForm.BLOCK4):
        return reader.read_bytes(reader.read_u32())
    if form in (int(constants.DwarfForm.BLOCK), int(constants.DwarfForm.EXPRLOC)):
        return reader.read_bytes(reader.read_uleb128())

    if form in (int(constants.DwarfForm.LOCLISTX), int(constants.DwarfForm.RNGLISTX)):
        return reader.read_uleb128()

    return {"unsupported_form": form}
