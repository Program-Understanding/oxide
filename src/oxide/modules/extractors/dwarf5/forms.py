"""DWARF form decoding logic (v4 + v5 core forms)."""

import constants
import stream


def _read_offset(reader, dwarf64):
    return reader.read_u64() if dwarf64 else reader.read_u32()


def _resolve_strp(offset, debug_sections):
    """Resolve a .debug_str offset to the actual string."""
    # Try .debug_str first (DWARF4 and DWARF5 .debug_str section)
    str_data = debug_sections.get(".debug_str", {}).get("data", b"")
    if str_data and offset < len(str_data):
        end = offset
        while end < len(str_data) and str_data[end] != 0:
            end += 1
        return str_data[offset:end].decode("utf-8", errors="replace")

    # Fallback: try .debug_line_str (DWARF5)
    line_str_data = debug_sections.get(".debug_line_str", {}).get("data", b"")
    if line_str_data and offset < len(line_str_data):
        end = offset
        while end < len(line_str_data) and line_str_data[end] != 0:
            end += 1
        return line_str_data[offset:end].decode("utf-8", errors="replace")

    return f"<strp:{offset}>"


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
            form,
            reader,
            dwarf64=dwarf64,
            address_size=address_size,
            debug_sections=debug_sections,
            unit_bases=unit_bases,
            implicit_const=None,
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

    # String pointer: offset into .debug_str → resolve to actual string
    if form in (int(constants.DwarfForm.STRP), int(constants.DwarfForm.STRP_SUP)):
        offset = _read_offset(reader, dwarf64)
        return _resolve_strp(offset, debug_sections)
    if form == int(constants.DwarfForm.LINE_STRP):
        offset = _read_offset(reader, dwarf64)
        return _resolve_strp(offset, debug_sections)

    if form == int(constants.DwarfForm.STRX):
        return reader.read_uleb128()
    if form == int(constants.DwarfForm.STRX1):
        return reader.read_u8()
    if form == int(constants.DwarfForm.STRX2):
        return reader.read_u16()
    if form == int(constants.DwarfForm.STRX3):
        b = reader.read_bytes(3)
        return b[0] | (b[1] << 8) | (b[2] << 16)
    if form == int(constants.DwarfForm.STRX4):
        return reader.read_u32()

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
        n = reader.read_u8()
        return reader.read_bytes(n)
    if form == int(constants.DwarfForm.BLOCK2):
        n = reader.read_u16()
        return reader.read_bytes(n)
    if form == int(constants.DwarfForm.BLOCK4):
        n = reader.read_u32()
        return reader.read_bytes(n)
    if form in (int(constants.DwarfForm.BLOCK), int(constants.DwarfForm.EXPRLOC)):
        n = reader.read_uleb128()
        return reader.read_bytes(n)

    if form in (int(constants.DwarfForm.LOCLISTX), int(constants.DwarfForm.RNGLISTX)):
        return reader.read_uleb128()

    return {"unsupported_form": form}
