"""Parser/helpers for .debug_str_offsets (DWARF5 §7.26)."""

import stream


def parse_str_offsets(section_data: bytes, dwarf64: bool) -> list[int]:
    """Return the list of string offsets, skipping any DWARF5 unit header."""
    if not section_data:
        return []
    r = stream.BinaryReader(section_data)
    # DWARF5 §7.26: section may start with a unit header
    # (unit_length, version u16, padding u16).  Detect by checking version field.
    # The header exists only when the section uses the new format (DWARF5).
    # We peek: if bytes [4..6] (or [12..14] for 64-bit) look like version==5, skip header.
    data_start = 0
    if len(section_data) >= 8:
        initial = int.from_bytes(section_data[0:4], "little")
        is_64 = initial == 0xFFFFFFFF
        if is_64 and len(section_data) >= 16:
            ver = int.from_bytes(section_data[12:14], "little")
            if ver >= 5:
                data_start = 16  # 4(0xff marker)+8(length)+2(version)+2(padding)
        elif not is_64:
            ver = int.from_bytes(section_data[4:6], "little")
            if ver >= 5:
                data_start = 8   # 4(length)+2(version)+2(padding)

    step = 8 if dwarf64 else 4
    r.seek(data_start)
    out = []
    while r.tell() + step <= len(section_data):
        out.append(r.read_u64() if dwarf64 else r.read_u32())
    return out


def lookup_str_offset(section_data: bytes, base: int, index: int, dwarf64: bool) -> int | None:
    """Given str_offsets_base (byte offset into section) and a STRX index,
    return the corresponding .debug_str byte offset, or None if out of bounds."""
    step = 8 if dwarf64 else 4
    pos = base + index * step
    if pos + step > len(section_data):
        return None
    chunk = section_data[pos: pos + step]
    return int.from_bytes(chunk, "little")
