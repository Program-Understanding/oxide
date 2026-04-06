"""Parser for .debug_str_offsets (DWARF5)."""

import stream


def parse_str_offsets(section_data: bytes, dwarf64: bool) -> list[int]:
    if not section_data:
        return []
    r = stream.BinaryReader(section_data)
    out = []
    step = 8 if dwarf64 else 4
    while r.tell() + step <= len(section_data):
        out.append(r.read_u64() if dwarf64 else r.read_u32())
    return out
