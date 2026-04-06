"""Parser for .debug_addr (DWARF5)."""

from . import stream


def parse_debug_addr(section_data: bytes, address_size: int) -> list[int]:
    if not section_data:
        return []
    r = stream.BinaryReader(section_data)
    out = []
    step = 8 if address_size == 8 else 4
    while r.tell() + step <= len(section_data):
        out.append(r.read_u64() if step == 8 else r.read_u32())
    return out
