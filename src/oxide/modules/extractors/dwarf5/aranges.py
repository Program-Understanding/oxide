"""Minimal parser for .debug_aranges"""

import stream


def _read_initial_length(r: stream.BinaryReader) -> tuple[bool, int, int]:
    unit_start = r.tell()
    initial = r.read_u32()
    if initial == 0xFFFFFFFF:
        return True, r.read_u64(), unit_start
    return False, initial, unit_start


def parse_aranges(section_data: bytes) -> dict:
    if not section_data:
        return {"units": []}

    r = stream.BinaryReader(section_data)
    units = []

    while r.tell() < len(section_data):
        start = r.tell()
        if start + 4 > len(section_data):
            break

        is_64, unit_length, unit_start = _read_initial_length(r)
        if unit_length == 0:
            continue

        length_field_size = 12 if is_64 else 4
        unit_end = unit_start + length_field_size + unit_length
        if unit_end > len(section_data):
            break

        version = r.read_u16()
        debug_info_offset = r.read_u64() if is_64 else r.read_u32()
        address_size = r.read_u8()
        segment_size = r.read_u8()

        tuple_size = segment_size + (2 * address_size)
        while tuple_size and ((r.tell() - unit_start) % tuple_size) != 0 and r.tell() < unit_end:
            r.read_u8()

        entries = []
        while r.tell() + tuple_size <= unit_end and tuple_size:
            if segment_size:
                seg = int.from_bytes(r.read_bytes(segment_size), "little")
            else:
                seg = None
            addr = int.from_bytes(r.read_bytes(address_size), "little")
            length = int.from_bytes(r.read_bytes(address_size), "little")

            if (seg in (None, 0)) and addr == 0 and length == 0:
                break

            entries.append({"segment": seg, "address": addr, "length": length})

        r.seek(unit_end)
        units.append(
            {
                "offset": unit_start,
                "version": version,
                "is_64bit": is_64,
                "debug_info_offset": debug_info_offset,
                "address_size": address_size,
                "segment_size": segment_size,
                "entries": entries,
            }
        )

    return {"units": units}
