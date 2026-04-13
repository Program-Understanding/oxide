"""Minimal parser for .debug_line (header-focused)."""

import stream


def _safe_u8(r: stream.BinaryReader, limit: int) -> int | None:
    if r.tell() + 1 > limit:
        return None
    return r.read_u8()


def _safe_u16(r: stream.BinaryReader, limit: int) -> int | None:
    if r.tell() + 2 > limit:
        return None
    return r.read_u16()


def _safe_u32(r: stream.BinaryReader, limit: int) -> int | None:
    if r.tell() + 4 > limit:
        return None
    return r.read_u32()


def _safe_u64(r: stream.BinaryReader, limit: int) -> int | None:
    if r.tell() + 8 > limit:
        return None
    return r.read_u64()


def parse_line(section_data: bytes) -> dict:
    if not section_data:
        return {"units": []}

    r = stream.BinaryReader(section_data)
    units = []

    while r.tell() + 4 <= len(section_data):
        unit_start = r.tell()
        initial = _safe_u32(r, len(section_data))
        if initial is None:
            break
        is_64 = initial == 0xFFFFFFFF
        unit_length = _safe_u64(r, len(section_data)) if is_64 else initial
        if unit_length is None:
            units.append({"offset": unit_start, "status": "partial", "error": "truncated initial length"})
            break
        if unit_length == 0:
            continue

        length_field_size = 12 if is_64 else 4
        unit_end = unit_start + length_field_size + unit_length
        if unit_end > len(section_data):
            break

        version = _safe_u16(r, unit_end)
        if version is None:
            units.append({"offset": unit_start, "status": "partial", "error": "truncated version"})
            r.seek(unit_end)
            continue

        # DWARF5 spec §6.2.4: address_size + segment_selector_size come BEFORE
        # header_length in v5; v2–v4 have header_length immediately after version.
        address_size: int | None = None
        segment_selector_size: int | None = None

        if version >= 5:
            address_size = _safe_u8(r, unit_end)
            segment_selector_size = _safe_u8(r, unit_end)
            if address_size is None or segment_selector_size is None:
                units.append({"offset": unit_start, "version": version,
                               "status": "partial",
                               "error": "truncated v5 address_size/segment_selector_size"})
                r.seek(unit_end)
                continue

        header_length = _safe_u64(r, unit_end) if is_64 else _safe_u32(r, unit_end)
        if header_length is None:
            units.append({"offset": unit_start, "version": version,
                           "status": "partial", "error": "truncated header_length"})
            r.seek(unit_end)
            continue
        header_start = r.tell()

        # Read fixed header fields (order differs between v5 and v2–v4)
        if version >= 5:
            min_instruction_length = _safe_u8(r, unit_end)
            max_ops_per_instruction = _safe_u8(r, unit_end)
            default_is_stmt_raw = _safe_u8(r, unit_end)
            line_base_raw = _safe_u8(r, unit_end)
            line_range = _safe_u8(r, unit_end)
            opcode_base = _safe_u8(r, unit_end)
            if None in (min_instruction_length, max_ops_per_instruction,
                        default_is_stmt_raw, line_base_raw, line_range, opcode_base):
                units.append({"offset": unit_start, "version": version,
                               "status": "partial", "error": "truncated v5 header fields"})
                r.seek(unit_end)
                continue
        else:
            min_instruction_length = _safe_u8(r, unit_end)
            max_ops_per_instruction = 1
            default_is_stmt_raw = _safe_u8(r, unit_end)
            line_base_raw = _safe_u8(r, unit_end)
            line_range = _safe_u8(r, unit_end)
            opcode_base = _safe_u8(r, unit_end)
            if None in (min_instruction_length, default_is_stmt_raw,
                        line_base_raw, line_range, opcode_base):
                units.append({"offset": unit_start, "version": version,
                               "status": "partial", "error": "truncated v2-v4 header fields"})
                r.seek(unit_end)
                continue

        # Safe unwrap (None cases already caught above)
        assert min_instruction_length is not None
        assert max_ops_per_instruction is not None
        assert default_is_stmt_raw is not None
        assert line_base_raw is not None
        assert line_range is not None
        assert opcode_base is not None

        line_base = int.from_bytes(bytes([line_base_raw]), "little", signed=True)

        std_opcode_lengths = []
        for _ in range(max(opcode_base - 1, 0)):
            op_len = _safe_u8(r, unit_end)
            if op_len is None:
                units.append({"offset": unit_start, "version": version,
                               "status": "partial",
                               "error": "truncated standard opcode lengths"})
                r.seek(unit_end)
                break
            std_opcode_lengths.append(op_len)
        else:
            # Skip remaining header body conservatively
            target = min(header_start + header_length, unit_end)
            r.seek(target)

            unit_obj: dict = {
                "offset": unit_start,
                "is_64bit": is_64,
                "version": version,
                "header_length": header_length,
                "min_instruction_length": min_instruction_length,
                "max_ops_per_instruction": max_ops_per_instruction,
                "default_is_stmt": bool(default_is_stmt_raw),
                "line_base": line_base,
                "line_range": line_range,
                "opcode_base": opcode_base,
                "standard_opcode_lengths": std_opcode_lengths,
            }
            if version >= 5:
                unit_obj["address_size"] = address_size
                unit_obj["segment_selector_size"] = segment_selector_size
            units.append(unit_obj)

        r.seek(unit_end)

    return {"units": units}
