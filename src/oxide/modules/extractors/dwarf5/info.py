"""Parsers for .debug_info and CU headers (DWARF4/5)."""

import abbrev
import forms
import models
import stream


def _parse_unit_header(reader: stream.BinaryReader) -> models.UnitHeader:
    unit_offset = reader.tell()
    initial_length = reader.read_u32()
    is_64bit = initial_length == 0xFFFFFFFF
    unit_length = reader.read_u64() if is_64bit else initial_length

    length_field_size = 12 if is_64bit else 4
    unit_end = unit_offset + length_field_size + unit_length

    version = reader.read_u16()
    unit_type = None
    extras = {}

    if version >= 5:
        unit_type = reader.read_u8()
        address_size = reader.read_u8()
        abbrev_offset = reader.read_u64() if is_64bit else reader.read_u32()
        if unit_type in (0x02, 0x06):
            extras["type_signature"] = reader.read_u64()
            extras["type_offset"] = reader.read_u64() if is_64bit else reader.read_u32()
        elif unit_type in (0x04, 0x05):
            extras["dwo_id"] = reader.read_u64()
    else:
        abbrev_offset = reader.read_u64() if is_64bit else reader.read_u32()
        address_size = reader.read_u8()

    return models.UnitHeader(
        unit_offset=unit_offset,
        is_64bit=is_64bit,
        unit_length=unit_length,
        version=version,
        unit_type=unit_type,
        address_size=address_size,
        abbrev_offset=abbrev_offset,
        unit_end=unit_end,
        extras=extras,
    )


def parse_debug_info(debug_sections: dict) -> dict:
    data = debug_sections.get(".debug_info", {}).get("data", b"")
    abbrev_data = debug_sections.get(".debug_abbrev", {}).get("data", b"")
    if not data:
        return {"compile_units": []}

    reader = stream.BinaryReader(data)
    units = []

    while reader.tell() < len(data):
        unit = _parse_unit_header(reader)
        table = (
            abbrev.parse_abbrev_table(abbrev_data, unit.abbrev_offset) if abbrev_data else {}
        )

        dies = []
        while reader.tell() < unit.unit_end:
            die_offset = reader.tell()
            abbrev_code = reader.read_uleb128()
            if abbrev_code == 0:
                continue

            entry = table.get(abbrev_code)
            if entry is None:
                break

            attrs = []
            unit_bases = {}
            for spec in entry.attributes:
                value = forms.decode_form(
                    spec.form,
                    reader,
                    dwarf64=unit.is_64bit,
                    address_size=unit.address_size,
                    debug_sections=debug_sections,
                    unit_bases=unit_bases,
                    implicit_const=spec.implicit_const,
                )
                attrs.append({"attr": spec.name, "form": spec.form, "value": value})

            dies.append(
                {
                    "offset": die_offset,
                    "abbrev_code": abbrev_code,
                    "tag": entry.tag,
                    "has_children": entry.has_children,
                    "attributes": attrs,
                }
            )

        units.append(
            {
                "header": unit,
                "dies": dies,
            }
        )

        reader.seek(unit.unit_end)

    return {"compile_units": units}
