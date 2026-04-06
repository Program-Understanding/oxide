"""Parser for .debug_abbrev."""

import constants
import models
import stream


def parse_abbrev_table(abbrev_data: bytes, table_offset: int) -> dict[int, models.AbbrevEntry]:
    reader = stream.BinaryReader(abbrev_data, offset=table_offset)
    table: dict[int, models.AbbrevEntry] = {}

    while reader.tell() < len(abbrev_data):
        code = reader.read_uleb128()
        if code == 0:
            break

        tag = reader.read_uleb128()
        has_children = bool(reader.read_u8())
        attrs: list[models.AbbrevAttributeSpec] = []

        while True:
            name = reader.read_uleb128()
            form = reader.read_uleb128()
            if name == 0 and form == 0:
                break

            implicit_const = None
            if form == int(constants.DwarfForm.IMPLICIT_CONST):
                implicit_const = reader.read_sleb128()

            attrs.append(
                models.AbbrevAttributeSpec(name=name, form=form, implicit_const=implicit_const)
            )

        table[code] = models.AbbrevEntry(
            code=code, tag=tag, has_children=has_children, attributes=attrs
        )

    return table
