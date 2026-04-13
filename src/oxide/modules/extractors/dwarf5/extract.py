"""Top-level DWARF extraction orchestration."""

import logging
import struct
from addr import parse_debug_addr
from aranges import parse_aranges
from constants import DwarfAttribute, DwarfTag, LANGUAGE_NAME
from info import parse_debug_info
from line import parse_line
from loclists import parse_loclists
from rnglists import parse_rnglists
from str_offsets import parse_str_offsets

logger = logging.getLogger("dwarf5.extract")

# Maps integer tag codes → DW_TAG_xxx string (best-effort; unknown → hex string)
_TAG_NAMES: dict[int, str] = {}
for _t in DwarfTag:
    _TAG_NAMES[int(_t)] = "DW_TAG_" + _t.name.lower()

_ATTR_NAMES: dict[int, str] = {}
for _a in DwarfAttribute:
    _ATTR_NAMES[int(_a)] = "DW_AT_" + _a.name.lower()

# DW_AT_language attribute code
_LANG_ATTR = int(DwarfAttribute.LANGUAGE)


def _tag_name(code: int) -> str:
    return _TAG_NAMES.get(code, f"DW_TAG_unknown_{code:#x}")


def _attr_name(code: int) -> str:
    return _ATTR_NAMES.get(code, f"DW_AT_unknown_{code:#x}")


def _normalize_info(raw: dict) -> dict:
    """Convert parse_debug_info output to the shape high_dwarf expects:

    {
      cu_offset: {
        die_offset: { "Tag": "DW_TAG_xxx", "Attributes": [(attr_str, value), ...] }
      }
    }
    """
    out: dict = {}
    for unit in raw.get("compile_units", []):
        hdr = unit["header"]
        cu_offset = hdr.unit_offset
        cu_dies: dict = {}
        for die in unit.get("dies", []):
            attrs = []
            for a in die.get("attributes", []):
                attr_name = _attr_name(a["attr"])
                value = a["value"]
                # Resolve DW_AT_language to human-readable name (e.g., 12 → "C99")
                if a["attr"] == _LANG_ATTR and isinstance(value, int):
                    value = LANGUAGE_NAME.get(value, str(value))
                attrs.append((attr_name, value))
            cu_dies[die["offset"]] = {
                "Tag": _tag_name(die["tag"]),
                "Attributes": attrs,
            }
        out[cu_offset] = cu_dies
    return out


def _initialize_sections(data: bytes, sections: dict) -> dict:
    dwarf_sections = {}
    for section_name, section_info in sections.items():
        if ".debug" not in str(section_name):
            continue
        section_start = section_info["section_offset"]
        section_end = section_start + section_info["section_len"]
        dwarf_sections[section_name] = dict(section_info)
        dwarf_sections[section_name]["data"] = data[section_start:section_end]
    return dwarf_sections


def parse_dwarf(oid: str, data: bytes, header) -> dict | None:
    sections = header.section_info
    if not sections:
        logger.info("No sections found for oid (%s)", oid)
        return None

    dwarf_sections = _initialize_sections(data, sections)
    out: dict = {"sections": sorted(dwarf_sections.keys())}

    if ".debug_info" in dwarf_sections:
        raw = parse_debug_info(dwarf_sections)
        out[".debug_info"] = _normalize_info(raw)

    if ".debug_addr" in dwarf_sections:
        # address_size is taken from the first CU header if available
        addr_size = 8
        if ".debug_info" in dwarf_sections:
            # peek at raw for address_size
            raw_info = parse_debug_info(dwarf_sections)
            cus = raw_info.get("compile_units", [])
            if cus:
                addr_size = cus[0]["header"].address_size
        out[".debug_addr"] = parse_debug_addr(
            dwarf_sections[".debug_addr"].get("data", b""), address_size=addr_size
        )

    if ".debug_str_offsets" in dwarf_sections:
        dwarf64 = False
        if ".debug_info" in dwarf_sections:
            raw_info = parse_debug_info(dwarf_sections)
            cus = raw_info.get("compile_units", [])
            if cus:
                dwarf64 = cus[0]["header"].is_64bit
        out[".debug_str_offsets"] = parse_str_offsets(
            dwarf_sections[".debug_str_offsets"].get("data", b""), dwarf64=dwarf64
        )

    if ".debug_rnglists" in dwarf_sections:
        out[".debug_rnglists"] = parse_rnglists(
            dwarf_sections[".debug_rnglists"].get("data", b"")
        )

    if ".debug_loclists" in dwarf_sections:
        out[".debug_loclists"] = parse_loclists(
            dwarf_sections[".debug_loclists"].get("data", b"")
        )

    if ".debug_aranges" in dwarf_sections:
        out[".debug_aranges"] = parse_aranges(
            dwarf_sections[".debug_aranges"].get("data", b"")
        )

    if ".debug_line" in dwarf_sections:
        out[".debug_line"] = parse_line(
            dwarf_sections[".debug_line"].get("data", b"")
        )

    return out
