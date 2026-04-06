"""Minimal parser scaffold for .debug_loclists (DWARF5)."""


def parse_loclists(section_data: bytes) -> dict:
    return {
        "raw_size": len(section_data or b""),
        "status": "scaffold",
    }
