"""Minimal parser scaffold for .debug_rnglists (DWARF5)."""


def parse_rnglists(section_data: bytes) -> dict:
    return {
        "raw_size": len(section_data or b""),
        "status": "scaffold",
    }
