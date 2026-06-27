"""Agentic tool layer — modular registry of atomic Oxide-capability tools.
"""
from __future__ import annotations

from .registry import build_tools, all_schemas, REGISTRY, ToolSpec, tool  # noqa: F401
from .context import OxideContext  # noqa: F401

# importing the group modules registers their tools
from . import elf, ghidra, util  # noqa: F401,E402

TOOL_SCHEMAS = all_schemas()


def schemas(groups=None) -> list:
    """Schemas for a group subset (None = all)."""
    return [s.schema for s in REGISTRY.values() if groups is None or s.group in set(groups)]
