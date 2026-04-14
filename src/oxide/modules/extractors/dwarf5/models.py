"""Core parser models."""

from dataclasses import dataclass, field
from typing import Any


@dataclass
class AbbrevAttributeSpec:
    name: int
    form: int
    implicit_const: int | None = None


@dataclass
class AbbrevEntry:
    code: int
    tag: int
    has_children: bool
    attributes: list[AbbrevAttributeSpec] = field(default_factory=list)


@dataclass
class UnitHeader:
    unit_offset: int
    is_64bit: bool
    unit_length: int
    version: int
    unit_type: int | None
    address_size: int
    abbrev_offset: int
    unit_end: int
    extras: dict[str, Any] = field(default_factory=dict)
