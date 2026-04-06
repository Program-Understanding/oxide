"""DWARF constants (focused subset for v4/v5 parser support)."""

from enum import IntEnum


class DwarfUnitType(IntEnum):
    COMPILE = 0x01
    TYPE = 0x02
    PARTIAL = 0x03
    SKELETON = 0x04
    SPLIT_COMPILE = 0x05
    SPLIT_TYPE = 0x06


class DwarfTag(IntEnum):
    COMPILE_UNIT = 0x11
    SUBPROGRAM = 0x2E
    INLINED_SUBROUTINE = 0x1D
    VARIABLE = 0x34
    FORMAL_PARAMETER = 0x05
    BASE_TYPE = 0x24
    CALL_SITE = 0x48
    CALL_SITE_PARAMETER = 0x49
    SKELETON_UNIT = 0x4A
    COARRAY_TYPE = 0x44
    DYNAMIC_TYPE = 0x46
    GENERIC_SUBRANGE = 0x45
    IMMUTABLE_TYPE = 0x4B
    ATOMIC_TYPE = 0x47


class DwarfAttribute(IntEnum):
    NAME = 0x03
    LOW_PC = 0x11
    HIGH_PC = 0x12
    LANGUAGE = 0x13
    STMT_LIST = 0x10
    COMP_DIR = 0x1B
    PRODUCER = 0x25
    TYPE = 0x49
    LOCATION = 0x02
    RANGES = 0x55
    ADDR_BASE = 0x73
    STR_OFFSETS_BASE = 0x72
    RNGLISTS_BASE = 0x74
    LOCLISTS_BASE = 0x8C
    DWO_NAME = 0x76
    DWO_ID = 0x2131
    NORETURN = 0x87
    DELETED = 0x8A
    DEFAULTED = 0x8B
    RANK = 0x81


class DwarfForm(IntEnum):
    ADDR = 0x01
    BLOCK2 = 0x03
    BLOCK4 = 0x04
    DATA2 = 0x05
    DATA4 = 0x06
    DATA8 = 0x07
    STRING = 0x08
    BLOCK = 0x09
    BLOCK1 = 0x0A
    DATA1 = 0x0B
    FLAG = 0x0C
    SDATA = 0x0D
    STRP = 0x0E
    UDATA = 0x0F
    REF_ADDR = 0x10
    REF1 = 0x11
    REF2 = 0x12
    REF4 = 0x13
    REF8 = 0x14
    REF_UDATA = 0x15
    INDIRECT = 0x16
    SEC_OFFSET = 0x17
    EXPRLOC = 0x18
    FLAG_PRESENT = 0x19
    REF_SIG8 = 0x20

    STRX = 0x1A
    ADDRX = 0x1B
    REF_SUP4 = 0x1C
    STRP_SUP = 0x1D
    DATA16 = 0x1E
    LINE_STRP = 0x1F
    REF_SIG8_V5 = 0x20
    IMPLICIT_CONST = 0x21
    LOCLISTX = 0x22
    RNGLISTX = 0x23
    REF_SUP8 = 0x24
    STRX1 = 0x25
    STRX2 = 0x26
    STRX3 = 0x27
    STRX4 = 0x28
    ADDRX1 = 0x29
    ADDRX2 = 0x2A
    ADDRX3 = 0x2B
    ADDRX4 = 0x2C


FORM_NAME = {int(v): v.name for v in DwarfForm}
ATTR_NAME = {int(v): v.name for v in DwarfAttribute}
TAG_NAME = {int(v): v.name for v in DwarfTag}
