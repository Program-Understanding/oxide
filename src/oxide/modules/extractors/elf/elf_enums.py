"""
Copyright 2023 National Technology & Engineering Solutions
of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS,
the U.S. Government retains certain rights in this software.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
"""

# -------------------------- ELF HEADER -------------------------------------

ELF_IDENT_SPEC = [
    ("magic",       4, "File magic"),
    ("class",       1, "File class"),
    ("data",        1, "Data encoding"),
    ("version",     1, "File version"),
    ("osabi",       1, "Operating system and ABI"),
    ("abi_version", 1, "Version of the ABI"),
    ("pad",         6, "padding"),
    ("nident",      1, "Size of ident[]"),
]
ELF_IDENT_STR = "=4sBBBBB6BB"

ELF_32_HEADER_SPEC = [
    ("type",      2, "File type"),
    ("machine",   2, "Architecture"),
    ("version",   4, "File version"),
    ("entry",     4, "Starting virtual address, 0 if it doesn't exist"),
    ("phoff",     4, "Program header offset, 0 if it doesn't exist"),
    ("shoff",     4, "Section header offset, 0 if it doesn't exist"),
    ("flags",     4, "Processor specific flags"),
    ("ehsize",    2, "ELF header size in bytes"),
    ("phentsize", 2, "Size in bytes of program header"),
    ("phnum",     2, "Number of program header entries"),
    ("shentsize", 2, "Section header size in bytes"),
    ("shnum",     2, "Number of section header entries"),
    ("shstrndx",  2, "Section header table index"),
]
ELF_32_HEADER_STR = "=HHLLLLLHHHHHH"

ELF_64_HEADER_SPEC = [
    ("type",      2, "File type"),
    ("machine",   2, "Architecture"),
    ("version",   4, "File version"),
    ("entry",     8, "Starting virtual address, 0 if it doesn't exist"),
    ("phoff",     8, "Program header offset, 0 if it doesn't exist"),
    ("shoff",     8, "Section header offset, 0 if it doesn't exist"),
    ("flags",     4, "Processor specific flags"),
    ("ehsize",    2, "ELF header size in bytes"),
    ("phentsize", 2, "Size in bytes of program header"),
    ("phnum",     2, "Number of program header entries"),
    ("shentsize", 2, "Section header size in bytes"),
    ("shnum",     2, "Number of section header entries"),
    ("shstrndx",  2, "Section header table index"),
]
ELF_64_HEADER_STR = "=HHLQQQLHHHHHH"

# ---------------------------- SECTIONS ---------------------------------

SECTION_32_ENTRY_SPEC = [
    ("name_offset", 4, "Offset to name of the section"),
    ("type",      4, "Section type"),
    ("flags",     4, "1-bit flags"),
    ("addr",      4, "Address of the first section's first byte"),
    ("offset",    4, "Offset from the first byte, or 0"),
    ("size",      4, "Section size in bytes"),
    ("link",      4, "Section header table index link"),
    ("info",      4, "Extra info"),
    ("addralign", 4, "Address alignment contraints, 0 otherwise"),
    ("entsize",   4, "Fixed-size entries"),
]
SECTION_32_ENTRY_STR = "=LLLLLLLLLL"

SECTION_64_ENTRY_SPEC = [
    ("name_offset", 4, "Offset to name of the section"),
    ("type",      4, "Section type"),
    ("flags",     8, "1-bit flags"),
    ("addr",      8, "Address of the first section's first byte"),
    ("offset",    8, "Offset from the first byte, or 0"),
    ("size",      8, "Section size in bytes"),
    ("link",      4, "Section header table index link"),
    ("info",      4, "Extra info"),
    ("addralign", 8, "Address alignment contraints, 0 otherwise"),
    ("entsize",   8, "Fixed-size entries"),
]
SECTION_64_ENTRY_STR = "=LLQQQQLLQQ"

# ---------------------------- SEGMENTS ---------------------------------

SEGMENT_32_ENTRY_SPEC = [
    ("type",   4, "Type of segment"),
    ("offset", 4, "Offset from begining of the file"),
    ("vaddr",  4, "Virtual address of the segment"),
    ("paddr",  4, "Physical address of the segment"),
    ("filesz", 4, "File image size in bytes"),
    ("memsz",  4, "Memory image size in bytes"),
    ("flags",  4, "Flags"),
    ("align",  4, "Segment alignment in memory and in the file"),
]
SEGMENT_32_ENTRY_STR = "=LLLLLLLL"

SEGMENT_64_ENTRY_SPEC = [
    ("type",   4, "Type of segment"),
    ("flags",  4, "Flags"),
    ("offset", 8, "Offset from begining of the file"),
    ("vaddr",  8, "Virtual address of the segment"),
    ("paddr",  8, "Physical address of the segment"),
    ("filesz", 8, "File image size in bytes"),
    ("memsz",  8, "Memory image size in bytes"),
    ("align",  8, "Segment alignment in memory and in the file"),
]
SEGMENT_64_ENTRY_STR = "<LLQQQQQQ"

# ---------------------------- RELOCATIONS ------------------------------

ELF_RELOCATION_32_TYPE_E = {
    0 : "R_x86_NONE",
    1 : "R_x86_32",
    2 : "R_x86_PC32",
    3 : "R_x86_GOT32",
    4 : "R_x86_PLT32",
    5 : "R_x86_COPY",
    6 : "R_x86_GLOB_DAT",
    7 : "R_x86_JUMP_SLOT",
    8 : "R_x86_RELATIVE",
    9 : "R_x86_GOTOFF",
    10: "R_x86_GOTPC",
    11: "R_x86_32PLT",
    # Thread-local storage
    # (https://docs.oracle.com/cd/E19120-01/open.solaris/819-0690/chapter8-50/index.html)
    12: "R_386_TLS_GD_PLT",
    13: "R_386_TLS_LDM_PLT",
    14: "R_386_TLS_TPOFF",
    15: "R_386_TLS_IE",
    16: "R_386_TLS_GOTIE",
    17: "R_386_TLS_LE",
    18: "R_386_TLS_GD",
    19: "R_386_TLS_LDM",
    #
    20: "R_x86_16",
    21: "R_x86_PC16",
    22: "R_x86_8",
    23: "R_x86_PC8",
    # TLS storage pt 2
    32: "R_386_TLS_LDO_32",
    35: "R_386_TLS_DTPMOD32",
    36: "R_386_TLS_DTPOFF32",
    #
    38: "R_x86_SIZE32"
}

ELF_RELOCATION_64_TYPE_E = {
    0: "R_X86_64_NONE",
    1: "R_X86_64_64",
    2: "R_X86_64_PC32",
    3: "R_X86_64_GOT32",
    4: "R_X86_64_PLT32",
    5: "R_X86_64_COPY",
    6: "R_X86_64_GLOB_DAT",
    7: "R_X86_64_JUMP_SLOT",
    8: "R_X86_64_RELATIVE",
    9: "R_X86_64_GOTPCREL",
    10: "R_X86_64_32",
    11: "R_X86_64_32S",
    12: "R_X86_64_16",
    13: "R_X86_64_PC16",
    14: "R_X86_64_8",
    15: "R_X86_64_PC8",
    24: "R_X86_64_PC64",
    25: "R_X86_64_GOTOFF64",
    26: "R_X86_64_GOTPC32",
    32: "R_X86_64_SIZE32",
    33: "R_X86_64_SIZE64",
    37: "R_X86_64_IRELATIV",
    42: "R_386_IRELATIVE"
}

ELF_RELOCATION_ARM_TYPE_E = {
    0: "R_ARM_NONE",
    1: "(Deprecated)R_ARM_PC24",
    2: "R_ARM_ABS32",
    3: "R_ARM_REL32",
    4: "R_ARM_LDR_PC_G0",
    5: "R_ARM_ABS16",
    6: "R_ARM_ABS12",
    7: "R_ARM_THM_ABS5",
    8: "R_ARM_ABS8",
    9: "R_ARM_SBREL32",
    10: "R_ARM_THM_CALL",
    11: "R_ARM_THM_PC8",
    12: "R_ARM_BREL_ADJ",
    13: "R_ARM_TLS_DESC",
    14: "(Deprecated)R_ARM_THM_SWI8",
    15: "(Deprecated)R_ARM_XPC25",
    16: "(Deprecated)R_ARM_THM_XPC22",
    17: "R_ARM_TLS_DTPMOD32",
    18: "R_ARM_TLS_DTPOFF32",
    19: "R_ARM_TLS_TPOFF32",
    20: "R_ARM_COPY",
    21: "R_ARM_GLOB_DAT",
    22: "R_ARM_JUMP_SLOT",
    23: "R_ARM_RELATIVE",
    24: "R_ARM_GOTOFF32",
    25: "R_ARM_BASE_PREL",
    26: "R_ARM_GOT_BREL",
    27: "(Deprecated)R_ARM_PLT32",
    28: "R_ARM_CALL",
    29: "R_ARM_JUMP24",
    30: "R_ARM_THM_JUMP24",
    31: "R_ARM_BASE_ABS",
    32: "(Deprecated)R_ARM_ALU_PCREL_7_0",
    33: "(Deprecated)R_ARM_ALU_PCREL_15_8",
    34: "(Deprecated)R_ARM_ALU_PCREL_23_15",
    35: "(Deprecated)R_ARM_LDR_SBREL_11_0_NC",
    36: "(Deprecated)R_ARM_ALU_SBREL_19_12_NC",
    37: "(Deprecated)R_ARM_ALU_SBREL_27_20_CK",
    38: "R_ARM_TARGET1",
    39: "(Deprecated)R_ARM_SBREL31",
    40: "R_ARM_V4BX",
    41: "R_ARM_TARGET2",
    42: "R_ARM_PREL31",
    43: "R_ARM_MOVW_ABS_NC",
    44: "R_ARM_MOVT_ABS",
    45: "R_ARM_MOVW_PREL_NC",
    46: "R_ARM_MOVT_PREL",
    47: "R_ARM_THM_MOVW_ABS_NC",
    48: "R_ARM_THM_MOVT_ABS",
    49: "R_ARM_THM_MOVW_PREL_NC",
    50: "R_ARM_THM_MOVT_PREL",
    51: "R_ARM_THM_JUMP19",
    52: "R_ARM_THM_JUMP6",
    53: "R_ARM_THM_ALU_PREL_11_0",
    54: "R_ARM_THM_PC12",
    55: "R_ARM_ABS32_NOI",
    56: "R_ARM_REL32_NOI",
    57: "R_ARM_ALU_PC_G0_NC",
    58: "R_ARM_ALU_PC_G0",
    59: "R_ARM_ALU_PC_G1_NC",
    60: "R_ARM_ALU_PC_G1",
    61: "R_ARM_ALU_PC_G2",
    62: "R_ARM_LDR_PC_G1",
    63: "R_ARM_LDR_PC_G2",
    64: "R_ARM_LDRS_PC_G0",
    65: "R_ARM_LDRS_PC_G1",
    66: "R_ARM_LDRS_PC_G2",
    67: "R_ARM_LDC_PC_G0",
    68: "R_ARM_LDC_PC_G1",
    69: "R_ARM_LDC_PC_G2",
    70: "R_ARM_ALU_SB_G0_NC",
    71: "R_ARM_ALU_SB_G0",
    72: "R_ARM_ALU_SB_G1_NC",
    73: "R_ARM_ALU_SB_G1",
    74: "R_ARM_ALU_SB_G2",
    75: "R_ARM_LDR_SB_G0",
    76: "R_ARM_LDR_SB_G1",
    77: "R_ARM_LDR_SB_G2",
    78: "R_ARM_LDRS_SB_G0",
    79: "R_ARM_LDRS_SB_G1",
    80: "R_ARM_LDRS_SB_G2",
    81: "R_ARM_LDC_SB_G0",
    82: "R_ARM_LDC_SB_G1",
    83: "R_ARM_LDC_SB_G2",
    84: "R_ARM_MOVW_BREL_NC",
    85: "R_ARM_MOVT_BREL",
    86: "R_ARM_MOVW_BREL",
    87: "R_ARM_THM_MOVW_BREL_NC",
    88: "R_ARM_THM_MOVT_BREL",
    89: "R_ARM_THM_MOVW_BREL",
    90: "R_ARM_TLS_GOTDESC",
    91: "R_ARM_TLS_CALL",
    92: "R_ARM_TLS_DESCSEQ",
    93: "R_ARM_THM_TLS_CALL",
    94: "R_ARM_PLT32_ABS",
    95: "R_ARM_GOT_ABS",
    96: "R_ARM_GOT_PREL",
    97: "R_ARM_GOT_BREL12",
    98: "R_ARM_GOTOFF12",
    99: "R_ARM_GOTRELAX",
    100: "(Deprecated)R_ARM_GNU_VTENTRY",
    101: "(Deprecated)R_ARM_GNU_VTINHERIT",
    102: "R_ARM_THM_JUMP11",
    103: "R_ARM_THM_JUMP8",
    104: "R_ARM_TLS_GD32",
    105: "R_ARM_TLS_LDM32",
    106: "R_ARM_TLS_LDO32",
    107: "R_ARM_TLS_IE32",
    108: "R_ARM_TLS_LE32",
    109: "R_ARM_TLS_LDO12",
    110: "R_ARM_TLS_LE12",
    111: "R_ARM_TLS_IE12GP",
    112: "R_ARM_PRIVATE_0",
    113: "R_ARM_PRIVATE_1",
    114: "R_ARM_PRIVATE_2",
    115: "R_ARM_PRIVATE_3",
    116: "R_ARM_PRIVATE_4",
    117: "R_ARM_PRIVATE_5",
    118: "R_ARM_PRIVATE_6",
    119: "R_ARM_PRIVATE_7",
    120: "R_ARM_PRIVATE_8",
    121: "R_ARM_PRIVATE_9",
    122: "R_ARM_PRIVATE_10",
    123: "R_ARM_PRIVATE_11",
    124: "R_ARM_PRIVATE_12",
    125: "R_ARM_PRIVATE_13",
    126: "R_ARM_PRIVATE_14",
    127: "R_ARM_PRIVATE_15",
    128: "(Deprecated)R_ARM_ME_TOO",
    129: "R_ARM_THM_TLS_DESCSEQ16",
    130: "R_ARM_THM_TLS_DESCSEQ32",
    131: "R_ARM_THM_GOT_BREL12",
    132: "R_ARM_THM_ALU_ABS_G0_NC",
    133: "R_ARM_THM_ALU_ABS_G1_NC",
    134: "R_ARM_THM_ALU_ABS_G2_NC",
    135: "R_ARM_THM_ALU_ABS_G3",
    136: "R_ARM_THM_BF16",
    137: "R_ARM_THM_BF12",
    138: "R_ARM_THM_BF18",
    # 139-159: "(RESERVED)"
    160: "(Reserved)R_ARM_IRELATIVE",
    161: "R_ARM_PRIVATE_16",
    162: "R_ARM_PRIVATE_17",
    163: "R_ARM_PRIVATE_18",
    164: "R_ARM_PRIVATE_19",
    165: "R_ARM_PRIVATE_20",
    166: "R_ARM_PRIVATE_21",
    167: "R_ARM_PRIVATE_22",
    168: "R_ARM_PRIVATE_23",
    169: "R_ARM_PRIVATE_24",
    170: "R_ARM_PRIVATE_25",
    171: "R_ARM_PRIVATE_26",
    172: "R_ARM_PRIVATE_27",
    173: "R_ARM_PRIVATE_28",
    174: "R_ARM_PRIVATE_29",
    175: "R_ARM_PRIVATE_30",
    176: "R_ARM_PRIVATE_31",
    # 177-255: "(Reserved)"
}

# endianness added in parsing
RELOCATIONS_32_STRINGS = {
    "REL" : "II",
    "RELA": "III"
}

RELOCATIONS_64_STRINGS = {
    "REL" : "QQ",
    "RELA": "QQQ"
}

ELF_RELOCATION_MAGIC_STRINGS = {
    "32-bit_REL": ("2I", 4, 6),  # 32 bit
    "32-bit_RELA": ("3I", 4, 6),  # 32 bit
    "64-bit_REL": ("2Q", 8, 4),  # 64 bit
    "64-bit_RELA": ("3Q", 8, 4),  # 64 bit
    "32-bit_REL_little": ("<2I", 4, 6),  # 32 bit
    "32-bit_RELA_little": ("<3I", 4, 6),  # 32 bit
    "64-bit_REL_little": ("<2Q", 8, 4),  # 64 bit
    "64-bit_RELA_little": ("<3Q", 8, 4),  # 64 bit
}

SYMBOL_32_ENTRY_SPEC = [
    ("name",  4, "Symbol name"),
    ("value", 4, "Value of the symbol, may be absolute or an address or ..."),
    ("size",  4, "Size of the symbol, may be 0"),
    ("info",  1, "Type and binding attributes"),
    ("other", 1, "No meaning, should be 0"),
    ("shndx", 2, "Section header table index for the symbol"),
]
SYMBOL_32_ENTRY_STR = "=LLLBBH"

SYMBOL_64_ENTRY_SPEC = [
    ("name",  4, "Symbol name"),
    ("info",  1, "Type and binding attributes"),
    ("other", 1, "No meaning, should be 0"),
    ("shndx", 2, "Section header table index for the symbol"),
    ("value", 8, "Value of the symbol, may be absolute or an address or ..."),
    ("size",  8, "Size of the symbol, may be 0"),
]
SYMBOL_64_ENTRY_STR = "=LBBHQQ"
