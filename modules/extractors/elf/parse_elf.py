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

DESC = " This module extracts features from the ELF header."
NAME = "parse_elf"

import struct
import logging
from collections import defaultdict

from typing import Optional, List, Tuple

from elf_enums import (ELF_IDENT_STR, ELF_IDENT_SPEC,
                       ELF_32_HEADER_STR, ELF_32_HEADER_SPEC,
                       ELF_64_HEADER_STR, ELF_64_HEADER_SPEC,
                       SECTION_32_ENTRY_STR, SECTION_32_ENTRY_SPEC,
                       SECTION_64_ENTRY_STR, SECTION_64_ENTRY_SPEC,
                       SYMBOL_32_ENTRY_STR, SYMBOL_32_ENTRY_SPEC,
                       SYMBOL_64_ENTRY_STR, SYMBOL_64_ENTRY_SPEC,
                       SEGMENT_32_ENTRY_STR, SEGMENT_32_ENTRY_SPEC,
                       SEGMENT_64_ENTRY_STR, SEGMENT_64_ENTRY_SPEC,
                       ELF_RELOCATION_32_TYPE_E, ELF_RELOCATION_64_TYPE_E,
                       # machine specific relocations
                       ELF_RELOCATION_ARM_TYPE_E,
                       RELOCATIONS_64_STRINGS, RELOCATIONS_32_STRINGS)

logger = logging.getLogger(NAME)
logger.debug("init")


def parse_elf(data: bytes, oid: str) -> Optional[dict]:

    header = {}
    header["offsets"] = defaultdict(list)

    # implicitly update offsets
    elf_header = parse_elf_header(data, header["offsets"])
    if not elf_header:
        logger.error("ELF Header not found in %s", oid)
        return None
    header["elf_header"] = elf_header

    sections = _parse_section_header(data, elf_header, header["offsets"])
    header["section_table"] = sections
    segments = _parse_program_header(data, elf_header, header["offsets"])
    header["segments"] = segments

    if not sections:
        logger.error("No sections found in %s", oid)
        return header

    (dyn_symbols, symbols), (dyn_imports, imports) = _parse_symbol_table(data, sections, elf_header, header["offsets"])
    header["dyn_symbols"] = dyn_symbols
    header["symbols"] = symbols
    header["imports"] = imports
    header["dyn_imports"] = dyn_imports

    # Parse Relocations
    header["relocations"] = _parse_relocations(sections, data, header)

    return header


def parse_elf_header(data: bytes, offsets: dict) -> dict:
    ident_len = struct.calcsize(ELF_IDENT_STR)
    # claimed length is less than provided
    if len(data) < ident_len:
        return None

    vals = {}

    val_data = struct.unpack(ELF_IDENT_STR, data[:ident_len])

    for offset, elem in enumerate(ELF_IDENT_SPEC):
        vals[elem[0]] = val_data[offset]

    if vals["magic"] != b"\x7fELF":
        return None

    vals["osabi"] = get_e_osabi(vals["osabi"])
    vals["class"] = get_e_class(vals["class"])

    elf_header_spec = ELF_32_HEADER_SPEC
    elf_header_str = ELF_32_HEADER_STR
    if vals["class"] == "64-bit":
        elf_header_spec = ELF_64_HEADER_SPEC
        elf_header_str = ELF_64_HEADER_STR

    header_len = struct.calcsize(elf_header_str)
    header_end = ident_len + header_len
    if len(data) < header_end:
        fill_len = header_end - len(data)
        data += b"\x00" * fill_len

    val_data = struct.unpack(elf_header_str, data[ident_len: header_end])
    for offset, elem in enumerate(elf_header_spec):
        vals[elem[0]] = val_data[offset]

    vals["machine"] = get_e_machine(vals["machine"])
    vals["type"] = get_e_type(vals["type"])
    vals["version"] = get_e_version(vals["version"])
    vals["data"] = get_e_data(vals["data"])

    return vals


def _parse_relocations(sections: dict, data: bytes, header: dict) -> Optional[dict]:
    '''
    This will parse the relocations from a elf binary in the sym tab and dyn sym sections
    '''
    dynsym_symbols = []

    try:
        for i in header["dyn_symbols"]:
            dynsym_symbols.append((header["dyn_symbols"][i]["value"], i))
    except KeyError:
        pass
    relocation_info = {}

    for section_name, section_info in sections.items():
        if not (section_info["type"] in ["REL", "RELA"]): continue
        reloc_info = section_info
        offset = section_info["offset"]
        size = section_info["size"]
        reloc_info["data"] = data[offset: offset + size]
        reloc_info["relocation_info"] = relocation_value_parser(reloc_info, data, header, dynsym_symbols)
        relocation_info[section_name] = reloc_info
    return relocation_info if relocation_info else None


def relocation_value_parser(relocation_info, data, header, dynsym_symbols):
    """ Parses relocation information for provided section
        https://refspecs.linuxbase.org/elf/gabi4+/ch4.reloc.html
    """
    if not (header["elf_header"]["machine"] in ["AMD x86-64 architecture", "Intel 80386", "ARM"]):
        return None

    rels = defaultdict(dict)

    sec_data = relocation_info["data"]
    # Iterates over entire relocation section
    section_offset = relocation_info["offset"]
    offset = section_offset

    if _is64bit(header["elf_header"]):
        reloc_str = RELOCATIONS_64_STRINGS[relocation_info["type"]]
        reloc_type_enum = ELF_RELOCATION_64_TYPE_E
    else:
        reloc_str = RELOCATIONS_32_STRINGS[relocation_info["type"]]
        reloc_type_enum = ELF_RELOCATION_32_TYPE_E

    if header["elf_header"]["data"] == "BigEndian":
        reloc_str = ">{}".format(reloc_str)
    else:
        reloc_str = "<{}".format(reloc_str)

    # TODO:: generalize this for machine type
    #   https://docs.oracle.com/cd/E19120-01/open.solaris/819-0690/chapter6-62988/index.html
    # Machine specific types (assume x86, optionally fix with ARM if present)
    if header["elf_header"]["machine"] == "ARM":
        reloc_type_enum = ELF_RELOCATION_ARM_TYPE_E

    format_size = struct.calcsize(reloc_str)
    logger.debug("Binary 64b: %s machine: %s type: %s", _is64bit(header["elf_header"]),
                                                       header["elf_header"]["data"],
                                                       header["elf_header"]["machine"])
    while offset < section_offset + relocation_info["size"]:
        # val_data is tuple of two or three elements
        val_data = struct.unpack(reloc_str, sec_data[offset - section_offset:
                                                     (offset - section_offset + format_size)])

        offset += format_size

        r_addend = None
        if relocation_info["type"] == "REL":
            r_offset, r_info = val_data
        else:  # RELA
            r_offset, r_info, r_addend = val_data

        rels[offset]["rva"] = r_offset

        # When setting info, we pad a number of 0s to info in order to properly index into
        # it to get symbol index and relocation type. The number of zeroes to parse is
        # format_size in 32 bit binaries (which is 8) an format_size / 2 in 64 bit binaries
        # (which is 12)
        if _is64bit(header["elf_header"]):
            rels[offset]["info"] = r_info
            rels[offset]["type"] = r_info & 0xffffffff  # lower 32 bits
            rels[offset]["sym_index"] = r_info >> 32          # top 32 bits
        else:  # magic_strings[0][0] == '2' or magic_strings[0][1] == '2': # 32 bit
            rels[offset]["info"] = r_info
            rels[offset]["type"] = r_info & 0xff        # lower 8 bits
            rels[offset]["sym_index"] = r_info >> 8           # top 24 bits

        try:
            rels[offset]["reloc_type"] = reloc_type_enum[rels[offset]["type"]]
        except KeyError:
            logger.info("invalid relocation parsing 64b: %s:%s machine: %s type: %s", _is64bit(header["elf_header"]),
                                                                                      header["elf_header"]["data"],
                                                                                      header["elf_header"]["machine"],
                                                                                      rels[offset]["type"])
            break

        # symbol index of 0 implies non-dynamic symbol, and symbol list starts at index 1
        if rels[offset]["sym_index"] > 0 and rels[offset]["sym_index"] <= len(dynsym_symbols):
            # index starts at 0
            dynsym_val, dynsym_name = dynsym_symbols[rels[offset]["sym_index"] - 1]
            rels[offset]["sym_name"] = dynsym_name
            rels[offset]["sym_val"] = dynsym_val
            rels[offset]["lib"] = None

        # RELA sections have updated value
        if r_addend and "sym_val" in rels[offset]:
            rels[offset]["sym_val"] += r_addend

        # FIXME:: libc.so does not parse the correct symbols+library for glob data
        # imports are organized into library -> symbols
        for imported_lib in header["imports"]:
            if ((imported_lib and "sym_name" in rels[offset]) and
               (rels[offset]["sym_name"] in header["imports"][imported_lib].keys() and
               imported_lib != "Unknown")):
                rels[offset]["lib"] = imported_lib

        # if dynamic symbol and library is not set, parse symbole table for it
        if "lib" in rels[offset] and rels[offset]["lib"] is None:
            for symbol in header["symbols"]:
                if "sym_name" in rels[offset] and rels[offset]["sym_name"] + "@@" in symbol:
                    rels[offset]["lib"] = symbol[symbol.index("@@") + 2:]
    return rels

# ----- Pretty printing value to string -----------------------


def get_e_osabi(val: int) -> str:
    """ Reference: https://pkg.go.dev/debug/elf#OSABI
    """
    exe_abi = "UNDEFINED"
    if val == 0:
        exe_abi = "None specified (SystemV)"
    elif val == 1:
        exe_abi = "HP-UX"
    elif val == 2:
        exe_abi = "NetBSD"
    elif val == 3:
        exe_abi = "Linux/GNU"
    elif val == 4:
        exe_abi = "GNU/HURD"
    elif val == 5:
        exe_abi = "86Open Common ABI"
    elif val == 6:
        exe_abi = "Sun Solaris"
    elif val == 7:
        exe_abi = "AIX"
    elif val == 8:
        exe_abi = "IRIX"
    elif val == 9:
        exe_abi = "FreeBSD"
    elif val == 10:
        exe_abi = "Compaq TRU64 UINIX"
    elif val == 11:
        exe_abi = "Novell Modesto"
    elif val == 12:
        exe_abi = "Open BSD"
    elif val == 13:
        exe_abi = "Open VMS"
    elif val == 14:
        exe_abi = "HP Non-Stop Kernel"
    elif val == 15:
        exe_abi = "Amiga Research OS"
    elif val == 16:
        exe_abi = "FenixOS"
    elif val == 17:
        exe_abi = "Nuxi CloudABI"
    elif val == 64:
        exe_abi = "ARM specific"
    elif val == 97:
        exe_abi = "ARM ABI"
    elif val == 255:
        exe_abi = "Standalone"
    return exe_abi


def get_e_data(val: int) -> str:
    endianness = "UNDEFINDED"
    if val == 0:
        endianness = "ELFDATANONE"  # Unknown data format
    elif val == 1:
        endianness = "LittleEndian"  # Two's complement, little-endian
    elif val == 2:
        endianness = "BigEndian"  # Two's complement, big-endian
    return endianness


def get_e_version(val):
    exe_version = "UNDEFINDED"
    if val == 0:
        exe_version = "Invalid version"
    elif val == 1:
        exe_version = "Current version"
    return exe_version


def get_e_type(val: int) -> str:
    """ https://code.woboq.org/userspace/glibc/elf/elf.h.html
    """
    exe_type = "UNDEFINDED"
    if val == 0:
        exe_type = "No file type"
    elif val == 1:
        exe_type = "Relocatable file"
    elif val == 2:
        exe_type = "Executable file"
    elif val == 3:
        exe_type = "Shared object file"
    elif val == 4:
        exe_type = "Core file"
    elif 0xfe00 < val < 0xfeff:
        exe_type = "OS-specific"
    elif 0xff00 < val < 0xffff:
        exe_type = "Processor-specific"
    return exe_type


def get_e_machine(val: int) -> str:
    """ Reference: https://refspecs.linuxfoundation.org/elf/gabi4+/ch4.eheader.html
            e_machine section
    """
    machine = "UNDEFINED"
    if val in [11, 12, 13, 14, 16,
               24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
               121, 122, 123, 124, 125, 126, 127, 128, 129, 130,
               145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159,
               182, 184, 205, 206, 207, 208, 209,
               225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240,
               241, 242]:
        machine = "Reserved for future use"
    elif val == 0:
        machine = "No machine"
    elif val == 1:
        machine = "AT&T WE 32100"
    elif val == 2:
        machine = "SPARC"
    elif val == 3:
        machine = "Intel 80386"
    elif val == 4:
        machine = "Motorola 68000"
    elif val == 5:
        machine = "Motorola 88000"
    elif val == 6:
        machine = "Reserved for future use (was EM_486)"
    elif val == 7:
        machine = "Intel 80860"
    elif val == 8:
        machine = "MIPS I Architecture"
    elif val == 9:
        machine = "IBM System/370 Processor"
    elif val == 10:
        machine = "MIPS RS3000 Little-endian"
    elif val == 15:
        machine = "Hewlett-Packard PA-RISC"
    elif val == 17:
        machine = "Fujitsu VPP500"
    elif val == 18:
        machine = "SPARC 32 Plus"
    elif val == 19:
        machine = "Intel 80960"
    elif val == 20:
        machine = "PowerPC"
    elif val == 21:
        machine = "64-bit PowerPC"
    elif val == 22:
        machine = "IBM System/390 Processor"
    elif val == 23:  # https://code.woboq.org/userspace/glibc/elf/elf.h.html
        machine = "IBM SPU/SPC"
    elif val == 36:
        machine = "NEC V800"
    elif val == 37:
        machine = "Fujitsu FR20"
    elif val == 38:
        machine = "TRW RH-32"
    elif val == 39:
        machine = "Motorola RCE"
    elif val == 40:
        machine = "ARM"
    elif val == 41:
        machine = "Digital Alpha"
    elif val == 42:
        machine = "Hitachi SH"
    elif val == 43:
        machine = "SPARCv9"
    elif val == 44:
        machine = "Siemens TriCore embedded processor"
    elif val == 45:
        machine = "Argonaut RISC Core, Argonaut Technologies Inc."
    elif val == 46:
        machine = "Hitachi H8/300"
    elif val == 47:
        machine = "Hitachi H8/300H"
    elif val == 48:
        machine = "Hitachi H8S"
    elif val == 49:
        machine = "Hitachi H8/500"
    elif val == 50:
        machine = "IA 64"
    elif val == 51:
        machine = "Stanford MIPS-X"
    elif val == 52:
        machine = "Motorola ColdFire"
    elif val == 53:
        machine = "Motorola M68HC12"
    elif val == 54:
        machine = "Fujitsu MMA Multimedia Accelerator"
    elif val == 55:
        machine = "Siemens PCP"
    elif val == 56:
        machine = "Sony nCPU embedded RISC processor"
    elif val == 57:
        machine = "Denso NDR1 microprocessor"
    elif val == 58:
        machine = "Motorola Star*Core processor"
    elif val == 59:
        machine = "Toyota ME16 processor"
    elif val == 60:
        machine = "STMicroelectronics ST100 processor"
    elif val == 61:
        machine = "Advanced Logic Corp. TinyJ embedded processor family"
    elif val == 62:
        machine = "AMD x86-64 architecture"
    elif val == 63:
        machine = "Sony DSP Processor"
    elif val == 64:
        machine = "Digital Equipment Corp. PDP-10"
    elif val == 65:
        machine = "Digital Equipment Corp. PDP-11"
    elif val == 66:
        machine = "Siemens FX66 microcontroller"
    elif val == 67:
        machine = "STMicroelectronics ST9+ 8/16 bit microcontroller"
    elif val == 68:
        machine = "STMicroelectronics ST7 8-bit microcontroller"
    elif val == 69:
        machine = "Motorola MC68HC16 Microcontroller"
    elif val == 70:
        machine = "Motorola MC68HC11 Microcontroller"
    elif val == 71:
        machine = "Motorola MC68HC08 Microcontroller"
    elif val == 72:
        machine = "Motorola MC68HC05 Microcontroller"
    elif val == 73:
        machine = "Silicon Graphics SVx"
    elif val == 74:
        machine = "STMicroelectronics ST19 8-bit microcontroller"
    elif val == 75:
        machine = "Digital VAX"
    elif val == 76:
        machine = "Axis Communications 32-bit embedded processor"
    elif val == 77:
        machine = "Infineon Technologies 32-bit embedded processor"
    elif val == 78:
        machine = "Element 14 64-bit DSP Processor"
    elif val == 79:
        machine = "LSI Logic 16-bit DSP Processor"
    elif val == 80:
        machine = "Donald Knuth's educational 64-bit processor"
    elif val == 81:
        machine = "Harvard University machine-independent object files"
    elif val == 82:
        machine = "SiTera Prism"
    elif val == 83:
        machine = "Atmel AVR 8-bit microcontroller"
    elif val == 84:
        machine = "Fujitsu FR30"
    elif val == 85:
        machine = "Mitsubishi D10V"
    elif val == 86:
        machine = "Mitsubishi D30V"
    elif val == 87:
        machine = "NEC v850"
    elif val == 88:
        machine = "Mitsubishi M32R"
    elif val == 89:
        machine = "Matsushita MN10300"
    elif val == 90:
        machine = "Matsushita MN10200"
    elif val == 91:
        machine = "picoJava"
    elif val == 92:
        machine = "OpenRISC 32-bit embedded processor"
    elif val == 93:
        machine = "ARC Cores Tangent-A5"
    elif val == 94:
        machine = "Tensilica Xtensa Architecture"
    elif val == 95:
        machine = "Alphamosaic VideoCore processor"
    elif val == 96:
        machine = "Thompson Multimedia General Purpose Processor"
    elif val == 97:
        machine = "National Semiconductor 32000 series"
    elif val == 98:
        machine = "Tenor Network TPC processor"
    elif val == 99:
        machine = "Trebia SNP 1000 processor"
    elif val == 100:
        machine = "STMicroelectronics ST200 microcontroller"
    # https://code.woboq.org/userspace/glibc/elf/elf.h.html
    elif val == 101:
        machine = "Ubicom IP2xxx"
    elif val == 102:
        machine = "MAX processor"
    elif val == 103:
        machine = "National Semi. CompactRISC"
    elif val == 104:
        machine = "Fujitsu F2MC16"
    elif val == 105:
        machine = "Texas Instruments msp430"
    elif val == 106:
        machine = "Analog Devices Blackfin DSP"
    elif val == 107:
        machine = "Seiko Epson S1C33 family"
    elif val == 108:
        machine = "Sharp embedded microprocessor"
    elif val == 109:
        machine = "Arca RISC"
    elif val == 110:
        machine = "PKU-Unity & MPRC Peking Uni. mc series"
    elif val == 111:
        machine = "eXcess configurable cpu"
    elif val == 112:
        machine = "Icera Semi. Deep Execution Processor"
    elif val == 113:
        machine = "Altera Nios II"
    elif val == 114:
        machine = "National Semi. CompactRISC CRX"
    elif val == 115:
        machine = "Motorola XGATE"
    elif val == 116:
        machine = "Infineon C16x/XC16x"
    elif val == 117:
        machine = "Renesas M16C"
    elif val == 118:
        machine = "Microchip Technology dsPIC30F"
    elif val == 119:
        machine = "Freescale Communication Engine RISC"
    elif val == 120:
        machine = "Renesas M32C"
    elif val == 131:
        machine = "Altium TSK3000"
    elif val == 132:
        machine = "Freescale RS08"
    elif val == 133:
        machine = "Analog Devices SHARC family"
    elif val == 134:
        machine = "Cyan Technology eCOG2"
    elif val == 135:
        machine = "Sunplus S+core7 RISC"
    elif val == 136:
        machine = "New Japan Radio (NJR) 24-bit DSP"
    elif val == 137:
        machine = "Broadcom VideoCore III"
    elif val == 138:
        machine = "RISC for Lattice FPGA"
    elif val == 139:
        machine = "Seiko Epson C17"
    elif val == 140:
        machine = "Texas Instruments TMS320C6000 DSP"
    elif val == 141:
        machine = "Texas Instruments TMS320C2000 DSP"
    elif val == 142:
        machine = "Texas Instruments TMS320C55x DSP"
    elif val == 143:
        machine = "Texas Instruments App. Specific RISC"
    elif val == 144:
        machine = "Texas Instruments Prog. Realtime Unit"
    elif val == 160:
        machine = "STMicroelectronics 64bit VLIW DSP"
    elif val == 161:
        machine = "Cypress M8C"
    elif val == 162:
        machine = "Renesas R32C"
    elif val == 163:
        machine = "NXP Semi. TriMedia"
    elif val == 164:
        machine = "QUALCOMM DSP6"
    elif val == 165:
        machine = "Intel 8051 and variants"
    elif val == 166:
        machine = "STMicroelectronics STxP7x"
    elif val == 167:
        machine = "Andes Tech. compact code emb. RISC"
    elif val == 168:
        machine = "Cyan Technology eCOG1X"
    elif val == 169:
        machine = "Dallas Semi. MAXQ30 mc"
    elif val == 170:
        machine = "New Japan Radio (NJR) 16-bit DSP"
    elif val == 171:
        machine = "M2000 Reconfigurable RISC"
    elif val == 172:
        machine = "Cray NV2 vector architecture"
    elif val == 173:
        machine = "Renesas RX"
    elif val == 174:
        machine = "Imagination Tech. META"
    elif val == 175:
        machine = "MCST Elbrus"
    elif val == 176:
        machine = "Cyan Technology eCOG16"
    elif val == 177:
        machine = "National Semi. CompactRISC CR16"
    elif val == 178:
        machine = "Freescale Extended Time Processing Unit"
    elif val == 179:
        machine = "Infineon Tech. SLE9X"
    elif val == 180:
        machine = "Intel L10M"
    elif val == 181:
        machine = "Intel K10M"
    elif val == 183:
        machine = "ARM AARCH64"
    elif val == 185:
        machine = "Amtel 32-bit microprocessor"
    elif val == 186:
        machine = "STMicroelectronics STM8"
    elif val == 187:
        machine = "Tileta TILE64"
    elif val == 188:
        machine = "Tilera TILEPro"
    elif val == 189:
        machine = "Xilinx MicroBlaze"
    elif val == 190:
        machine = "NVIDIA CUDA"
    elif val == 191:
        machine = "Tilera TILE-Gx"
    elif val == 192:
        machine = "CloudShield"
    elif val == 193:
        machine = "KIPO-KAIST Core-A 1st gen."
    elif val == 194:
        machine = "KIPO-KAIST Core-A 2nd gen."
    elif val == 195:
        machine = "Synopsys ARCompact V2"
    elif val == 196:
        machine = "Open8 RISC"
    elif val == 197:
        machine = "Renesas RL78"
    elif val == 198:
        machine = "Broadcom VideoCore V"
    elif val == 199:
        machine = "Renesas 78KOR"
    elif val == 200:
        machine = "Freescale 56800EX DSC"
    elif val == 201:
        machine = "Beyond BA1"
    elif val == 202:
        machine = "Beyond BA2"
    elif val == 203:
        machine = "XMOS xCORE"
    elif val == 204:
        machine = "Microchip 8-bit PIC(r)"
    elif val == 210:
        machine = "KM211 KM32"
    elif val == 211:
        machine = "KM211 KMX32"
    elif val == 212:
        machine = "KM211 KMX16"
    elif val == 213:
        machine = "KM211 KMX8"
    elif val == 214:
        machine = "KM211 KVARC"
    elif val == 215:
        machine = "Paneve CDP"
    elif val == 216:
        machine = "Cognitive Smart Memory Processor"
    elif val == 217:
        machine = "Bluechip CoolEngine"
    elif val == 218:
        machine = "Nanoradio Optimized RISC"
    elif val == 219:
        machine = "CSR Kalimba"
    elif val == 220:
        machine = "Zilog Z80"
    elif val == 221:
        machine = "Controls and Data Services VISIUMcore"
    elif val == 222:
        machine = "FTDI Chip FT32"
    elif val == 223:
        machine = "Moxie processor"
    elif val == 224:
        machine = "AMD GPU"
    elif val == 243:
        machine = "RISC-V"
    elif val == 247:
        machine = "Linux BPF -- in-kernel virtual machine"
    elif val == 252:
        machine = "C-SKY"
    elif val == 0x9026:
        machine = "Alpha"
    return machine


def get_e_class(val: int) -> str:
    addr_class = "UNDEFINDED"
    if val == 0:
        addr_class = "Invalid class"
    elif val == 1:
        addr_class = "32-bit"
    elif val == 2:
        addr_class = "64-bit"
    return addr_class


def get_section_type(val: int) -> str:
    """ https://code.woboq.org/userspace/glibc/elf/elf.h.html
        https://refspecs.linuxfoundation.org/LSB_2.1.0/LSB-Core-generic/LSB-Core-generic/elftypes.html
    """
    section_type = "UNDEFINED"
    if val == 0:
        section_type = "NULL"
    elif val == 1:
        section_type = "PROGBITS"
    elif val == 2:
        section_type = "SYMTAB"
    elif val == 3:
        section_type = "STRTAB"
    elif val == 4:
        section_type = "RELA"
    elif val == 5:
        section_type = "HASH"
    elif val == 6:
        section_type = "DYNAMIC"
    elif val == 7:
        section_type = "NOTE"
    elif val == 8:
        section_type = "NOBITS"
    elif val == 9:
        section_type = "REL"
    elif val == 10:
        section_type = "SHLIB"
    elif val == 11:
        section_type = "DYNSYM"
    elif val == 14:
        section_type = "INIT_ARRAY"
    elif val == 15:
        section_type = "FINI_ARRAY"
    elif val == 16:
        section_type = "PREINIT_ARRAY"
    elif val == 17:
        section_type = "GROUP"
    elif val == 18:
        section_type = "SYMTAB_SHNDX"

    # https://github.com/torvalds/linux/blob/master/include/uapi/linux/elf.h#L38
    elif val == 0x6474E550:
        section_type = "GNU_EH_FRAME"
    elif val == 0x6474E551:
        section_type = "GNU_STACK"
    elif val == 0x6474E552:
        section_type = "GNU_RELRO"
    elif val == 0x6474E553:
        section_type = "GNU_PROPERTY"

    elif val == 0x6ffffff5:
        section_type = "GNU_ATTRIBUTES"
    elif val == 0x6ffffff6:
        section_type = "GNU_HASH"
    elif val == 0x6ffffff7:
        section_type = "GNU_LIBLIST"
    elif val == 0x6ffffff8:
        section_type = "CHECKSUM"
    elif val == 0x6ffffffd:
        section_type = "GNU_VERDEF"
    elif val == 0x6ffffffe:
        section_type = "GNU_VERNEED"
    elif val == 0x6fffffff:
        section_type = "GNU_VERSYM"
    elif 0x60000000 < val < 0x6fffffff:
        # 0x70000000 "LOOS"
        # 0x7fffffff "HIOS"
        section_type = "OS(OSSPECIFIC)"
    elif 0x70000000 < val < 0x7fffffff:
        # 0x70000000 "LOPROC"
        # 0x7fffffff "HIPROC"
        section_type = "PROC(PROCSPECIFIC)"
    elif 0x80000000 < val < 0x8fffffff:
        # 0x80000000 "LOUSER"
        # 0x8fffffff "HIUSER"
        section_type = "USER(APPSPECIFIC)"
    return section_type


def get_segment_type(val: int) -> str:
    """ https://code.woboq.org/userspace/glibc/elf/elf.h.html
    """
    segment_type = "UNDEFINED"
    if val == 0:
        segment_type = "NULL"
    elif val == 1:
        segment_type = "LOAD"
    elif val == 2:
        segment_type = "DYNAMIC"
    elif val == 3:
        segment_type = "INTERP"
    elif val == 4:
        segment_type = "NOTE"
    elif val == 5:
        segment_type = "SHLIB"
    elif val == 6:
        segment_type = "PHDR"
    elif val == 7:
        segment_type = "TLS"
    elif val == 0x7000000 < val < 0x7fffffff:
        # LOPROC 0x7000000
        # HIPROC 0x7fffffff
        segment_type = "PROC(PROCSPECIFIC)"
    return segment_type


def get_symbol_info(val: int) -> str:
    symbol_info = "UNDEFINED ({})".format(val)
    if val == 0:
        symbol_info = "NOTYPE"
    elif val == 1:
        symbol_info = "OBJECT"
    elif val == 2:
        symbol_info = "FUNC"
    elif val == 3:
        symbol_info = "SECTION"
    elif val == 4:
        symbol_info = "FILE"
    elif val == 5:
        symbol_info = "COMMON"
    elif val == 6:
        symbol_info = "TLS"
    elif val == 7:
        symbol_info = "NUM"
    elif val == 10:
        symbol_info = "OS SPECIFIC LO"
    elif val == 12:
        symbol_info = "OS SPECIFIC HI"
    elif val == 13:
        symbol_info = "PROCESSOR SPECIFIC LO"
    elif val == 15:
        symbol_info = "PROCESSOR SPECIFIC HI"
    return symbol_info


def get_symbol_bind(val: int) -> str:
    """ https://refspecs.linuxfoundation.org/elf/gabi4+/ch4.symtab.html
        https://code.woboq.org/userspace/glibc/elf/elf.h.html
    """
    symbol_shndx = str(val)
    if val == 0:
        symbol_shndx = "LOCAL"
    elif val == 1:
        symbol_shndx = "GLOBAL"
    elif val == 2:
        symbol_shndx = "WEAK"
    elif val == 10:
        symbol_shndx = "GNU_UNIQUE"
    elif val == 13:
        symbol_shndx = "LOPROC"
    elif val == 14:
        symbol_shndx = "HIPROC"
    return symbol_shndx


def get_symbol_visibility(val: int) -> str:
    symbol_vis = "UNKNOWN"
    if val == 0:
        symbol_vis = "DEFAULT"
    elif val == 1:
        symbol_vis = "INTERNAL"
    elif val == 2:
        symbol_vis = "HIDDEN"
    elif val == 3:
        symbol_vis = "PROTECTED"
    return symbol_vis


def _is64bit(elf_header: dict) -> bool:
    return elf_header["class"] == "64-bit"


# ---------------- Sections ----------------------------------


def _parse_section_header(data, elf_header, offsets) -> Optional[dict]:
    """ Section header is an array of entries ...

        There is a special entry elf_header["shstrndx"] that has the string table needed
        for section names
    """
    if elf_header["shoff"] == 0:
        logger.error(" No section header")
        return None

    if _is64bit(elf_header):
        section_entry_str = SECTION_64_ENTRY_STR
        section_entry_spec = SECTION_64_ENTRY_SPEC
    else:
        section_entry_str = SECTION_32_ENTRY_STR
        section_entry_spec = SECTION_32_ENTRY_SPEC

    entry_len = struct.calcsize(section_entry_str)
    entries = {}
    offset = elf_header["shoff"]
    for entry in range(elf_header["shnum"]):
        vals = {}
        if len(data) < (offset + entry_len):
            break
        val_data = struct.unpack(section_entry_str, data[offset: offset + entry_len])
        for i, elem in enumerate(section_entry_spec):
            vals[elem[0]] = val_data[i]

        vals["flags"] = get_section_flags(vals["flags"])
        vals["type"] = get_section_type(vals["type"])
        entries[entry] = vals
        offset += entry_len

    if not entries:
        return None

    sections = assign_section_names(data, entries, elf_header["shstrndx"])
    return sections


def get_name_from_string_table(data: bytes, st_offset: int, index: int) -> Optional[str]:
    if index == 0:
        return None

    i = st_offset + index
    name = ""
    try:
        while data[i] != 0:  # Names are null terminated
            name += chr(data[i])
            i += 1
    except IndexError:
        logger.error(" Out of bounds while searching string table")
        name = None

    return name


def assign_section_names(data: bytes, entries: dict, st_entry: str) -> dict:
    if not entries:
        return {}

    offset = entries[st_entry]["offset"]  # offset to the string table section
    sections = {}
    for _, entry in entries.items():
        name = get_name_from_string_table(data, offset, entry["name_offset"])
        if name:
            sections[name] = entry
            sections[name]["name"] = name
    return sections


def get_section_flags(val: int) -> List[str]:
    # docs.oracle.com/cd/E19120-01/open.solaris/819-0690/6n33n7fcj/index.html
    # accessed: 9/6/21
    flags = []

    if val != 0x0:
        if val & 0x1:
            flags.append("WRITE")  # section is writeable during execution
        if val & 0x2:
            flags.append("ALLOC")  # section occupies memory during execution
        if val & 0x4:
            flags.append("EXECINSTR")  # section executes machine instructions
        if val & 0x10:
            flags.append("MERGE")  # section with data merged to remove duplication
        if val & 0x20:
            flags.append("STRINGS")  # null terminated character strings
        if val & 0x40:
            flags.append("INFO_LINK")  # section sh_info field holds section header table index
        if val & 0x80:
            flags.append("LINK_ORDER")  # special ordering requirements for linker
        if val & 0x100:
            flags.append("NONCONFORMING")  # os specific behavior beyond standard linking
        if val & 0x200:
            flags.append("GROUP")  # section is memory of a section group
        if val & 0x400:
            flags.append("TLS")  # thread local storage
        if val & 0x0ff00000:
            flags.append("MASKOS")  # OS specific semantics
        if val & 0x20000000:
            flags.append("AMD64_LARGE")  # section can hold more than 2GB data
        if val & 0x40000000:
            flags.append("ORDERED")  # older version of LINK_ORDER
        if val & 0x80000000:
            flags.append("EXCLUDE")  # excluded from input to linker of executable or shared object (can be ignored)
        if val & 0xf000000:
            flags.append("MASKPROC")  # processor specific semantics
    return flags


# ----------------------- PROGRAM HEADER ---------------------------------


def _parse_program_header(data, elf_header, offsets) -> Optional[dict]:
    """ Program header is an array of entries ...
    """
    if elf_header["phoff"] == 0:
        logger.error(" No program header")
        return None

    if _is64bit(elf_header):
        segment_entry_str = SEGMENT_64_ENTRY_STR
        segment_entry_spec = SEGMENT_64_ENTRY_SPEC
    else:
        segment_entry_str = SEGMENT_32_ENTRY_STR
        segment_entry_spec = SEGMENT_32_ENTRY_SPEC

    entry_len = struct.calcsize(segment_entry_str)
    offset = elf_header["phoff"]
    segments = {}
    for entry in range(elf_header["phnum"]):
        vals = {}
        if offset + entry_len > len(data): break
        val_data = struct.unpack(segment_entry_str, data[offset: offset + entry_len])
        for i, elem in enumerate(segment_entry_spec):
            vals[elem[0]] = val_data[i]

        vals["type"] = get_segment_type(vals["type"])
        vals["flags"] = get_segment_flags(vals["flags"])

        segments[entry] = vals
        offset += entry_len

    return segments


def get_segment_flags(val: int) -> List[str]:
    flags = []
    if val != 0:
        if val & 0x1:
            flags.append("EXECUTE")
        if val & 0x2:
            flags.append("WRITE")
        if val & 0x4:
            flags.append("READ")
        if val & 0xf0000000:
            flags.append("MASKPROC")  # unspecified meaning
    return flags


# -------------------------- SYMBOL TABLE ------------------------------------


def _parse_symbol_section(symbol_entry_str, symbol_entry_spec, sections, data, section, st_offset, entry_len, offsets):
    """  This will parse the passed section for symbols that it contains as well as info and offsets
    """
    symbols = {}
    imports = defaultdict(dict)
    offset = sections[section]["offset"]
    size = sections[section]["size"]
    index = offset

    while index < offset + size:
        vals = {}
        if len(data) < index + entry_len:
            break

        val_data = struct.unpack(symbol_entry_str, data[index:index + entry_len])
        for i, elem in enumerate(symbol_entry_spec):
            vals[elem[0]] = val_data[i]

        if st_offset is None:
            symbols[vals["name"]] = vals
        else:
            func_name = get_name_from_string_table(data, st_offset, vals["name"])
            if func_name:
                vals.pop("name")

                # info is unpacked into bind and info
                info = vals["info"] & 0xf
                bind = vals["info"] >> 4

                # convert enums to strings
                vals["info"] = get_symbol_info(info)
                vals["bind"] = get_symbol_bind(bind)
                vals["other"] = get_symbol_visibility(vals["other"])

                if vals["value"] == 0:
                    tmp_name = func_name
                    import_lib = "Unknown"
                    if "@@" in func_name:
                        i = tmp_name.find("@@")
                        func_name = tmp_name[:i]
                        import_lib = tmp_name[i:].strip("@@")

                    imports[import_lib][func_name] = vals

                symbols[func_name] = vals

        index += entry_len

    return symbols, imports


def _parse_symbol_table(data, sections, elf_header, offsets: dict) -> Tuple[dict, dict, dict]:
    """ Symbol table is an array of entries ...
    """
    sym_symbols = {}
    sym_dyn_symbols = {}
    sym_imports = {}
    sym_dyn_imports = {}
    sym_offsets = (None, None, None, None)

    if _is64bit(elf_header):
        symbol_entry_str = SYMBOL_64_ENTRY_STR
        symbol_entry_spec = SYMBOL_64_ENTRY_SPEC
    else:
        symbol_entry_str = SYMBOL_32_ENTRY_STR
        symbol_entry_spec = SYMBOL_32_ENTRY_SPEC
    entry_len = struct.calcsize(symbol_entry_str)

    st_offset = None
    if ".symtab" in sections:
        section = ".symtab"
        if ".strtab" in sections:
            st_offset = sections[".strtab"]["offset"]
        else:
            st_offset = sections[section]["offset"]
        sym_symbols, sym_imports = _parse_symbol_section(symbol_entry_str, symbol_entry_spec, sections, data, section, st_offset, entry_len, offsets)

    if ".dynsym" in sections:
        section = ".dynsym"
        if ".dynstr" in sections:
            st_offset = sections[".dynstr"]["offset"]
        else:
            st_offset = sections[section]["offset"]
        sym_dyn_symbols, sym_dyn_imports = _parse_symbol_section(symbol_entry_str, symbol_entry_spec, sections, data, section, st_offset, entry_len, offsets)

    else:
        section = None

    if section not in sections:
        return ({}, {}), ({}, {})

    return (sym_dyn_symbols, sym_symbols), (sym_dyn_imports, sym_imports)
