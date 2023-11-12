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

import struct
import logging
from collections import defaultdict

from typing import Optional, Union, List

from macho_enums import (MACHO_MAGIC_STR, MACHO_MAGIC_SPEC,
                         MH_MAGIC, MH_CIGAM, MH_MAGIC_64, MH_CIGAM_64, FAT_MAGIC, FAT_CIGAM,
                         NFAT_ARCH_STR, ARCH_STR, NFAT_ARCH_SPEC, ARCH_SPEC, MACHO_HEADER32_STR,
                         MACHO_HEADER64_SPEC, MACHO_HEADER32_SPEC, SEGMENT64_COMMAND_STR,
                         MACHO_HEADER64_STR, LOAD_CMD_STR, LOAD_CMD_SPEC,
                         ENTRY_POINT_COMMAND_STR, ENTRY_POINT_COMMAND_SPEC, SEGMENT64_COMMAND_SPEC,
                         SEGMENT32_COMMAND_SPEC, SEGMENT32_COMMAND_STR, NLIST64_SPEC,
                         SYMTAB_STR, SYMTAB_SPEC, NLIST32_STR, NLIST64_STR, NLIST32_SPEC,
                         SECTION32_SPEC, SECTION32_STR, SECTION64_SPEC, SECTION64_STR,
                         DYSYMTAB_STR, DYSYMTAB_SPEC)

NAME = "parse_macho"
logger = logging.getLogger(NAME)


def parse_macho(data: bytes, oid: str, file_offset: int = 0) -> dict:
    """ Process a potential Mach-O file by first determining if it is a single Mach-O file
        or if it is a Fat /OSX Universal file with multiple embedded Mach-O files. The
        file type can be determined by parsing the magic value.

        - If it is a single Mach-O file process it accordingly.

        - If it is a Fat file then first process the Fat header then process each
          embedded Mach-O file.
    """
    header = {}
    header = parse_magic_header(data, file_offset)
    if not header:
        logger.info("Magic value not found for %s", oid)

    elif header["type"] == "Mach-O":
        # Single Mach-O file
        header["header_offset"] = header["magic_len"]
        macho_header = process_macho_header(data, header, file_offset)
        header.update(macho_header)

    elif header["type"] == "Fat":
        # Fat/OSX Universal file has multiple embedded Mach-O files
        header["header_offset"] = header["magic_len"]
        fat_header = parse_fat_header(data, header)
        fat_header["embedded"] = []

        # Process embedded Mach-O files
        for arch in fat_header["arches"]:
            pass
            # recursively parse macho in file
            #TODO: something sane here... macho = process_macho_header(data[arch["offset"]:], fat_header, file_offset + arch["offset"])  # noqa
            #fat_header["embedded"].append(macho)
        header.update(fat_header)

    else:
        logger.info("Unknown header type for %s", oid)

    return header


def process_macho_header(data: bytes, header: dict, file_offset) -> dict:
    """ Process the Mach-O header by first parsing the header then process each load
        command.
    """
    macho_header = parse_macho_header(data, header)
    load_cmds = parse_load_commands(data, macho_header)
    if load_cmds is None:
        return macho_header

    segments = {}
    dylibs = []
    # weak_dylibs = []
    # id_dylibs = []
    # all_dylibs = []
    entry_point = None
    stack_size = None
    uuid = None
    symtab = None
    dysymtab = None
    linker = None

    cmd_offset = macho_header["header_end"]
    cpu_type = macho_header["cputype"]
    big_endian = macho_header["big_endian"]
    addr_size = macho_header["addr_size"]

    # Process load commands
    for load_cmd in load_cmds:
        if load_cmd["cmd_type"] == "SEGMENT":
            segment = parse_segment_command(data, cmd_offset, addr_size, big_endian)
            name = segment.pop("segname")
            segments[name] = segment

        elif load_cmd["cmd_type"] == "UUID":
            uuid = parse_uuid_command(data, cmd_offset, big_endian)

        elif load_cmd["cmd_type"] in ("THREAD", "UNIXTHREAD"):
            thread_command = parse_thread_command(data, cmd_offset, cpu_type, big_endian)
            load_cmd["thread_command"] = thread_command
            entry_point = load_cmd["thread_command"]["entry_point"]

        elif load_cmd["cmd_type"] == "MAIN":
            entry_point_command = parse_entry_point_command(data, cmd_offset, cpu_type, big_endian)
            entry_point = entry_point_command["entryoff"]
            stack_size = entry_point_command["stacksize"]

        elif load_cmd["cmd_type"] in ("LOAD_DYLIB", "LOAD_WEAK_DYLIB"):
            dylib = parse_dylib(data, cmd_offset, addr_size, big_endian)
            dylibs.append(dylib)

        elif load_cmd["cmd_type"] == "SYMTAB":
            symtab = parse_symtab(data, cmd_offset, addr_size, big_endian)

        elif load_cmd["cmd_type"] == "DYSYMTAB":
            dysymtab = parse_dysymtab(data, cmd_offset, big_endian)

        elif load_cmd["cmd_type"] == "LOAD_DYLINKER":
            linker = parse_dylinker(data, cmd_offset, big_endian)

        cmd_offset += load_cmd["cmdsize"]

    macho_header["commands"] = load_cmds
    macho_header["uuid"] = uuid
    macho_header["segments"] = segments
    macho_header["dylibs"] = dylibs
    macho_header["entry_point"] = entry_point
    macho_header["stack_size"] = stack_size
    macho_header["symtab"] = symtab
    macho_header["dysymtab"] = dysymtab
    macho_header["linker"] = linker
    macho_header["imports"] = get_imports(symtab, dysymtab, dylibs)

    return macho_header


def find_section(header: dict, vaddr: int) -> Optional[int]:
    """ Given an address return the section that the address resides in
    """
    for seg in header["segments"]:
        sections = header["segments"][seg]["sections"]

        for _, sec_info in sections:
            beg = sec_info["addr"]
            end = beg + sec_info["size"]
            if beg <= vaddr <= end:
                return sec_info
    return None


def get_offset(header: dict, vaddr: int) -> Optional[int]:
    """
    Returns physical offset of virtual address given.
    """

    offset = None
    section = find_section(header, vaddr)
    if section:
        offset = section['offset'] + (vaddr - section['addr'])
    return offset


def get_rva(header: dict, offset: int) -> Optional[int]:
    """
    Returns relative virtual address of physical offset.
    """
    rva = None
    for seg in header["segments"]:
        sections = header["segments"][seg]["sections"]
        for s in sections:
            ofs = sections[s]["offset"]
            end = ofs + sections[s]["size"]

            # if offset occurs in this section
            if ofs <= offset < end:
                begin_va = sections[s]["addr"]
                rva = begin_va + (offset - ofs)
                break
    return rva


# ---------------------- MAGIC VALUES ----------------------------------------------------


def parse_magic_header(data: bytes, file_offset: int) -> Optional[dict]:
    """ Parse the magic value and return a header dictionary
    """

    header = {}
    header["magic_len"] = struct.calcsize(MACHO_MAGIC_STR)

    if len(data) < header["magic_len"]:
        return None

    val_data = struct.unpack(MACHO_MAGIC_STR, data[: header["magic_len"]])
    for offset, elem in enumerate(MACHO_MAGIC_SPEC):
        header[elem[0]] = val_data[offset]

    if header["magic"] == MH_MAGIC:
        header["magic"] = b"0xfeedface"
        header["type"] = "Mach-O"
        header["big_endian"] = True
        header["addr_size"] = 32

    elif header["magic"] == MH_CIGAM:
        header["magic"] = b"0xcefaedfe"
        header["type"] = "Mach-O"
        header["big_endian"] = False
        header["addr_size"] = 32

    elif header["magic"] == MH_MAGIC_64:
        header["magic"] = b"0xfeedfacf"
        header["type"] = "Mach-O"
        header["big_endian"] = True
        header["addr_size"] = 64

    elif header["magic"] == MH_CIGAM_64:
        header["magic"] = b"0xcffaedfe"
        header["type"] = "Mach-O"
        header["big_endian"] = False
        header["addr_size"] = 64

    elif header["magic"] == FAT_MAGIC:
        header["type"] = "Fat"
        header["magic"] = b"0xcafebabe"
        header["big_endian"] = True

    elif header["magic"] == FAT_CIGAM:
        header["magic"] = b"0xbebafeca"
        header["big_endian"] = False
        header["type"] = "Fat"

    else:
        header["type"] = "Unknown"
        logger.warning("Unsupported type %s", header["magic"])

    header["offsets"] = defaultdict(list)
    header["offsets"][file_offset].append({"len": 4, "string": "Magic"})

    return header


# ---------------------- FAT / OSX UNIVERSAL HEADER --------------------------------------


def parse_fat_header(data: bytes, header: dict) -> Optional[dict]:
    """ An array of fat_arch data structures appears directly after the fat_header data
        structure of a binary that contains object files for multiple architectures.

        Regardless of the content this data structure describes, all its fields are stored
        in big-endian byte order.
    """
    nfat_arch_str = ('>' if header["big_endian"] else '<') + NFAT_ARCH_STR
    arch_str = ('>' if header["big_endian"] else '<') + ARCH_STR

    nfat_arch_len = struct.calcsize(nfat_arch_str)
    if len(data) < nfat_arch_len:
        return None

    val_data = struct.unpack(nfat_arch_str,
                             data[header["header_offset"]:
                                  header["header_offset"] + nfat_arch_len])

    for offset, elem in enumerate(NFAT_ARCH_SPEC):
        header[elem[0]] = val_data[offset]

    arch_len = struct.calcsize(arch_str)
    header["header_len"] = header["nfat_arch"] * arch_len
    header["header_end"] = header["header_offset"] + header["header_len"]
    if len(data) < header["header_end"]:
        return header

    # Parse each arch entry
    arches = []
    arch_offset = header["header_offset"] + nfat_arch_len
    for _ in range(header["nfat_arch"]):
        arch_end = arch_offset + arch_len
        val_data = struct.unpack(arch_str, data[arch_offset:arch_end])
        arch = {}
        for offset, elem in enumerate(ARCH_SPEC):
            arch[elem[0]] = val_data[offset]

        arch["cputype"] = get_cputype(arch["cputype"])
        arches.append(arch)
        arch_offset += arch_len

    header["arches"] = arches
    return header


# ---------------------- MACH-O HEADER ---------------------------------------------------


def parse_macho_header(data: bytes, header: dict) -> dict:
    if header["addr_size"] == 32:
        macho_header_spec = MACHO_HEADER32_SPEC
        macho_header_str = ('>' if header["big_endian"] else '<') + MACHO_HEADER32_STR
    else:
        macho_header_spec = MACHO_HEADER64_SPEC
        macho_header_str = ('>' if header["big_endian"] else '<') + MACHO_HEADER64_STR

    header["header_len"] = struct.calcsize(macho_header_str)
    header["header_end"] = header["header_offset"] + header["header_len"]

    if len(data) < header["header_end"]:
        return header

    val_data = struct.unpack(macho_header_str,
                             data[header["header_offset"]: header["header_end"]])
    for offset, elem in enumerate(macho_header_spec):
        header[elem[0]] = val_data[offset]

    header["cputype"] = get_cputype(header["cputype"])
    header["filetype"] = get_filetype(header["filetype"])
    header["flags"] = get_flags(header["flags"])

    return header


# ---------------------- LOAD COMMANDS ---------------------------------------------------


def parse_load_commands(data: bytes, header: dict) -> Optional[dict]:
    cmd_offset = header["header_end"]
    cmd_size = header["sizeofcmds"]
    num_cmds = header["ncmds"]

    load_cmd_str = ('>' if header["big_endian"] else '<') + LOAD_CMD_STR

    if len(data) < cmd_offset + cmd_size:
        return None

    cmd_len = struct.calcsize(load_cmd_str)
    commands = []
    for _ in range(num_cmds):
        vals = {}
        val_data = struct.unpack(load_cmd_str, data[cmd_offset: cmd_offset + cmd_len])
        for offset, elem in enumerate(LOAD_CMD_SPEC):
            vals[elem[0]] = val_data[offset]

        vals["cmd_type"] = get_command_type(vals["cmd"])
        cmd_offset += vals["cmdsize"]
        commands.append(vals)

    return commands


def parse_entry_point_command(data: bytes, cmd_offset: int, addr_size: int,
                              big_endian: bool) -> Optional[dict]:
    entry_point_command_str = ('>' if big_endian else '<') + ENTRY_POINT_COMMAND_STR

    entry_len = struct.calcsize(entry_point_command_str)
    segment_end = cmd_offset + entry_len
    if len(data) < segment_end:
        return None

    vals = {}
    val_data = struct.unpack(entry_point_command_str, data[cmd_offset:segment_end])
    for offset, elem in enumerate(ENTRY_POINT_COMMAND_SPEC):
        vals[elem[0]] = val_data[offset]

    return vals

# ---------------------- SEGMENTS --------------------------------------------------------
""" A segment defines a range of bytes in a Mach-O file and the addresses and memory
    protection attributes at which those bytes are mapped into virtual memory when the
    dynamic linker loads the application. As such, segments are always virtual memory page
    aligned. A segment contains zero or more sections.
"""


def parse_segment_command(data, cmd_offset, addr_size, big_endian):
    if addr_size == 32:
        segment_command_spec = SEGMENT32_COMMAND_SPEC
        segment_command_str = ('>' if big_endian else '<') + SEGMENT32_COMMAND_STR
    else:
        segment_command_spec = SEGMENT64_COMMAND_SPEC
        segment_command_str = ('>' if big_endian else '<') + SEGMENT64_COMMAND_STR

    entry_len = struct.calcsize(segment_command_str)
    segment_end = cmd_offset + entry_len
    if len(data) < segment_end:
        return None

    vals = {}
    val_data = struct.unpack(segment_command_str, data[cmd_offset: segment_end])
    for offset, elem in enumerate(segment_command_spec):
        vals[elem[0]] = val_data[offset]

    name = vals["segname"].replace(b"\x00", b"")
    vals["segname"] = name

    sections = parse_sections(data, segment_end, vals["nsects"], addr_size, big_endian)
    vals["sections"] = sections

    return vals

# ----------------------- SECTIONS --------------------------------------------------------
""" The __TEXT and __DATA segments may contain a number of standard sections.
    The __OBJC segment contains a number of sections that are private to the
    Objective-C compiler.
    Note that the static linker and file analysis tools use the section type
    and attributes (instead of the section name) to determine how they should
    treat the section.
"""


def parse_sections(data, section_offset, nsects, addr_size, big_endian):
    if addr_size == 32:
        section_spec = SECTION32_SPEC
        section_str = ('>' if big_endian else '<') + SECTION32_STR
    else:
        section_spec = SECTION64_SPEC
        section_str = ('>' if big_endian else '<') + SECTION64_STR

    section_len = struct.calcsize(section_str)
    section_end = section_offset + section_len * nsects
    if len(data) < section_end:
        return None

    sections = {}
    for _ in range(nsects):
        val_data = struct.unpack(section_str, data[section_offset: section_offset+section_len])
        vals = {}
        for offset, elem in enumerate(section_spec):
            vals[elem[0]] = val_data[offset]

        vals["segname"] = vals["segname"].replace(b"\x00", b"")
        name = vals["sectname"].replace(b"\x00", b"")
        vals.pop("sectname")
        type_bits = vals["flags"] & 0x0000000f
        vals["type"] = get_section_type(type_bits)
        vals["flags"] = get_section_flags(vals["flags"])

        sections[name] = vals
        section_offset += section_len

    return sections


# ---------------------- SYMBOL TABLE ----------------------------------------------------
# The data structure for the SYMTAB load command including the size and location of the
# symbol table data structures.


def parse_symtab(data: bytes, cmd_offset: int, addr_size: int,
                 big_endian: bool) -> Optional[dict]:
    symtab_str = (">" if big_endian else "<") + SYMTAB_STR

    cmd_len = struct.calcsize(symtab_str)
    if len(data) < cmd_offset+cmd_len:
        return None

    val_data = struct.unpack(symtab_str, data[cmd_offset: cmd_offset + cmd_len])
    vals = {}
    for offset, elem in enumerate(SYMTAB_SPEC):
        vals[elem[0]] = val_data[offset]

    tmp_entries = parse_symtab_entries(data, vals["symoff"], vals["nsyms"],
                                       addr_size, big_endian)

    strend = vals["stroff"] + vals["strsize"]
    names = []
    entries = []
    for entry in tmp_entries:
        offset = vals["stroff"] + entry["n_un"]
        if offset == 0:
            name = "NULL"
        elif offset < strend:
            name = get_null_string(data, offset)
        else:
            name = "Unknown"

        entry["name"] = name
        entries.append(entry)
        names.append(name)

    vals["names"] = names
    vals["entries"] = entries

    return vals


def parse_symtab_entries(data, n_off, nsyms, addr_size, big_endian):
    if addr_size == 32:
        nlist_spec = NLIST32_SPEC
        nlist_str = (">" if big_endian else "<") + NLIST32_STR
    else:
        nlist_spec = NLIST64_SPEC
        nlist_str = (">" if big_endian else "<") + NLIST64_STR

    n_len = struct.calcsize(nlist_str)
    entries = []
    for _ in range(nsyms):
        if len(data) < n_off + n_len:
            break

        val_data = struct.unpack(nlist_str, data[n_off:n_off+n_len])
        vals = {}
        for offset, elem in enumerate(nlist_spec):
            vals[elem[0]] = val_data[offset]

        vals["type"] = get_symbol_type(vals["n_type"])
        vals["desc"] = get_symbol_desc(vals["n_desc"])

        entries.append(vals)
        n_off += n_len

    return entries


# --------------------- DYNAMIC SYMBOL TABLE -------------------------------------------
""" The data structure for the DYSYMTAB load command. It describes the sizes and
    locations of the parts of the symbol table used for dynamic linking.
"""

def parse_dysymtab(data: bytes, cmd_offset: int, big_endian: bool) -> Optional[dict]:
    dysymtab_str = (">" if big_endian else "<") + DYSYMTAB_STR

    cmd_len = struct.calcsize(dysymtab_str)

    if len(data) < cmd_offset + cmd_len:
        return None

    val_data = struct.unpack(dysymtab_str, data[cmd_offset:cmd_offset+cmd_len])
    vals = {}
    for offset, elem in enumerate(DYSYMTAB_SPEC):
        vals[elem[0]] = val_data[offset]

    return vals


def parse_dylib(data, cmd_offset, addr_size, big_endian):
    dylib_spec = [
        ("cmd",                   4, ""),
        ("cmdsize",               4, ""),
        ("offset",                4, "Offset to the name"),
        ("timestamp",             4, "Date and time when the shared library was built"),
        ("current_version",       4, ""),
        ("compatibility_version", 4, ""),
    ]
    if big_endian:
        dylib_str = ">IIIIII"
    else:
        dylib_str = "<IIIIII"

    cmd_len = struct.calcsize(dylib_str)
    if len(data) < cmd_offset+cmd_len:
        return None

    val_data = struct.unpack(dylib_str, data[cmd_offset:cmd_offset+cmd_len])
    vals = {}
    for offset, elem in enumerate(dylib_spec):
        vals[elem[0]] = val_data[offset]

    offset = vals["offset"] + cmd_offset
    vals["name"] = get_null_string(data, offset)
    return vals


# ---------------------- IMPORTS ---------------------------------------------------------


def get_imports(symtab, dysymtab, dylibs):
    imports = {}
    for dylib in dylibs:
        imports[dylib["name"]] = {}

    for sym in symtab["entries"]:
        if sym["n_value"] == 0:
            index = sym["n_desc"] >> 8
            dylib = dylibs[index-1]
            imports[dylib["name"]][sym["name"]] = sym

    return imports


# ---------------------- UUID ------------------------------------------------------------


def parse_uuid_command(data, cmd_offset: int, big_endian: bool) -> str:
    uuid_spec = [
        ("cmd",     4, ""),
        ("cmdsize", 4, ""),
        ("uuid",   16, ""),
    ]
    if big_endian:
        uuid_str = ">II16s"
    else:
        uuid_str = "<II16s"

    cmd_size = struct.calcsize(uuid_str)
    if len(data) < cmd_offset+cmd_size:
        return None

    val_data = struct.unpack(uuid_str, data[cmd_offset:cmd_offset+cmd_size])
    vals = {}
    for offset, elem in enumerate(uuid_spec):
        vals[elem[0]] = val_data[offset]

    # Convert uuid raw bytes to the string format XXXXXXXXX-XXXX-XXXX-XXXX-XXXXXXXXX
    uuid = ""
    for v in vals["uuid"]:
        val = hex(v).replace("0x", "").upper()
        if len(val) == 1:
            val = "0" + val
        uuid += val
        if len(uuid) == 8 or len(uuid) == 13 or len(uuid) == 18 or len(uuid) == 23:
            uuid += "-"

    return uuid

# ---------------------- DYLINKER --------------------------------------------------------


def parse_dylinker(data, cmd_offset, big_endian):
    dylinker_spec = [
        ("cmd",     4, ""),
        ("cmdsize", 4, ""),
        ("offset",  4, ""),
    ]
    if big_endian:
        dylinker_str = ">III"
    else:
        dylinker_str = "<III"

    cmd_len = struct.calcsize(dylinker_str)
    if len(data) < cmd_offset + cmd_len:
        return "Unknown"

    val_data = struct.unpack(dylinker_str, data[cmd_offset:cmd_offset+cmd_len])
    vals = {}
    for offset, elem in enumerate(dylinker_spec):
        vals[elem[0]] = val_data[offset]

    dylinker_offset = vals["offset"] + cmd_offset
    return get_null_string(data, dylinker_offset)

# ---------------------- THREAD Command --------------------------------------------------
# The THREAD command can be used to get the entry point by parsing the register values


def parse_thread_command(data, cmd_offset, cputype, big_endian=True):
    thread_command_spec = [
            ("cmd",     4, ""),
            ("cmdsize", 4, ""),
            ("flavor",  4, ""),
            ("count",   4, ""),
    ]
    if big_endian:
        thread_command_str = ">IIII"
    else:
        thread_command_str = "<IIII"

    cmd_len = struct.calcsize(thread_command_str)
    if len(data) < cmd_offset + cmd_len:
        return None

    val_data = struct.unpack(thread_command_str, data[cmd_offset:cmd_offset+cmd_len])
    vals = {}
    for offset, elem in enumerate(thread_command_spec):
        vals[elem[0]] = val_data[offset]

    # thread_state_start = cmd_offset+cmd_len
    # thread_state_end = thread_state_start + vals["cmdsize"]
    # cpu_thread_state = data[thread_state_start:thread_state_end]
    reg_offset = cmd_offset + cmd_len

    if cputype.startswith("x86"):
        if vals["flavor"] == 1:
            vals["flavor"] = "i386_THREAD_STATE"
            vals["reg_state"] = parse_x86_reg(data, reg_offset, big_endian)
            vals["entry_point"] = vals["reg_state"]["eip"]

        elif vals["flavor"] == 4:
            vals["flavor"] = "x86_THREAD_STATE64"
            vals["reg_state"] = parse_x86_64_reg(data, reg_offset, big_endian)
            vals["entry_point"] = vals["reg_state"]["rip"]

    elif cputype == "PPC":
        if vals["flavor"] == 1:
            vals["flavor"] = "PPC_THREAD_STATE"
        elif vals["flavor"] == 5:
            vals["flavor"] = "PPC_THREAD_STATE64"
        vals["reg_state"] = parse_ppc_reg(data, reg_offset, big_endian)
        vals["entry_point"] = vals["reg_state"]["srr0"]

    elif cputype == "ARM":
        if vals["flavor"] == 1:
            vals["flavor"] = "ARM_THREAD_STATE"
        vals["reg_state"] = parse_arm_reg(data, reg_offset, big_endian)
        vals["entry_point"] = vals["reg_state"]["r15"]

    return vals

# ---------------------- REG PARSING -----------------------------------------------------
# Register value parsing is used to get the entry point


def parse_x86_reg(data, reg_offset, big_endian):
    x86_reg_spec = [
        ("eax",    4, ""),
        ("ebx",    4, ""),
        ("exc",    4, ""),
        ("edx",    4, ""),
        ("edi",    4, ""),
        ("esi",    4, ""),
        ("ebp",    4, ""),
        ("esp",    4, ""),
        ("ss",     4, ""),
        ("eflags", 4, ""),
        ("eip",    4, ""),
        ("cs",     4, ""),
        ("ds",     4, ""),
        ("es",     4, ""),
        ("fs",     4, ""),
        ("gs",     4, ""),
    ]
    if big_endian:
        x86_reg_str = ">IIIIIIIIIIIIIIII"
    else:
        x86_reg_str = "<IIIIIIIIIIIIIIII"

    x86_reg_len = struct.calcsize(x86_reg_str)

    if len(data) < reg_offset + x86_reg_len:
        return None

    val_data = struct.unpack(x86_reg_str, data[reg_offset:reg_offset+x86_reg_len])
    vals = {}
    for offset, elem in enumerate(x86_reg_spec):
        vals[elem[0]] = val_data[offset]
    return vals


def parse_x86_64_reg(data, reg_offset, big_endian):
    x86_64_reg_spec = [
        ("rax",    8, ""),
        ("rbx",    8, ""),
        ("rxc",    8, ""),
        ("rdx",    8, ""),
        ("rdi",    8, ""),
        ("rsi",    8, ""),
        ("rbp",    8, ""),
        ("rsp",    8, ""),
        ("r8",     8, ""),
        ("r9",     8, ""),
        ("r10",    8, ""),
        ("r11",    8, ""),
        ("r12",    8, ""),
        ("r13",    8, ""),
        ("r14",    8, ""),
        ("r15",    8, ""),
        ("rip",    8, ""),
        ("rflags", 8, ""),
        ("cs",     8, ""),
        ("fs",     8, ""),
        ("gs",     8, ""),
    ]
    if big_endian:
        x86_64_reg_str = ">QQQQQQQQQQQQQQQQQQQQQ"
    else:
        x86_64_reg_str = "<QQQQQQQQQQQQQQQQQQQQQ"

    x86_64_reg_len = struct.calcsize(x86_64_reg_str)

    if len(data) < reg_offset + x86_64_reg_len:
        return None

    val_data = struct.unpack(x86_64_reg_str, data[reg_offset:reg_offset+x86_64_reg_len])
    vals = {}
    for offset, elem in enumerate(x86_64_reg_spec):
        vals[elem[0]] = val_data[offset]
    return vals


def parse_arm_reg(data, reg_offset, big_endian):
    arm_reg_spec = [
        ("r0",  4, ""),
        ("r1",  4, ""),
        ("r2",  4, ""),
        ("r3",  4, ""),
        ("r4",  4, ""),
        ("r5",  4, ""),
        ("r6",  4, ""),
        ("r7",  4, ""),
        ("r8",  4, ""),
        ("r9",  4, ""),
        ("r10", 4, ""),
        ("r11", 4, ""),
        ("r12", 4, ""),
        ("r13", 4, ""),
        ("r14", 4, ""),
        ("r15", 4, ""),
        ("r16", 4, ""),
    ]
    if big_endian:
        arm_reg_str = ">IIIIIIIIIIIIIIIII"
    else:
        arm_reg_str = "<IIIIIIIIIIIIIIIII"

    arm_reg_len = struct.calcsize(arm_reg_str)

    if len(data) < reg_offset + arm_reg_len:
        return None

    val_data = struct.unpack(arm_reg_str, data[reg_offset:reg_offset+arm_reg_len])
    vals = {}
    for offset, elem in enumerate(arm_reg_spec):
        vals[elem[0]] = val_data[offset]
    return vals


def parse_ppc_reg(data, reg_offset, big_endian):
    ppc_reg_spec = [
        ("srr0",   4, "Instruction address register (PC)"),
        ("srr1",   4, "Machine state register (supervisor)"),
        ("r0",     4, ""),
        ("r1",     4, ""),
        ("r2",     4, ""),
        ("r3",     4, ""),
        ("r4",     4, ""),
        ("r5",     4, ""),
        ("r6",     4, ""),
        ("r7",     4, ""),
        ("r8",     4, ""),
        ("r9",     4, ""),
        ("r10",    4, ""),
        ("r11",    4, ""),
        ("r12",    4, ""),
        ("r13",    4, ""),
        ("r14",    4, ""),
        ("r15",    4, ""),
        ("r16",    4, ""),
        ("r17",    4, ""),
        ("r18",    4, ""),
        ("r19",    4, ""),
        ("r20",    4, ""),
        ("r21",    4, ""),
        ("r22",    4, ""),
        ("r23",    4, ""),
        ("r24",    4, ""),
        ("r25",    4, ""),
        ("r26",    4, ""),
        ("r27",    4, ""),
        ("r28",    4, ""),
        ("r29",    4, ""),
        ("r30",    4, ""),
        ("r31",    4, ""),
        ("cr",     4, "Condition register"),
        ("xer",    4, "User's integer exception register"),
        ("lr",     4, "Link register"),
        ("ctr",    4, "Count register"),
        ("mq",     4, "MQ register (601 only)"),
        ("vrsave", 4, "Vector save register"),
    ]
    if big_endian:
        ppc_reg_str = ">IIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIII"
    else:
        ppc_reg_str = "<IIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIIII"

    ppc_reg_len = struct.calcsize(ppc_reg_str)
    if len(data) < reg_offset + ppc_reg_len:
        return None

    val_data = struct.unpack(ppc_reg_str, data[reg_offset:reg_offset+ppc_reg_len])
    vals = {}
    for offset, elem in enumerate(ppc_reg_spec):
        vals[elem[0]] = val_data[offset]
    return vals

# ---------------------- SYMBOLS UTILITY FUNCTIONS ---------------------------------------


def get_symbol_type(val):
    if val == 0x0:
        return ["UNDF"]

    types = []
    if val & 0x10:
        types.append("PEXT")

    if val & 0xe0:  # If STAB interpret type as debug
        types.append("STAB")

        if val == 0x20:
            types.append("DBG-GSYM")
        elif val == 0x22:
            types.append("DBG-FNAME")
        elif val == 0x24:
            types.append("DBG-FUN")
        elif val == 0x26:
            types.append("DBG-STSYM")
        elif val == 0x28:
            types.append("DBG-LCSYM")
        elif val == 0x2e:
            types.append("DBG-BNSYM")
        elif val == 0x3c:
            types.append("DBG-OPT")
        elif val == 0x40:
            types.append("DBG-RSYM")
        elif val == 0x44:
            types.append("DBG-SLINE")
        elif val == 0x4e:
            types.append("DBG-ENSYM")
        elif val == 0x60:
            types.append("DBG-SSYM")
        elif val == 0x64:
            types.append("DBG-SO")
        elif val == 0x66:
            types.append("DBG-OSO")
        elif val == 0x80:
            types.append("DBG-LSYM")
        elif val == 0x82:
            types.append("DBG-BINCL")
        elif val == 0x84:
            types.append("DBG-SOL")
        elif val == 0x86:
            types.append("DBG-PARAMS")
        elif val == 0x88:
            types.append("DBG-VERSION")
        elif val == 0x8A:
            types.append("DBG-OLEVEL")
        elif val == 0xa0:
            types.append("DBG-PSYM")
        elif val == 0xa2:
            types.append("DBG-EINCL")
        elif val == 0xa4:
            types.append("DBG-ENTRY")
        elif val == 0xc0:
            types.append("DBG-LBRAC")
        elif val == 0xc2:
            types.append("DBG-EXCL")
        elif val == 0xe0:
            types.append("DBG-RBRAC")
        elif val == 0xe2:
            types.append("DBG-BCOMM")
        elif val == 0xe4:
            types.append("DBG-ECOMM")
        elif val == 0xe8:
            types.append("DBG-ECOML")
        elif val == 0xfe:
            types.append("DBG-LENG")
        elif val == 0x30:
            types.append("DBG-PC")
        else:
            types.append(val)

        return types

    # If not STAB use standard types
    if 0x0e & val:
        sym_type = val & 0x0e
        if sym_type == 0x2:
            types.append("TYPE-ABS")
        elif sym_type == 0xe:
            types.append("TYPE-SECT")
        elif sym_type == 0xc:
            types.append("TYPE-PBUD")
        elif sym_type == 0xa:
            types.append("TYPE-INDR")
        else:
            types.append(sym_type)
    else:
        types.append(val)

    return types


def get_symbol_desc(val: int) -> List[str]:
    if val == 0x0:
        return ["UNDEFINED_NON_LAZY"]

    desc = []
    tmp_val = val & 0xf
    # Only one of these should apply
    if tmp_val == 0x1:
        desc.append("UNDEFINED_LAZY")
    elif tmp_val == 0x2:
        desc.append("DEFINED")
    elif tmp_val == 0x3:
        desc.append("PRIVATE_DEFINED")
    elif tmp_val == 0x4:
        desc.append("PRIVATE_UNDEFINED_NON_LAZY")
    elif tmp_val == 0x5:
        desc.append("PRIVATE_UNDEFINED_LAZY")

    if val & 0x10:
        desc.append("DYNAMICALLY")
    if val & 0x20:
        desc.append("DISCARDED")
    if val & 0x40:
        desc.append("WEAK_REF")
    if val & 0x80:
        desc.append("WEAK_DEF")

    if not desc:
        return [val]

    return desc

# ---------------------- SECTIONS UTILITY FUNCTIONS --------------------------------------


def get_section_type(val: int) -> str:
    res = val
    if val == 0x0:
        res = "REGULAR"
    elif val == 0x1:
        res = "ZEROFILL"
    elif val == 0x2:
        res = "CSTRING_LITERALS"
    elif val == 0x3:
        res = "4BYTE_LITERALS"
    elif val == 0x4:
        res = "8BYTE_LITERALS"
    elif val == 0x5:
        res = "LITERAL_POINTERS"
    elif val == 0x6:
        res = "NON_LAZY_SYMBOL_POINTERS"
    elif val == 0x7:
        res = "LAZY_SYMBOL_POINTERS"
    elif val == 0x8:
        res = "SYMBOL_STUBS"
    elif val == 0x9:
        res = "MOD_INIT_FUNC_POINTERS"
    elif val == 0xa:
        res = "MOD_TERM_FUNC_POINTERS"
    elif val == 0xb:
        res = "COALESCED"
    elif val == 0xc:
        res = "GB_ZEROFILL"
    elif val == 0xd:
        res = "INTERPOSING"
    elif val == 0xe:
        res = "1BYTE_LITERALS"
    elif val == 0xf:
        res = "DTRACE_DOF"
    elif val == 0x10:
        res = "LAZY_DYLIB_SYMBOL_POINTERS"
    elif val == 0x11:
        res = "THREAD_LOCAL_REGULAR"
    elif val == 0x12:
        res = "THREAD_LOCAL_ZEROFILL"
    elif val == 0x13:
        res = "THREAD_LOCAL_VARIABLES"
    elif val == 0x14:
        res = "THREAD_LOCAL_VARIABL_POINTERS"
    elif val == 0x15:
        res = "THREAD_LOCAL_INIT_FUNCTION_POINTERS"

    return res


def get_section_flags(val):
    flags = []
    if val & 0xff000000 == 0xff000000:
        flags.append("ATTRIBUTES_USR")
    if val & 0x80000000 == 0x80000000:
        flags.append("ATTR_PURE_INSTRUCTIONS")
    if val & 0x40000000 == 0x40000000:
        flags.append("ATTR_NO_TOC")
    if val & 0x20000000 == 0x20000000:
        flags.append("ATTR_STRIP_STATIC_SYMS")
    if val & 0x10000000 == 0x10000000:
        flags.append("ATTR_NO_DEAD_STRIP")
    if val & 0x08000000 == 0x08000000:
        flags.append("ATTR_LIVE_SUPPORT")
    if val & 0x04000000 == 0x04000000:
        flags.append("ATTR_SELF_MODIFYING_CODE")
    if val & 0x02000000 == 0x02000000:
        flags.append("ATTR_DEBUG")
    if val & 0x00ffff00 == 0x00ffff00:
        flags.append("ATTRIBUTES_SYS")
    if val & 0x00000400 == 0x00000400:
        flags.append("ATTR_SOME_INSTRUCTIONS")
    if val & 0x00000200 == 0x00000200:
        flags.append("ATTR_EXT_RELOC")
    if val & 0x00000100 == 0x00000100:
        flags.append("ATTR_LOC_RELOC")

    return flags

# ---------------------- MISC UTILITY FUNCTIONS ------------------------------------------


def get_null_string(data: bytes, offset: int) -> bytes:
    """ Given an list of data and an offset return the string from the offset to a null
    """
    s = b""
    data_len = len(data)
    if offset > data_len:
        return s

    c = data[offset:offset+1]
    while c != b"\x00" and offset < data_len:
        s += c
        c = data[offset:offset+1]
        offset += 1

    s = s.strip()
    return s


def get_cputype(val: int) -> str:
    cpu_arch_mask = 0x00ffffff
    cpu_arch_abi64 = 0x01000000
    cpu = "UNDEFINED"

    if val & cpu_arch_mask == 7:
        cpu = "x86"
    elif val & cpu_arch_mask == 12:
        cpu = "ARM"
    elif val & cpu_arch_mask == 18:
        cpu = "PPC"

    if val & cpu_arch_abi64:
        cpu += "_64"

    return cpu


def get_filetype(val: int) -> str:
    res = "UNDEFINED"
    if val == 0x1:
        res = "relocatable object file"
    elif val == 0x2:
        res = "demand paged executable file"
    elif val == 0x3:
        res = "fixed VM shared library file"
    elif val == 0x4:
        res = "core file"
    elif val == 0x5:
        res = "preloaded executable file"
    elif val == 0x6:
        res = "dynamically bound shared library"
    elif val == 0x7:
        res = "dynamic link editor"
    elif val == 0x8:
        res = "dynamically bound bundle file"
    elif val == 0x9:
        res = "shared library stub for static linking only, no section contents"
    elif val == 0xa:
        res = "companion file with only debug sections"
    elif val == 0xb:
        res = "kexts"

    return res


def get_flags(val: int) -> List[str]:
    flags = []
    if val & 0x1:
        flags.append("NOUNDEFS")
    if val & 0x2:
        flags.append("NCRLINK")
    if val & 0x4:
        flags.append("DYLDLINK")
    if val & 0x8:
        flags.append("BINDATLOAD")
    if val & 0x10:
        flags.append("PREBOUND")
    if val & 0x20:
        flags.append("SPLIT_SEGS")
    if val & 0x40:
        flags.append("LAZY_INIT")
    if val & 0x80:
        flags.append("TWOLEVEL")
    if val & 0x100:
        flags.append("FORCE_FLAT")
    if val & 0x200:
        flags.append("NOMULTIDEFS")
    if val & 0x400:
        flags.append("NOFIXPREBINDING")
    if val & 0x800:
        flags.append("PREBINDABLE")
    if val & 0x1000:
        flags.append("ALLMODSBOUND")
    if val & 0x2000:
        flags.append("SUBSECTIONS_VIA_SYMBOLS")
    if val & 0x4000:
        flags.append("CANONICAL")
    if val & 0x8000:
        flags.append("WEAK_DEFINES")
    if val & 0x10000:
        flags.append("BINDS_TO_WEAK")
    if val & 0x20000:
        flags.append("ALLOW_STACK_EXECUTION")
    if val & 0x40000:
        flags.append("ROOT_SAFE")
    if val & 0x80000:
        flags.append("SETUID_SAFE")
    if val & 0x100000:
        flags.append("NO_REEXPORTED_DYLIBS")
    if val & 0x200000:
        flags.append("PIE")
    if val & 0x400000:
        flags.append("DEAD_STRIPPABLE_DYLIB")
    if val & 0x800000:
        flags.append("HAS_TLV_DESCRIPTORS")
    if val & 0x1000000:
        flags.append("NO_HEAP_EXECUTION")

    return flags


def get_command_type(val: int) -> Union[str, int]:
    """
        https://raw.githubusercontent.com/synalysis/Grammars/master/mach-o.grammar
        https://www.sweetscape.com/010editor/repository/files/MachO.bt
    """
    req_dyld = 0x80000000

    if val == 0x1:
        res = "SEGMENT"
    elif val == 0x2:
        res = "SYMTAB"
    elif val == 0x3:
        res = "SYMSEG"
    elif val == 0x4:
        res = "THREAD"
    elif val == 0x5:
        res = "UNIXTHREAD"
    elif val == 0x6:
        res = "LOADFVMLIB"
    elif val == 0x7:
        res = "IDFVMLIB"
    elif val == 0x8:
        res = "IDENT"
    elif val == 0x9:
        res = "FVMFILE"
    elif val == 0xa:
        res = "PREPAGE"
    elif val == 0xb:
        res = "DYSYMTAB"
    elif val == 0xc:
        res = "LOAD_DYLIB"
    elif val == 0xd:
        res = "ID_DYLIB"
    elif val == 0xe:
        res = "LOAD_DYLINKER"
    elif val == 0xf:
        res = "ID_DYLIB"
    elif val == 0x10:
        res = "PREBOUND_DYLIB"
    elif val == 0x11:
        res = "ROUTINES"
    elif val == 0x12:
        res = "SUB_FRAMEWORK"
    elif val == 0x13:
        res = "SUB_UMBRELLA"
    elif val == 0x14:
        res = "SUB_CLIENT"
    elif val == 0x15:
        res = "SUB_LIBRARY"
    elif val == 0x16:
        res = "TWOLEVEL_HINTS"
    elif val == 0x17:
        res = "PREBIND_CKSUM"
    elif val ^ req_dyld == 0x18:
        res = "LOAD_WEAK_DYLIB"
    elif val == 0x19:
        res = "SEGMENT"
    elif val == 0x1a:
        res = "ROUTINES_64"
    elif val == 0x1b:
        res = "UUID"
    elif val ^ req_dyld == 0x1c:
        res = "RPATH"
    elif val == 0x1d:
        res = "CODE_SIGNATURE"
    elif val == 0x1e:
        res = "SEGMENT_SPLIT_INFO"
    elif val ^ req_dyld == 0x1f:
        res = "REEXPORT_DYLIB"
    elif val == 0x20:
        res = "LAZY_LOAD_DYLIB"
    elif val == 0x21:
        res = "ENCRYPTION_INFO"
    elif val == 0x22:
        res = "DYLD_INFO"
    elif val ^ req_dyld == 0x22:
        res = "DYLD_INFO_ONLY"
    elif val ^ req_dyld == 0x23:
        res = "LOAD_UPWARD_DYLIB"
    elif val == 0x24:
        res = "VERSION_MIN_MACOSX"
    elif val == 0x25:
        res = "VERSION_MIN_IPHONEOS"
    elif val == 0x26:
        res = "FUNCTION_STARTS"
    elif val == 0x27:
        res = "DYLD_ENVIRONMENT"
    elif val ^ req_dyld == 0x28:
        res = "MAIN"
    elif val == 0x29:
        res = "DATA_IN_CODE"
    elif val == 0x2A:
        res = "SOURCE_VERSION"
    elif val == 0x2B:
        res = "DYLIB_CODE_SIGN_DRS"
    elif val == 0x2C:
        res = "ENCRYPTION_INFO_64"
    elif val == 0x2d:
        res = "LINKER_OPTION"
    elif val == 0x2e:
        res = "LINKER_OPTIMIZATION_HINT"
    elif val == 0x2f:
        res = "VERSION_MIN_TVOS"
    elif val == 0x30:
        res = "VERSION_MIN_WATCHOS"
    elif val == 0x31:
        res = "NOTE"
    elif val == 0x32:
        res = "BUILD_VERSION"
    else:
        res = val
    return res
