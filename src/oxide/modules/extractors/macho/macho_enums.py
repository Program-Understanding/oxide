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

# MAGIC VALUES
MH_MAGIC = b"\xfe\xed\xfa\xce"  # Macho-O 32-bit
MH_CIGAM = b"\xce\xfa\xed\xfe"  # Macho-0 32-bit  reverse endian

MH_MAGIC_64 = b"\xfe\xed\xfa\xcf"  # Macho-O 64-bit
MH_CIGAM_64 = b"\xcf\xfa\xed\xfe"  # Macho-O 64-bit reversed endian

FAT_MAGIC = b"\xca\xfe\xba\xbe"  # FAT/Universal
FAT_CIGAM = b"\xbe\xba\xfe\xca"  # FAT/Universal reverse endian

MACHO_MAGIC_SPEC = [
    ("magic", 4, "Magic value"),
]
MACHO_MAGIC_STR = "4s"

NFAT_ARCH_SPEC = [
    ("nfat_arch",  4, "Specifies the number of fat_arch data structures"),
]
NFAT_ARCH_STR = "I"

ARCH_SPEC = [
    ("cputype",    4, "CPU family"),
    ("cpusubtype", 4, "CPU subtype"),
    ("offset",     4, "Offset to the beginning of the data for this CPU"),
    ("size",       4, "Size of the data for this CPU"),
    ("align",      4, "The power of 2 alignment for the offset of the object file for this CPU"),
]
ARCH_STR = "IIIII"

MACHO_HEADER32_SPEC = [
    ("cputype",    4, "CPU family"),
    ("cpusubtype", 4, ""),
    ("filetype",   4, ""),
    ("ncmds",      4, "The number of load commands"),
    ("sizeofcmds", 4, "The number of bytes that make up the load commands"),
    ("flags",      4, ""),
]
MACHO_HEADER32_STR = "IIIIII"

MACHO_HEADER64_SPEC = [
    ("cputype",    4, "CPU family"),
    ("cpusubtype", 4, ""),
    ("filetype",   4, ""),
    ("ncmds",      4, "The number of load commands"),
    ("sizeofcmds", 4, "The number of bytes that make up the load commands"),
    ("flags",      4, ""),
    ("reserved",   4, ""),
]
MACHO_HEADER64_STR = "IIIIIII"

LOAD_CMD_SPEC = [
    ("cmd",     4, "Type of load command"),
    ("cmdsize", 4, "Total size of command in bytes "),
]
LOAD_CMD_STR = "II"

ENTRY_POINT_COMMAND_SPEC = [
    ("cmd",       4, ""),
    ("cmdsize",   4, ""),
    ("entryoff",  8, "Entry address"),
    ("stacksize", 8, "Initial stack size"),
]
ENTRY_POINT_COMMAND_STR = "IIQQ"

SEGMENT32_COMMAND_SPEC = [
    ("cmd",      4, ""),
    ("cmdsize",  4, ""),
    ("segname", 16, ""),
    ("vmaddr",   4, "Starting virtual memory address of this segment"),
    ("vmsize",   4, "Size of virtual memory occupied by this segment"),
    ("fileoff",  4, "Indicates the offset in this file of the data to be mapped at vmaddr"),
    ("filesize", 4, "Indicates the number of bytes occupied by this segment on disk"),
    ("maxprot",  4, "Maximum permitted virtual memory protections of this segment"),
    ("initprot", 4, "Initial virtual memory protections of this segment"),
    ("nsects",   4, "Number of section data structures following this load command"),
    ("flags",    4, ""),
]
SEGMENT32_COMMAND_STR = "II16sIIIIIIII"

SEGMENT64_COMMAND_SPEC = [
    ("cmd",      4, ""),
    ("cmdsize",  4, ""),
    ("segname", 16, ""),
    ("vmaddr",   8, "Starting virtual memory address of this segment"),
    ("vmsize",   8, "Size of virtual memory occupied by this segment"),
    ("fileoff",  8, "Indicates the offset in this file of the data to be mapped at vmaddr"),
    ("filesize", 8, "Indicates the number of bytes occupied by this segment on disk"),
    ("maxprot",  4, "Maximum permitted virtual memory protections of this segment"),
    ("initprot", 4, "Initial virtual memory protections of this segmen"),
    ("nsects",   4, "Number of section data structures following this load command"),
    ("flags",    4, ""),
]
SEGMENT64_COMMAND_STR = "II16sQQQQIIII"

SECTION32_SPEC = [
    ("sectname", 16, ""),
    ("segname",  16, ""),
    ("addr",      4, "Virtual memory address of this section"),
    ("size",      4, "Size in bytes of the virtual memory occupied by this section"),
    ("offset",    4, "Offset to this section in the file"),
    ("align",     4, ""),
    ("reloc",     4, "File offset of the first relocation entry for this section"),
    ("nreloc",    4, "Number of relocation entries"),
    ("flags",     4, ""),
    ("reserved1", 4, ""),
    ("reserved2", 4, ""),
]
SECTION32_STR = "16s16sIIIIIIIII"

SECTION64_SPEC = [
    ("sectname", 16, ""),
    ("segname",  16, ""),
    ("addr",      8, ""),
    ("size",      8, ""),
    ("offset",    4, ""),
    ("align",     4, ""),
    ("reloc",     4, ""),
    ("nreloc",    4, ""),
    ("flags",     4, ""),
    ("reserved1", 4, ""),
    ("reserved2", 4, ""),
    ("reserved3", 4, ""),
]
SECTION64_STR = "16s16sQQIIIIIIII"

SYMTAB_SPEC = [
    ("cmd",     4, ""),
    ("cmdsize", 4, ""),
    ("symoff",  4, "Byte offset from the start of the file to the location of the symbol table entries."),
    ("nsyms",   4, "Number of entries in the symbol table"),
    ("stroff",  4, "Byte offset from the start of the image to the location of the string table"),
    ("strsize", 4, "Size in bytes of the string table"),
]
SYMTAB_STR = "IIIIII"

NLIST32_SPEC = [
    ("n_un",    4, "Index into the string table"),
    ("n_type",  1, "Type consisting of a four bit mask"),
    ("n_sect",  1, "Number of the sections that this symbol can be found in"),
    ("n_desc",  2, "Additional information about the nature of this symbol"),
    ("n_value", 4, "Format of this value is different for each type of symbol table entry (as specified by the type field"),
]
NLIST32_STR = "IBBHI"

NLIST64_SPEC = [
    ("n_un",    4, "Index into the string table"),
    ("n_type",  1, "Type consisting of a four bit mask"),
    ("n_sect",  1, "Number of the sections that this symbol can be found in"),
    ("n_desc",  2, "Additional information about the nature of this symbol"),
    ("n_value", 8, "Format of this value is different for each type of symbol table entry (as specified by the type field"),
]
NLIST64_STR = "IBBHQ"

DYSYMTAB_SPEC = [
    ("cmd",            4, ""),
    ("cmdsize",        4, ""),
    ("ilocalsym",      4, "Index of the first symbol in the group of local symbols"),
    ("nlocalsym",      4, "Number of symbols in the group of local symbols"),
    ("iextdefsym",     4, "Index of the first symbol in the group of defined external symbols"),
    ("nextdefsym",     4, "Number of symbols in the group of defined external symbols"),
    ("iundefsym",      4, "Index of the first symbol in the group of undefined external symbols"),
    ("nundefsym",      4, "Number of symbols in the group of undefined external symbols"),
    ("tocoff",         4, "Byte offset from the start of the file to the table of contents data"),
    ("ntoc",           4, "Number of entries in the table of contents"),
    ("modtaboff",      4, "Byte offset from the start of the file to the module table data"),
    ("nmodtab",        4, "Bumber of entries in the module table"),
    ("extrefsymoff",   4, "Byte offset from the start of the file to the external reference table data"),
    ("nextrefsyms",    4, "Number of entries in the external reference table"),
    ("indirectsymoff", 4, "Byte offset from the start of the file to the indirect symbol table data"),
    ("nindirectsyms",  4, "Number of entries in the indirect symbol table"),
    ("extreloff",      4, "Byte offset from the start of the file to the external relocation table data"),
    ("nextrel",        4, "Number of entries in the external relocation table"),
    ("locreloff",      4, "Byte offset from the start of the file to the local relocation table data"),
    ("nlocrel",        4, "Number of entries in the local relocation table"),
]
DYSYMTAB_STR = "IIIIIIIIIIIIIIIIIIII"
