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

""" pe_enums.py
Structs and enumerations for pe header types

spec: (name, offset, desc)
mask: (name, offset, desc)
enum: (value, name)

"""

# https://docs.microsoft.com/en-us/windows/win32/debug/pe-format#machine-types
MACHINE_ENUM = {
    0x0:    "Unknown",
    0x1d3:  "Matsushita AM33",
    0x8664: "AMD64",
    0x1c0:  "ARM little endian",
    0xaa64: "ARM64 little endian",
    0x1c4:  "ARM Thumb-2 little endian",
    0xebc:  "EFI bytecode",
    0x14c:  "Intel 386",
    0x200:  "Intel Itanium",
    0x6232: "LoongArch 32",
    0x6264: "LoongArch 64",
    0x9041: "Mitsubishi M32R little endian",
    0x266:  "MIPS16",
    0x366:  "MIPS with FPU",
    0x466:  "MIPS16 with FPU",
    0x1f0:  "PowerPC little endian",
    0x1f1:  "PowerPC with floating point support",
    0x166:  "MIPS little endian",
    0x5032: "RISC-V 32",
    0x5064: "RISC-V 64",
	0x5128: "RISC-V 128",
    0x1a2:  "Hitachi SH3",
    0x1a3:  "Hitachi SH3 DSP",
    0x1a6:  "Hitachi SH4",
    0x1a8:  "Hitachi SH5",
    0x1c2:  "ARM or Thumb",
    0x169:  "MIPS little endian WCE v2",
}

# https://docs.microsoft.com/en-us/windows/win32/debug/pe-format#windows-subsystem
SUBSYSTEM_ENUM = {
    0:  "Unknown",
    1:  "Native",
    2:  "Windows GUI",
    3:  "Windows CUI",
    5:  "OS/2",
    7:  "POSIX CUI",
    8:  "Native Win 9x Driver",
    9:  "Windows CE GUI",
    10: "EFI Application",
    11: "EFI Boot Service Driver",
    12: "EFI Runtime Driver",
    13: "EFI ROM Image",
    14: "XBOX",
    16: "Win Boot Application",
}

# https://docs.microsoft.com/en-us/windows/win32/debug/pe-format#intel-386-processors
# https://docs.microsoft.com/en-us/windows/win32/debug/pe-format#x64-processors
# https://docs.microsoft.com/en-us/windows/win32/debug/pe-format#arm-processors
# https://docs.microsoft.com/en-us/windows/win32/debug/pe-format#arm64-processors
# https://docs.microsoft.com/en-us/windows/win32/debug/pe-format#hitachi-superh-processors
# https://docs.microsoft.com/en-us/windows/win32/debug/pe-format#ibm-powerpc-processors
# etc...
# There are different relocation per arch (these are incorrect and loosely adapt 64 bit)
BASE_RELOCATION_TYPE_ENUM = {
    0: "absolute",
    1: "high16",
    2: "low16",
    3: "high_low",  # Adjust full 32 bits
    4: "high_adj",  # Takes 2 slots
    5: "mips_jmpaddr_arm_mov32a",
    7: "arm_mov32t",
    9: "mips_jumpaddr16",
    10: "dir64",
}

IMAGE_COFF_CHARACTERISTIC_MASK = [
    ("RELOCS_STRIPPED", 0x0001,
        "File must be loaded at preferred base address"),
    ("EXECUTABLE_IMAGE", 0x0002,
        "Image file can be executed"),
    ("LINE_NUMS_STRIPPED", 0x0004,
        "Deprecated - should be zero"),
    ("LOCAL_SYMS_STRIPPED", 0x0008,
        "Deprecated - should be zero"),
    ("AGGRESSIVE_WS_TRIM", 0x0010,
        "Aggressively trim working set - obsolete for win>2000"),
    ("LARGE_ADDRESS_AWARE", 0x0020,
        "Address can handle > 2G addressess"),
    ("BYTES_REVERSED_LO", 0x0080,
        "Deprecated - should be zero"),
    ("32_BIT_MACHINE", 0x0100,
        "Machine is 32 bit"),
    ("DEBUG_STRIPPED", 0x0200,
        "Debugging information has been removed"),
    ("REMOVABLE_RUN_FROM_SWAP", 0x0400,
        "If on removable media, fully load and copy to swap file"),
    ("NET_RUN_FROM_SWAP", 0x0800,
        "If on newwork media, fully load and copy to swap file"),
    ("SYSTEM", 0x1000,
        "File is a system file not a user program"),
    ("DLL", 0x2000,
        "File is a dll"),
    ("UP_SYSTEM_ONLY", 0x4000,
        "Should only be run on a uniprocessor system only"),
    ("BYTES_REVERSED_HI", 0x8000,
        "Deprecated - should be zero"),
]

DLL_CHARACTERISTICS_MASK = [
    ("DYNAMIC_BASE", 0x0040,
        "DLL can be relocated at load time"),
    ("FORCE_INTEGRITY", 0x0080,
        "Code integrity checks enforced"),
    ("NX_COMPAT", 0x0100,
        "Image is NX compatible"),
    ("NO_ISOLATION", 0x0200,
        "Isolation aware, but do not isolate"),
    ("NO_SEH", 0x0400,
        "Does not use structured exxception handling"),
    ("NO_BIND", 0x0800,
        "Do not bind"),
    ("WDM_DRIVER", 0x2000,
        "A WDM driver"),
    ("TERMINAL_SERVER_AWARE", 0x8000,
        "DLL is terminal server aware"),
]

SECTION_CHARACTERISTICS_MASK = [
    ("TYPE_NO_PAD",            0x00000008,
        "Section should not be padded to the next boundry, replaced by ALIGN_1BYTES"),
    ("CNT_CODE",               0x00000020,
        "Executable code"),
    ("CNT_INITIALIZED_DATA",   0x00000040,
        "Initialized data"),
    ("CNT_UNINITIALIZED_DATA", 0x00000080,
        "Uninitialized data"),
    ("LNK_OTHER",              0x00000100,
        "Reserved"),
    ("LNK_INFO",               0x00000200,
        "Comments, valid for object files only"),
    ("LNK_REMOVE",             0x00000800,
        "Not part of image, valid for object files only"),
    ("LNK_COMDAT",             0x00001000,
        "Contains COMDAT data, valid for object files only"),
    ("GPREL",                  0x00008000,
        "Contains data referenced through global pointer (GP)"),
    ("MEM_PURGEABLE",          0x00020000,
        "Reserved"),
    ("MEM_LOCKED",             0x00040000,
        "Reserved"),
    ("MEM_PRELOAD",            0x00080000,
        "Reserved"),
    ("ALIGN_1BYTES",           0x00100000,
        "Align data on 1 byte boundary, valid for object files only"),
    ("ALIGN_2BYTES",           0x00200000,
        "Align data on 2 byte boundary, valid for object files only"),
    ("ALIGN_4BYTES",           0x00300000,
        "Align data on 4 byte boundary, valid for object files only"),
    ("ALIGN_8BYTES",           0x00400000,
        "Align data on 8 byte boundary, valid for object files only"),
    ("ALIGN_16BYTES",          0x00500000,
        "Align data on 16 byte boundary, valid for object files only"),
    ("ALIGN_32BYTES",          0x00600000,
        "Align data on 32 byte boundary, valid for object files only"),
    ("ALIGN_64BYTES",          0x00700000,
        "Align data on 64 byte boundary, valid for object files only"),
    ("ALIGN_128BYTES",         0x00800000,
        "Align data on 128 byte boundary, valid for object files only"),
    ("ALIGN_256BYTES",         0x00900000,
        "Align data on 256 byte boundary, valid for object files only"),
    ("ALIGN_512BYTES",         0x00A00000,
        "Align data on 512 byte boundary, valid for object files only"),
    ("ALIGN_1024BYTES",        0x00B00000,
        "Align data on 1024 byte boundary, valid for object files only"),
    ("ALIGN_2048BYTES",        0x00C00000,
        "Align data on 2048 byte boundary, valid for object files only"),
    ("ALIGN_4096BYTES",        0x00D00000,
        "Align data on 4096 byte boundary, valid for object files only"),
    ("ALIGN_8192BYTES",        0x00E00000,
        "Align data on 8192 byte boundary, valid for object files only"),
    ("NRELOC_OVFL",            0x01000000,
        "Section contains extended relocations"),
    ("MEM_DISCARDABLE",        0x02000000,
        "Section can be discarded"),
    ("MEM_NOT_CACHED",         0x04000000,
        "Section cannot be cached"),
    ("MEM_NOT_PAGED",          0x08000000,
        "Section is not pageable"),
    ("MEM_SHARED",             0x10000000,
        "Section can be shared in memory"),
    ("MEM_EXECUTE",            0x20000000,
        "Section can be executed as code"),
    ("MEM_READ",               0x40000000,
        "Section can be read"),
    ("MEM_WRITE",              0x80000000,
        "Section can be written to"),
]

IMAGE_COFF_HDR_SPEC = [
    ("machine", 2,
        "Type of target machine"),
    ("number_of_sections", 2,
        "Number of sections"),
    ("time_date_stamp", 4,
        "Time the file was created"),
    ("pointer_to_symbol_table", 4,
        "File offset to coff symbol table - should be zero"),
    ("number_of_symbols", 4,
        "Number of symbols in the coff symbol table - should be zero"),
    ("size_of_optional_header", 2,
        "Should be zero for object files, valid for executables"),
    ("characteristics", 2,
        "Attributes of the file - see boolean values"),
]
IMAGE_COFF_HDR_STR = "=HHLLLHH"

IMAGE_DOS_HDR_SPEC = [
    ("magic", 2, "magic number"),
    ("cblp", 2, "Bytes on last page of file"),
    ("cp", 2, "Pages in file"),
    ("crlc", 2, "Relocations"),
    ("cparhdr", 2, "Size of header in paragraphs (should be 4)"),
    ("minalloc", 2, "Minimum extra paragraphs needed"),
    ("maxalloc", 2, "Maximum extra paragraphs needed"),
    ("ss", 2, "Initial relative ss value"),
    ("sp", 2, "Inital sp value"),
    ("csum", 2, "Checksum"),
    ("ip", 2, "Inital ip value"),
    ("cs", 2, "Inital relative cs value"),
    ("lfarlc", 2, "File address of relocation table"),
    ("ovno", 2, "Overlay number"),
    ("res", 8, "Reserved words"),
    ("oemid", 2, "OEM identifier"),
    ("oeminfo", 2, "OEM information"),
    ("res2", 20, "Reserved words"),
    ("lfanew", 4, "File address of new exe header")
]
IMAGE_DOS_HDR_STR = "=2sHHHHHHHHHHHHH8sHH20sL"

IMAGE_OPTIONAL_HDR_BASE_SPEC = [
    ("magic_type", 2,
        "0x10B = normal EXE, 0x107 = ROM image, 0x20B = PE32+ (64bit0)"),
    ("major_linker_version", 1,
        "Linker major version number"),
    ("minor_linker_version", 1,
        "Linker minor version number"),
    ("size_of_code", 4,
        "Size of code section or sum of all code sections if multiple"),
    ("size_of_initialized_data", 4,
        "Size of initialized data section or sum if multiple"),
    ("size_of_uninitialized_data", 4,
        "Size of uninitialized data section (BSS) or sum if multiple"),
    ("address_of_entry_point", 4,
        "RVA to entry of executable, init function for device drivers, and optional for dlls"),
    ("base_of_code", 4,
        "RVA to base of code section"),
]
IMAGE_OPTIONAL_HDR_BASE_STR = "=HBBLLLLL"

IMAGE_OPTIONAL_HDR_PE32_SPEC = [
    ("base_of_data", 4,
        "RVA to beginning of data section"),
    ("image_base", 4,
        "Preferred aaddress of image when loaded"),
    ("section_alignment", 4,
        "Alignment of sections in bytes when loaded into memory, >= file_alignment"),
    ("file_alignment", 4,
        "Alignment of sections in bytes in the image file (default is 512)"),
    ("major_os_version", 2,
        "OS major version number"),
    ("minor_os_version", 2,
        "OS minor version number"),
    ("major_image_version", 2,
        "Image major version number"),
    ("minor_image_version", 2,
        "Image minor version number"),
    ("major_subsystem_version", 2,
        "Subsystem major version number"),
    ("minor_subsystem_version", 2,
        "Subsystem minor version number"),
    ("win32_version", 4,
        "Reserved, must be 0"),
    ("size_of_image", 4,
        "Size of bytes in image as loaded in memory, must be multiple of section_alignment"),
    ("size_of_headers", 4,
        "Combined size of DOS Stub, PE header, and Section headers, rounded to multiple of file_alignment"),  # noqa
    ("checksum", 4,
        "Image file checksum as computed by imaghelp.dll"),
    ("subsystem", 2,
        "Subsystem rquired to run, see subsytem_description"),
    ("dll_characteristics", 2,
        "DLL characteristics - see boolean values"),
    ("size_of_stack_reserve", 4,
        "Memory reserved for stack"),
    ("size_of_stack_commit", 4,
        "Memory initially commited for the stack, additional pages added as needed"),
    ("size_of_heap_reserve", 4,
        "Memory reserved for local heap"),
    ("size_of_heap_commit", 4,
        "Memory initially commited for the local heap, additional pages added as needed"),
    ("loader_flags", 4,
        "Reserved - must be 0"),
    ("number_of_data_directories", 4,
        "Number of data directory entries following"),
]
IMAGE_OPTIONAL_HDR_PE32_STR = "=LLLLHHHHHHLLLLHHLLLLLL"

IMAGE_OPTIONAL_HDR_PE32_PLUS_SPEC = [
    ("image_base", 8,
        "Preferred address of image when loaded"),
    ("section_alignment", 4,
        "Alignment of sections in bytes when loaded into memory, >= file_alignment"),
    ("file_alignment", 4,
        "alignment of sections in bytes in the image file (default is 512)"),
    ("major_os_version", 2,
        "OS major version number"),
    ("minor_os_version", 2,
        "OS minor version number"),
    ("major_image_version", 2,
        "Image major version number"),
    ("minor_image_version", 2,
        "Image minor version number"),
    ("major_subsystem_version", 2,
        "Subsystem major version number"),
    ("minor_subsystem_version", 2,
        "Subsystem minor version number"),
    ("win32_version", 4,
        "Reserved, must be 0"),
    ("size_of_image", 4,
        "Size of bytes in image as loaded in memory, must be multiple of section_alignment"),
    ("size_of_headers", 4,
        "Combined size of DOS Stub, PE header, and Section headers, rounded to multiple of file_alignment"),  # noqa
    ("checksum", 4,
        "Image file checksum as computed by imaghelp.dll"),
    ("subsystem", 2, "Subsystem required to run, see subsytem_description"),
    ("dll_characteristics", 2,
        "DLL characteristics - see boolean values"),
    ("size_of_stack_reserve", 8,
        "Memory reserved for stack"),
    ("size_of_stack_commit", 8,
        "Memory initially commited for the stack, additional pages added as needed"),
    ("size_of_heap_reserve", 8,
        "Memory reserved for local heap"),
    ("size_of_heap_commit", 8,
        "Memory initially commited for the local heap, additional pages added as needed"),
    ("loader_flags", 4,
        "Reserved - must be 0"),
    ("number_of_data_directories", 4,
        "Number of data directory entries following"),
]
IMAGE_OPTIONAL_HDR_PE32_PLUS_STR = "=QLLHHHHHHLLLLHHQQQQLL"


DATA_DIRECTORY_SPEC = [
    ("export_table", 8,
        "The export table address and size"),
    ("import_table", 8,
        "The import table address and size"),
    ("resource_table", 8,
        "The resource table address and size"),
    ("exception_table", 8,
        "The exception table address and size"),
    ("certificate_table", 8,
        "The certificate table address and size"),
    ("base_relocation_table", 8,
        "The base relocation table address and size"),
    ("debug", 8,
        "The debug data address and size"),
    ("architecture", 8,
        "Reserved must be 0"),
    ("global_ptr", 8,
        "The RVA of the value to be stored in the global pointer register, size must be 0"),
    ("tls_table", 8,
        "The thread local storage table address and size"),
    ("load_config_table", 8,
        "The load configuration table address and size"),
    ("bound_import_table", 8,
        "The bound import table address and size"),
    ("IAT", 8,
        "The import address table address and size"),
    ("delay_import_table", 8,
        "The delay import descriptor address and size"),
    ("clr_runtime_header", 8,
        "The common language runtime header address and size"),
    ("reserved", 8,
        "Must be 0"),
]
DATA_DIRECTORY_STR = "=LL"  # (address, length)

SECTION_HEADER_SPEC = [
    # Size, Field, Description
    ("name", 8,
        "Name of the section"),
    ("virtual_size", 4,
        "Total size of the section loaded into memory, 0 for ojbect files"),
    ("virtual_address", 4,
        "Address of the first byte of the section relative to image base in memory"),
    ("size_of_raw_data", 4,
        "Size of the initialized data on disc, must be a multiple of file_alignment"),
    ("pointer_to_raw_data", 4,
        "File pointer to the first page of the section of the COFF file"),
    ("pointer_to_relocations", 4,
        "File pointer to the begining of the relocations for the sections, 0 for executables"),
    ("pointer_to_line_numbers", 4,
        "File pointer to the begining of the line numbers for the section, 0 for executables"),
    ("number_of_relocations", 2,
        "Number of relocation entries for the section, 0 for executables"),
    ("number_of_line_numbers", 2,
        "Number of line numbers for the section, 0 for executables"),
    ("characteristics", 4,
        "Characteristics of the section"),
]
SECTION_HEADER_STR = "=8sLLLLLLHHL"

EXPORTS_DIRECTORY_TABLE_SPEC = [
    ("export_flags", 4, "Reserved must be 0"),
    ("time_date_stamp", 4, "Time date the export was created"),
    ("major_version", 2, "Major version number"),
    ("minor_version", 2, "Minor version number"),
    ("name_rva", 4, "RVA of the name of the DLL"),
    ("ordinal_base", 4, "Starting ordinal number usually set to 1"),
    ("address_table_entries", 4, "Number of entries in the address table"),
    ("number_of_name_pointers", 4, "Number of entries in the name pointer table"),
    ("export_address_table_rva", 4, "Address of the export address table"),
    ("name_pointer_rva", 4, "Address of the export name pointer table"),
    ("ordinal_table_rva", 4, "Address of the ordinal table"),
]
EXPORTS_DIRECTORY_TABLE_STR = "=LLHHLLLLLLL"

EXPORTS_ADDRESS_TABLE_SPEC = [
    ("address", 4, "Address of the exported function or name of forwarded DLL"),
]
EXPORTS_ADDRESS_TABLE_STR = "=L"

EXPORTS_NAME_POINTER_TABLE_SPEC = [
    ("name_pointer", 4, "Address of the name"),
]
EXPORTS_NAME_POINTER_TABLE_STR = "=L"

EXPORTS_ORDINAL_TABLE_SPEC = [
    ("ordinal", 2, "Ordinal value for the address of the export"),
]
EXPORTS_ORDINAL_TABLE_STR = "=H"

BASE_RELOCATION_BLOCK_SPEC = [
    ("page_rva", 4, "Image base + page RVA + offset = address of base relocation"),
    ("block_size", 4, "Total number of bytes in the base relocation block"),
]
BASE_RELOCATION_BLOCK_STR = "=LL"

BASE_RELOCATION_SPEC = [
    ("type_offset", 2, "First 4 bits is the type followed by 12 bits of offset"),
]
BASE_RELOCATION_STR = "=H"

DELAY_IMPORT_TABLE_SPEC = [
    ("attributes", 4,
        "Must be 0"),
    ("name_rva", 4,
        "RVA of the name of the DLL to be loaded"),
    ("module_handle", 4,
        "RVA of the module handle to be loaded"),
    ("delay_import_address_table", 4,
        "RVA of the delay load import address table"),
    ("delay_import_name_table", 4,
        "RVA of the delay import name table"),
    ("bound_delay_import_table", 4,
        "RVA of the bound delay load address table, if it exists"),
    ("unload_delay_import_table", 4,
        "RVA of the bound delay unload address table, should be an exact copy of the delay IAT"),
    ("timestamp", 4,
        "Timestamp of the DLL to which the image has been bound"),
]
DELAY_IMPORT_TABLE_STR = "=LLLLLLLL"

IMPORT_TABLE_SPEC = [
    ("import_lookup_table", 4,
        "RVA of import lookup table, containing name or ordinal for each import"),
    ("time_date_stamp", 4,
        "Time and date, 0 until bound then set to values for the DLL"),
    ("forwarder_chain", 4,
        "Index of first forwarder reference"),
    ("name_rva", 4,
        "RVA of the ASCII string containing the name of the DLL"),
    ("import_address_table", 4,
        "RVA of import address table, identical to import_lookup_table until image is bound"),
]
IMPORT_TABLE_STR = "=LLLLL"

IMPORT_LOOKUP_TABLE_32_SPEC = [
    ("name_or_ordinal", 4,
        "If first bit is set, ordinal number, otherwise RVA to name"),
]
IMPORT_LOOKUP_TABLE_32_STR = "=L"

IMPORT_LOOKUP_TABLE_64_SPEC = [
    ("name_or_ordinal", 8,
        "If first bit is set, ordinal number, otherwise RVA to name"),
]
IMPORT_LOOKUP_TABLE_64_STR = "=Q"

CERTIFICATE_TABLE_SPEC = [
    ("length", 4, "Length of the certificate"),
    ("revision", 2, "Certificate version number"),
    ("type", 2, "Type of the content"),
]
CERTIFICATE_TABLE_STR = "=LHH"
