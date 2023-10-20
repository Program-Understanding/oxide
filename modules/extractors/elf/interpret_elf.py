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

""" interpret_elf.py
elf representation standardized between elf/pe/macho
"""
NAME = "elf"
import logging

from typing import Optional

logger = logging.getLogger(NAME)
logger.debug("init")


class ElfRepr:
    def __init__(self, header: dict) -> None:
        """ Initialize this object to have all of the members needed by the object_header
            module.
        """
        # https://www.sco.com/developers/gabi/1998-04-29/ch4.eheader.html
        self.type = "ELF"
        self.set_type(header)
        self.set_machine(header)
        self.set_image_version(header)
        self.set_entry(header)
        self.set_os_version(header)
        self.set_endian(header)
        self.set_imports(header)
        self.set_symbols(header)

        self.insn_mode = self.get_insn_mode(header)
        self.image_base = self.get_image_base(header)
        self.image_size = self.get_image_size(header)
        self.code_size = self.get_code_size(header)
        self.code_base = self.get_code_base(header)
        self.data_size = self.get_data_size(header)
        self.section_info = self.get_section_info(header)
        self.section_names = list(self.section_info.keys())

        self.non_code_chunks = set()  # TODO:: Not sure how to do this for an ELF file
        self.file_alignment = ""  # ELF has alignment for segments but not for the file as a whole
        self.linker_version = ""  # ELF doesn't have this field
        self.data_base = 0  # ELF doesn't have this field
        self.delay_imports = None  # ELF doesn't have delay imports

    def set_entry(self, header: dict) -> None:
        self.entry = header["elf_header"]["entry"]

    def set_image_version(self, header: dict) -> None:
        self.image_version = header["elf_header"]["version"]

    def set_machine(self, header: dict) -> None:
        code = header["elf_header"]["machine"]
        if code in ("AMD x86-64 architecture", "Intel 80386"):
            self.machine = "x86"
        elif code in ["ARM", "ARM AARCH64"]:
            self.machine = "ARM"
        else:
            self.machine = "Unknown"

    def set_type(self, header: dict) -> None:
        self.etype = header["elf_header"]["type"]

    def set_os_version(self, header: dict) -> None:
        self.os_version = header["elf_header"]["osabi"]

    def set_endian(self, header: dict) -> None:
        if header["elf_header"]["data"] == "BigEndian":
            self.big_endian = True
            self.known_format = True
        elif header["elf_header"]["data"] == "LittleEndian":
            self.big_endian = False
            self.known_format = True
        else:
            self.big_endian = None
            self.known_format = False

    def set_imports(self, header: dict) -> None:
        self.imports = header["imports"] if "imports" in header else None
        self.dyn_imports = header["dyn_imports"] if "dyn_imports" in header else None

    def set_symbols(self, header: dict) -> None:
        self.symbols = header["symbols"] if "symbols" in header else None
        self.dyn_symbols = header["dyn_symbols"] if "dyn_symbols" in header else None

    def get_section_info(self, header: dict) -> dict:
        """ Given an ELF header object return a sections object that conforms to the format
            used by the object_header module
        """
        sections = header["section_table"]
        if not sections:
            return {}

        section_info = {}
        for sec_name, sec_info in sections.items():
            section_info[sec_name] = {}
            for field in sec_info:
                # rename some fields
                if field == "offset":
                    section_info[sec_name]["section_offset"] = sec_info[field]
                elif field == "addr":
                    section_info[sec_name]["section_addr"] = sec_info[field]
                elif field == "size":
                    section_info[sec_name]["section_len"] = sec_info[field]
                else:
                    section_info[sec_name][field] = sec_info[field]

            # easily accesible flag on whether section is executable
            if "EXECINSTR" in sections[sec_name]["flags"]:
                section_info[sec_name]["section_exec"] = True
            else:
                section_info[sec_name]["section_exec"] = False

        return section_info

    def get_entry_points(self) -> list:
        return [self.entry]  # FIXME

    def get_non_code_chunks_of_section(self, section: dict) -> list:
        return []  # FIXME

    def get_code_chunks_of_section(self, section: dict) -> list:
        return [(section["section_offset"], section["section_len"])]  # FIXME

    def get_insn_mode(self, header) -> Optional[int]:
        """ If this file is 32-bit return the integer 32,
            if this file is 64-bit return the integer 64,
            return None otherwise
        """
        insn_mode = None
        if header["elf_header"]["class"] == "32-bit":
            insn_mode = 32
        elif header["elf_header"]["class"] == "64-bit":
            insn_mode = 64
        return insn_mode

    def get_image_size(self, header: dict) -> int:
        """ Return the cumulative size of the segments (sections mapped into memory)
        """
        size = 0
        if not header["segments"]: return size
        for _, segment_info in header["segments"].items():
            size += segment_info["filesz"]
        return size

    def get_data_size(self, header: dict) -> int:
        """ Return the cumulative size of the 'non-code' segments
        """
        size = 0
        segments = header["segments"]
        if segments:
            for _, segment_info in segments.items():
                if "EXECUTE" not in segment_info["flags"]:
                    size += segment_info["filesz"]
        return size

    def get_code_size(self, header: dict) -> int:
        """ Return the cumulative size of the 'code' segments
        """
        size = 0
        segments = header["segments"]
        if segments:
            for _, segment_info in segments.items():
                if "EXECUTE" in segment_info["flags"]:
                    size += segment_info["filesz"]
        return size

    def is_64bit(self) -> bool:
        """ Return True if this file 64 bit and False otherwise
        """
        return self.insn_mode == 64

    def get_code_base(self, header: dict) -> int:
        """ Return the starting address of the section where the entry point resides
        """
        code_base = 0  # should not result in 0
        entry = header["elf_header"]["entry"]
        sections = header["section_table"]
        if sections:
            for _, section_info in sections.items():
                beg = section_info["addr"]
                end = section_info["addr"] + section_info["size"]
                if entry >= beg and entry < end:
                    code_base = beg
                    break
        return code_base

    def get_image_base(self, header: dict) -> int:
        """ first section address - first section offset
            TODO:: refactor
        """
        image_base = 0
        first_sec = None
        first_addr = None
        sections = header["section_table"]
        if sections:
            for sec_name, sec_info in sections.items():
                this_addr = sec_info['addr']
                if not first_sec or (this_addr != 0 and this_addr < first_addr):
                    first_sec = sec_name
                    first_addr = this_addr
            if not first_sec:
                return 0   # no sections found, call the image base 0.
            offset = sections[first_sec]['offset']
            addr = sections[first_sec]['addr']
            image_base = addr - offset
        return image_base

    def find_section(self, vaddr: int) -> Optional[dict]:
        """ Given an address return the section that the address resides in
        """
        found_section = None
        sections = self.section_info

        if sections:
            for _, section_info in sections.items():
                beg = section_info["section_addr"]
                end = section_info["section_addr"] + section_info["section_len"]
                if beg <= vaddr <= end:
                    found_section = section_info
                    break
        return found_section

    def get_offset(self, vaddr: int, loaded_image_base: Optional[int] = None) -> Optional[int]:
        """ Returns file offset of virtual address given.
        """
        offset = None
        if vaddr is None:
            return offset

        info = self.find_section(vaddr)
        if info:
            offset = info['section_offset'] + (vaddr - info['section_addr'])
        return offset

    def get_rva(self, offset: int) -> Optional[int]:
        """
        Returns relative virtual address of physical offset.
        """
        rva = None
        sections = self.section_info

        if sections:
            for _, section_info in sections.items():
                ofs = section_info['section_offset']
                end = ofs + section_info['section_len']
                if ofs <= offset < end:
                    # rva occurs in this section
                    begin_va = section_info['section_addr']
                    rva = begin_va + (offset - ofs)
                    break
        return rva
