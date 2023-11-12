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

import logging

from typing import List, Optional, Tuple

NAME = "macho"
logger = logging.getLogger(NAME)


class UniversalRepr:
    def __init__(self, header: dict) -> None:
        self.known_format: bool = False
        self.type: str = "MACHO"

        self.set_magic(header)
        self.set_big_endian(header)
        self.set_num_embedded(header)
        self.set_embedded(header)
        self.section_info = []

    def set_magic(self, header: dict) -> None:
        self.magic = header["magic"]

    def set_big_endian(self, header: dict) -> None:
        self.big_endian = header["big_endian"]

    def set_num_embedded(self, header: dict) -> None:
        self.num_embedded = header["nfat_arch"]

    def set_embedded(self, header: dict) -> None:
        embedded = header["embedded"]
        self.embedded = []
        for f in embedded:
            self.embedded.append(MachoRepr(f))

    def get_entries(self) -> List[int]:
        return []


class MachoRepr:
    def __init__(self, header: dict) -> None:
        """ Initialize this object to have all of the members needed by the object_header
            module.
        """
        self.type = "MACHO"
        self.known_format = True
        self.image_base = 0  # FIXME: UNDEFINED
        self.image_size = 0  # FIXME: UNDEFINED
        self.code_size = 0  # FIXME: UNDEFINED
        self.code_base = 0  # FIXME: UNDEFINED
        self.data_base = 0  # FIXME: UNDEFINED
        self.file_alignment = 0  # FIXME: UNDEFINED
        self.image_version = 0  # FIXME: UNDEFINED
        self.linker_version = 0  # FIXME: UNDEFINED
        self.os_version = 0  # FIXME: UNDEFINED

        self.set_magic(header)
        self.set_insn_mode(header)
        self.set_machine(header)
        self.set_uuid(header)
        self.set_big_endian(header)
        self.set_header_offset(header)
        self.set_file_end(header)
        self.set_entries(header)
        self.set_imports(header)

        self.section_info = self.get_section_info(header)
        self.section_names = list(self.section_info.keys())

    def set_magic(self, header: dict) -> None:
        self.magic = header["magic"]

    def set_insn_mode(self, header: dict) -> None:
        self.insn_mode = header["addr_size"]

    def set_machine(self, header: dict) -> None:
        self.machine = header["cputype"]

    def set_uuid(self, header: dict) -> None:
        self.uuid = header["uuid"]

    def set_big_endian(self, header: dict) -> None:
        self.big_endian = header["big_endian"]

    def set_header_offset(self, header: dict) -> None:
        self.header_offset = header["header_offset"]

    def get_last_segment(self, header: dict) -> Optional[str]:
        last_segment_offset = 0
        last_segment_size = 0
        last_segment = None
        segments = header["segments"]
        for segment_name, segment_info in segments.items():
            offset = segment_info["fileoff"]
            size = segment_info["filesize"]
            if offset > last_segment_offset:
                last_segment = segment_name
                last_segment_offset = offset
                last_segment_size = size

        return last_segment

    def set_file_end(self, header: dict) -> None:
        last_segment = self.get_last_segment(header)
        if last_segment is None:
            self.file_end = None
            return

        header_offset = header["header_offset"]
        last_segment_offset = header["segments"][last_segment]["fileoff"]
        last_segment_size = header["segments"][last_segment]["filesize"]

        self.file_end = header_offset + last_segment_offset + last_segment_size

    def set_entries(self, header) -> None:
        self.entries = [header["entry_point"]]

    def get_entry_points(self) -> List[int]:
        return self.entries

    def get_section_info(self, header):
        """ Given a Macho-O header object return a sections object that conforms to the
            format used by the object_header module
        """
        section_info = {}
        segments = header["segments"]

        for seg in segments:
            for s in segments[seg]["sections"]:
                section_info[s] = {}

                section_info[s]["section_offset"] = segments[seg]["sections"][s]["offset"]
                section_info[s]["section_addr"] = segments[seg]["sections"][s]["addr"]
                section_info[s]["section_len"] = segments[seg]["sections"][s]["size"]

                flags = segments[seg]["sections"][s]["flags"]
                section_info[s]['flags'] = flags
                if ( "ATTR_PURE_INSTRUCTIONS" in flags or
                     "ATTR_SOME_INSTRUCTIONS" in flags or
                     "ATTR_SELF_MODIFYING_CODE" in flags):
                    section_info[s]["section_exec"] = True
                else:
                    section_info[s]["section_exec"] = False

        return section_info

    def get_insn_mode(self, header: dict) -> int:
        return header["addr_size"]

    def set_image_version(self, header: dict) -> int:
        self.image_version = 0 # FIXME

    def set_os_version(self, header: str) -> str:
        self.os_version = "" # FIXME

    def set_imports(self, header) -> dict:
        self.imports = header["imports"]

    def set_symbols(self, header) -> None:
        self.symbols = ""  # FIXME

    def get_non_code_chunks_of_section(self, section: dict) -> List[Tuple[int, int]]:
        return []  # FIXME

    def get_code_chunks_of_section(self, section: dict) -> List[Tuple[int, int]]:
        return [(section['section_offset'], section['section_len'])]  # FIXME

    def get_image_size(self, header: dict) -> int:
        return 0 # FIXME

    def get_data_size(self, header: dict) -> int:
        return 0 # FIXME

    def get_code_size(self, header: dict) -> int:
        return 0 # FIXME

    def is_64bit(self) -> bool:
        return self.insn_mode == 64

    def get_code_base(self, header: dict) -> int:
        return 0 # FIXME

    def get_image_base(self, header: dict) -> int:
        return 0 # FIXME

    def find_section(self, vaddr: int) -> Optional[dict]:
        """ Given an address return the section that the address resides in
        """
        sections = self.section_info
        if not sections:
            return None

        for _, sec_info in sections.items():
            beg = sec_info["section_addr"]
            end = sec_info["section_addr"] + sec_info["section_len"]
            if beg <= vaddr <= end:
                return sec_info
        return None

    def get_offset(self, vaddr: int, loaded_image_base: Optional[int] = None) -> Optional[int]:
        """ Returns physical offset of virtual address given.
            TODO:: if loaded_image_base provided, overwrite parsed image_base
        """
        if not vaddr:
            return vaddr

        if loaded_image_base:
            # FIXME: this should come from file command table
            self.image_base = loaded_image_base

        offset = None
        # get section containing vaddr
        section_info = self.find_section(vaddr)
        if section_info:
            offset = section_info['section_offset'] + (vaddr - section_info['section_addr'])

        return offset

    def get_rva(self, offset: int) -> Optional[int]:
        """
        Returns relative virtual address of physical offset.
        """
        rva = None
        for n in self.section_names:
            ofs = self.section_info[ n ]['section_offset']
            end = ofs + self.section_info[ n ]['section_len']
            if ofs <= offset < end: # rva occurs in this section
                begin_va = self.section_info[ n ]['section_addr']
                rva = begin_va + (offset - ofs)
                break
        return rva
