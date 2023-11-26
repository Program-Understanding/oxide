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

""" interpret_pe.py
"""
import logging

from typing import Optional, List, Tuple, Set

NAME = "pe_interpret"
logger = logging.getLogger(NAME)


class PeRepr:
    """ Wrapper object for PECOFF binary
    """
    def __init__(self, pe: dict) -> None:
        """ Interpret PE dictionary object into standard format
        """
        self.big_endian   = False
        self.known_format = True
        self.type = "PE"

        # determine whether this is a 32 or 64 bit PE; condition TRUE => 64
        # can examine pe.FILE_HEADER.Machine or pe.FILE_HEADER.Characteristics
        if pe["coff_header"]:
            #   pe.FILE_HEADER.Characteristics & 0x0100 == 0
            self.insn_mode = 64 if (pe["coff_header"]["characteristics"]["32_BIT_MACHINE"] == 0) else 32
            if pe["coff_header"]["machine_description"] == "Intel 386":
                self.machine = "x86"
            elif pe["coff_header"]["machine_description"] == "ARM or Thumb":
                self.machine = "ARM"
            else:
                self.machine = "Unknown"
        else:
            self.insn_mode = 32
            self.machine = "Unknown"

        if pe["optional_header"]:
            self.image_base = pe["optional_header"]["image_base"]  # pe.OPTIONAL_HEADER.ImageBase
            self.image_size = pe["optional_header"]["size_of_image"]  # pe.OPTIONAL_HEADER.SizeOfImage
            self.code_size = pe["optional_header"]["size_of_code"]  # pe.OPTIONAL_HEADER.SizeOfCode
            self.code_base = pe["optional_header"]["base_of_code"]  # pe.OPTIONAL_HEADER.BaseOfCode
            if "base_of_data" in pe["optional_header"]:
                self.data_base = pe["optional_header"]["base_of_data"]  # pe.OPTIONAL_HEADER.BaseOfData
            else:
                self.data_base = 0
            self.file_alignment = pe["optional_header"]["file_alignment"]  # pe.OPTIONAL_HEADER.FileAlignment
            self.image_version = "{}.{}".format(pe["optional_header"]["major_image_version"], pe["optional_header"]["minor_image_version"])
            self.linker_version = "{}.{}".format(pe["optional_header"]["major_linker_version"], pe["optional_header"]["minor_image_version"])
            self.os_version = "{}.{}".format(pe["optional_header"]["major_os_version"], pe["optional_header"]["minor_os_version"])
        else:
            self.image_base = 0
            self.image_size = 0
            self.code_size = 0
            self.code_base = 0
            self.data_base = 0
            self.file_alignment = 1
            self.image_version = "N/A"
            self.linker_version = "N/A"
            self.os_version = "N/A"

        if "import_table" in pe:
            self.imports = pe["import_table"]  # pe.DIRECTORY_ENTRY_IMPORT
        else:
            self.imports = None

        if "delay_import_table" in pe:
            self.delay_imports = pe["delay_import_table"]
        else:
            self.delay_imports = None

        # Update members
        self.update_sections(pe)
        self.update_entry_points(pe)
        self.update_symbols(pe)

    def update_sections (self, pe: dict) -> None:
        """ Given PE dictionary, update section info dictionary, and section name list
        """
        self.section_info = dict()

        # image_base = 0
        # if (hasattr (pe, 'OPTIONAL_HEADER') and
        #     hasattr(pe.OPTIONAL_HEADER, 'ImageBase')):
        #     image_base = pe.OPTIONAL_HEADER.ImageBase

        # No valid section table.  Assume section is hiding in header, create fake section.
        if "section_table" not in pe or not pe["section_table"]:
            self.section_names = ["N/A"]
            self.section_info["N/A"] = {'name'           : 'n/a',
                                        'section_offset' : 0,
                                        'section_addr'   : 0,
                                        'section_len'    : self.image_size,
                                        'section_end'    : self.image_size,
                                        'section_exec'   : True}
            return

        names: dict = {}
        for n in pe["section_table"]:  # pe.sections:
            s = pe["section_table"][n]
            offset = s["pointer_to_raw_data"]  # pe.get_offset_from_rva(s["virtual_address"]) #s.VirtualAddress )
            name = s["name"]

            # make sure name is uniq; if not label it with an int
            if name in names:
                # is not uniq
                names[name] += 1
                fixed_name = "{}-dupe-{}".format(name, names[name])
                logger.warning("duplicate section names in binary - '%s' renamed to '%s'", name, fixed_name)
            else:
                # is uniq
                names[name] = 0
                fixed_name = name

            # update section info for section name (TODO::resolve collisions?)
            self.section_info [fixed_name] = {'name'           : fixed_name,
                                              'section_offset' : offset,
                                              'section_addr'   : s["virtual_address"],
                                              'section_len'    : s["size_of_raw_data"],
                                              'section_end'    : s["virtual_address"] + s["size_of_raw_data"],
                                              # if charactistic true, add to list
                                              'flags'          : [c for c in s["characteristics"] if s["characteristics"][c]],
                                              'section_exec'   : s["characteristics"]["MEM_EXECUTE"] > 0}

        # Update list of section names
        self.section_names = list(self.section_info.keys())

    def update_entry_points(self, pe: dict) -> None:
        """ Given PE object, update entry_addrs field with exported addresses (entry + exports)
        """
        addrs = set()
        if pe["optional_header"]:
            addrs.add(pe["optional_header"]["address_of_entry_point"])
        if "exports_directory_table" in pe and pe["exports_directory_table"]:
            for export_name in pe["exports_directory_table"]["export_names"]:
                addr = pe["exports_directory_table"]["export_names"][export_name]
                addrs.add(addr)
        self.entry_addrs = addrs

    def update_symbols(self, pe: dict) -> None:
        """ Gets the import/delay import for a PE program, and updates symbol_table field
        """
        sym_tab = dict()

        # aggregate import symbols
        if "import_table" in pe and pe["import_table"]:
            imps = pe["import_table"]
            for i in imps:
                if imps[i]["addresses"]:
                    for a in imps[i]["addresses"]:
                        sym_tab[a] = {'dll' : i,
                                      'name' : imps[i]["addresses"][a]}

        # aggregate delayed import symbols
        if "delay_import_table" in pe and pe["delay_import_table"]:
            imps = pe["delay_import_table"]
            for i in imps:
                if imps[i]["addresses"]:
                    for a in imps[i]["addresses"]:
                        sym_tab[a] = {'dll' : i,
                                      'name' : imps[i]["addresses"][a]}

        self.symbol_table = sym_tab

    def is_64bit(self) -> bool:
        """ Whether this class represents 32 or 64 bit executable.
        """
        return (self.insn_mode == 64)

    def find_section(self, vaddr: int) -> Optional[dict]:
        """ Section info that encompasses virtual address provided, None if no matching

        Args:
            vaddr: int - virtual address being queried

        known issue:
            whether to use RVA or virtual address
            pe_bit_shifts_vs_32.exe requires RVA
        """
        rva = vaddr - self.image_base
        for name in self.section_names:
            logger.debug("Checking %s for addr %s", name, vaddr)
            start = self.section_info[name]['section_addr']
            if rva < start: continue
            end = self.section_info[name]['section_end']
            if start <= rva < end:
                return self.section_info[name]
        return None

    def get_code_chunks_of_section(self, section: dict) -> List[Tuple[int, int]]:
        """ List of tuples (offset, len) of portions of section that are
            not found in self.non_code_chunks.
        """
        chunks = []

        non_code_chunks = getattr(self, 'non_code_chunks', None)
        # if not hasattr (self, ) or not self.non_code_chunks:
        if not non_code_chunks:
            return [ (section['section_offset'], section['section_len']) ]

        # self.non_code_chunks is sorted by offset
        last = section['section_offset']
        last_chunk_in_section = False

        section_start_ofs = section['section_offset']
        section_end_ofs   = section_start_ofs + section['section_len']
        logger.debug ("Section ranges [0x%x,0x%x]", section_start_ofs, section_end_ofs)

        for nx in non_code_chunks:  # iter over "non-exec" chunks
            # is this chunk completely inside this section?
            logger.debug ("Is %r in section %r?", nx, section)

            if not (section['section_addr'] <= nx['addr'] and nx['end'] <= section['section_end']):
                logger.debug ("no")
                last_chunk_in_section = False
                continue

            # this is a block of non-code in this section
            last_chunk_in_section = True

            # if "last" is before the start of this block, then record code block
            if last < nx['ofs']:
                chunk_len = nx['ofs'] - last
                chunks.append ((last, chunk_len))
                logger.debug ("Adding (0x%x=%d, %d) as exec chunk", last, last, chunk_len)

            # unconditionally advance last past block
            last = nx['ofs'] + nx['len']

        # add the end of the section, too
        if last_chunk_in_section:
            # chunk between last and end of section is code
            section_end_ofs = section['section_offset'] + section['section_len']
            chunk_size = section_end_ofs - last

            if chunk_size > 0:
                chunks.append ((last, section_end_ofs-last))

        logger.debug ("Found these code chunks: %r", chunks)
        return chunks

    def get_entry_points(self) -> Set[int]:
        """ List entry points (OEP + exports)
        """
        return self.entry_addrs

    def get_offset(self, vaddr: int, loaded_image_base: Optional[int] = None) -> Optional[int]:
        """ File offset of virtual address given.

        Args:
            vaddr: int - virtual address being queried
            loaded_image_base - in cases where image differs from header hints
        """
        if loaded_image_base is None:
            loaded_image_base = self.image_base
        image_diff = self.image_base - loaded_image_base  # TODO:: positive or negative okay?
        adjusted_vaddr = vaddr - image_diff  # difference in requested and tool loaded
        info = self.find_section(adjusted_vaddr)
        if info and adjusted_vaddr > self.image_base:
            offset = info['section_offset'] + (adjusted_vaddr - info['section_addr'] - self.image_base)
        else:
            # Case were no section was found to offset into
            # This does not handle data outside of sections
            # offset = info['section_offset'] + adjusted_vaddr - info['section_addr']
            offset = None
        return offset

    def get_rva(self, offset: int) -> Optional[int]:
        """ Returns relative virtual address of file offset.

        Args:
            offset: int - file offset being queried.
        """
        rva = None
        for section_name in self.section_names:
            logger.debug("looking for %s in section %s", offset, section_name)
            ofs = self.section_info[section_name]['section_offset']
            end = ofs + self.section_info[section_name]['section_len']
            if ofs <= offset < end: # rva occurs in this section
                begin_va = self.section_info[section_name]['section_addr']
                rva = begin_va + (offset - ofs)
                break
        return rva
