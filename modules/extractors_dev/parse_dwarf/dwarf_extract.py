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

NAME = "dwarf_extract"

""" Implementation loosely based on readelf/pyelftools, but primarily https://dwarfstd.org/doc/DWARF4.pdf
"""

import logging
import struct
from typing import Optional, Tuple
from collections import defaultdict

logger = logging.getLogger(NAME)

from dwarf_enums import (DWARF_FORM_MAP_E, DWARF_TAG_MAP_E,
                         DWARF_LANGUAGE_MAP_E, DWARF_ATTR_MAP_E,
                         DWARF_OP_MAP_E, ADDRESS, BLOCK, CONSTANT,
                         EXPRLOC, FLAG, SEC_OFFSET,
                         RANGELISTPTR, RANGE, STRING, CU64_STR, CU32_STR,
                         DEBUG_LINE_64_STR, ADDR_FORM_32_STR, ADDR_FORM_64_STR,
                         DIE_STR, REFERENCE1_STR, REFERENCE2_STR, REFERENCE4_STR, REFERENCE8_STR,
                         DATA1_STR, DATA2_STR, DATA4_STR, DATA8_STR,
                         LINEPTR32_STR, LINEPTR64_STR)


# ------------------ Exported interface --------------------------------

class StateMachine():
    """ State Machine used in .debug_line
        Initializing state machine registers
    """
    def __init__(self) -> None:
        # Initialize with default values
        self.address = 0
        self.op_index = 0
        self.file = 1
        self.line = 1
        self.column = 0
        self.is_stmt = is_stmt
        self.basic_block = False
        self.end_sequence = False
        self.proloque_end = False
        self.epilogue_end = False
        self.isa = 0
        self.discriminator = 0

    def update_registers(self, curr_opcode: int) -> None:
        """ Update current line using index of current opcode
        """
        self.line += curr_opcode


# CU offset list used for grabbing .debug_info information
# from .debug_abbrev
offset_list = []


def _initialize_sections(data: bytes, sections: dict):
    """Initialize empty dicts for each dwarf section
    """
    dwarf_sections = {}
    for section_name, section_info in sections.items():
        if ".debug" in str(section_name):
            # Initializing empty dict for each dwarf section
            dwarf_sections[section_name] = section_info
            section_start = section_info["section_offset"]
            section_end = section_start + section_info["section_len"]
            dwarf_sections[section_name]["data"] = data[section_start: section_end]
    # copy of debug section info, and empty copy of parsed information
    return dwarf_sections


def _parse_debug_sections(dwarf_sections: dict) -> dict:
    """ Check common debug sections, and parse if present.
    """
    dwarf_parsed = {"sections": list(dwarf_sections.keys())}

    if ".debug_abbrev" in dwarf_sections:
        # ".debug_abbrev" section, defines types of entries in "debug_info"
        dwarf_parsed[".debug_abbrev"] = _extract_debug_abbrev(dwarf_sections)

    import pprint; pprint.pprint(dwarf_parsed[".debug_abbrev"])
    import sys; sys.exit()
    if ".debug_info" in dwarf_sections:
        # ".debug_info" section, primary index into other sections to describe debug information
        dwarf_parsed[".debug_info"] = _extract_debug_info(dwarf_sections, dwarf_parsed[".debug_abbrev"])
    """
    if ".debug_types" in dwarf_sections:
        dwarf_parsed[".debug_types"] = _extract_debug_types(dwarf_sections)

    if ".debug_pubnames" in dwarf_sections:
        dwarf_parsed[".debug_pubnames"] = _extract_debug_pubnames(dwarf_sections)

    if ".debug_pubtypes" in dwarf_sections:
        dwarf_parsed[".debug_pubtypes"] = _extract_debug_pubtypes(dwarf_sections)

    if ".debug_aranges" in dwarf_sections:
        dwarf_parsed[".debug_aranges"] = _extract_debug_aranges(dwarf_sections)

    if ".debug_line" in dwarf_sections:
        dwarf_parsed[".debug_line"] = _extract_debug_line(dwarf_sections)
    """
    return dwarf_parsed


def _extract_debug_abbrev(dwarf_sections: dict):
    """Extracts the abbreviation table that makes up the .debug_abbrev section
        Parsing ".debug_abbrev" section, since it's needed to decode information within "debug_info"
        Each CU has an abbreviation table
          DIE Offset
            Abbrev Number
            Attributes
            Tag
    """
    # results
    abbrev_decoded = defaultdict(dict)

    offset = 0
    abbrev_zero_count = 0
    cu_count = 0
    cu_offset = 0
    global max_abbrev
    max_abbrev = 0

    # section data
    debug_abbrev_data = dwarf_sections[".debug_abbrev"]["data"]

    die_index = 1

    # Keep track of attr_name, attr_form pairs
    while (True):
        attribute_list = []
        data, offset = _uleb128_of_stream(debug_abbrev_data, offset)

        abbrev_code = _decode_uleb128(data)

        # Abbrev code 0 signals end of CU abbrev table
        # More than one 0 signals end of abbrev section
        if (abbrev_code == 0):
            abbrev_zero_count += 1

            if abbrev_zero_count == 2:
                global total_cu
                total_cu = cu_count
                break

            continue

        abbrev_zero_count = 0

        # Keeping track of the max abbrev value for now
        if max_abbrev < abbrev_code:
            max_abbrev = abbrev_code

        die_offset = offset

        tag, has_children = struct.unpack(DIE_STR, debug_abbrev_data[offset: offset + struct.calcsize(DIE_STR)])

        # A DW_TAG_compile_unit tag means we've encountered a new CU
        if DWARF_TAG_MAP_E[tag] == "DW_TAG_compile_unit":
            cu_offset = offset - 1
            offset_list.append(cu_offset)
            cu_count += 1
            abbrev_decoded['compile_unit'][cu_offset] = {'dies': defaultdict(dict)}
        offset = offset + struct.calcsize(DIE_STR)

        # FIXME:: duplicate logic
        if has_children:
            # Sibling entry, each chain is terminated by a null entry
            # Series of attribute specification ends with an entry containing 0 for name and 0 for form
            # This might not always be true (refer to DWARFv4 pg. 159 for more info)

            # Abbrev attr, form dictionary population
            # attr_form determines how the attribute is encoded (which is found in debug_info)
            while (True):
                data, offset = _uleb128_of_stream(debug_abbrev_data, offset)
                attr_name = _decode_uleb128(data)

                data, offset = _uleb128_of_stream(debug_abbrev_data, offset)
                attr_form = _decode_uleb128(data)

                # Signals the end of the current DWARF tag information
                if (attr_name == 0 and attr_form == 0):
                    break

                attribute_list.append((DWARF_ATTR_MAP_E[attr_name], DWARF_FORM_MAP_E[attr_form]))

        else:
            # This will repeat name,form until we hit 0,0 (corresponding values should be in .debug_info
            # attr_form determines how the attribute is encoded (which is found in debug_info)
            while (True):
                data, offset = _uleb128_of_stream(debug_abbrev_data, offset)
                attr_name = _decode_uleb128(data)

                data, offset = _uleb128_of_stream(debug_abbrev_data, offset)
                attr_form = _decode_uleb128(data)

                # Signals the end of the current DWARF tag information
                if (attr_name == 0 and attr_form == 0):
                    break

                # debug attr_name, attr_form
                attribute_list.append((DWARF_ATTR_MAP_E[attr_name], DWARF_FORM_MAP_E[attr_form]))

        # debug tag is value
        abbrev_decoded['compile_unit'][cu_offset]['dies'][die_index] = {"tag": DWARF_TAG_MAP_E[tag],
                                                                        "offset": die_offset,
                                                                        "attributes": attribute_list}
        die_index += 1
    return abbrev_decoded


def _parse_debug_info_attributes(dwarf_sections: dict, debug_info_data: bytes, offset: int,
                                 abbrev_decoded: dict, info_abbrev: int, debug_abbrev_offset: int,
                                 addr_size: int, dwarf_format_64: bool) -> Tuple[list, int, int]:
    # Iterate through each attr pair in a CU, as per abbrev section
    attribute_list = []
    # loop through attributes of abbreviation to find fields of DIE
    for attr, form in abbrev_decoded['compile_unit'][debug_abbrev_offset]['dies'][info_abbrev]["attributes"]:
        # Which form class are we in?
        if form in ADDRESS:
            # From machine not from debug type 32 vs 64
            if addr_size == 8:
                addr_form = "Q"
            else:
                addr_form = "I"
            addr_form_size = struct.calcsize(addr_form)
            address_form_val = struct.unpack(addr_form, debug_info_data[offset:offset + addr_form_size])
            offset += addr_form_size
            attribute_list.append((attr, address_form_val[0]))

        elif form in BLOCK:
            """ Block forms are 1,2,4, or uLEB lengths, followed by the information bytes specified by that length
            """
            Block1_t = "B"
            Block2_t = "H"
            Block4_t = "I"

            if form == "DW_FORM_block1":
                block_length = struct.unpack(Block1_t, debug_info_data[offset:offset + 1])
                offset += 1
            elif form == "DW_FORM_block2":
                block_length = struct.unpack(Block2_t, debug_info_data[offset:offset + 2])
                offset += 2
            elif form == "DW_FORM_block4":
                block_length = struct.unpack(Block4_t, debug_info_data[offset:offset + 4])
                offset += 4
            elif form == "DW_FORM_block":
                data, offset = _uleb128_of_stream(debug_info_data, offset)
                block_length = _decode_uleb128(data)

            block_length = block_length[0]
            information_bytes = debug_info_data[offset:offset + block_length]
            offset += block_length

            attribute_list.append(tuple([attr, information_bytes]))

        elif form in CONSTANT:
            if form == "DW_FORM_data1":
                data1_form_val = struct.unpack(DATA1_STR, debug_info_data[offset:offset + 1])
                offset += 1
                data_form_val = data1_form_val[0]

            elif form == "DW_FORM_data2":
                data2_form_val = struct.unpack(DATA2_STR, debug_info_data[offset:offset + 2])
                offset += 2
                data_form_val = data2_form_val[0]

            elif form == "DW_FORM_data4":
                data4_form_val = struct.unpack(DATA4_STR, debug_info_data[offset:offset + 4])
                offset += 4
                data_form_val = data4_form_val[0]

            elif form == "DW_FORM_data8":
                data8_form_val = struct.unpack(DATA8_STR, debug_info_data[offset:offset + 8])
                offset += 8
                data_form_val = data8_form_val[0]
            print(offset)
            # TODO: resolve non-at_language attribute
            if attr == "DW_AT_language":
                attribute_list.append((attr, DWARF_LANGUAGE_MAP_E[data_form_val]))
            else:
                attribute_list.append((attr, data_form_val))

        elif form in EXPRLOC:
            print("DEBUG:: EXPRLOC")
            # uLEB128 number indicating length of following bytes to read
            data, offset = _uleb128_of_stream(debug_info_data, offset)
            # data, offset = bytearray(debug_info_data, offset)
            length = _decode_uleb128(data)

            if length == 1:
                exprloc_t = "B"
            elif length == 2:
                exprloc_t = "H"
            elif length == 4:
                exprloc_t = "I"
            elif length == 8:
                exprloc_t = "Q"
            else:
                # Length can be more than 9, will take a look at this soon
                raise AssertionError()

            print(length)
            exprloc_form_val = struct.unpack(exprloc_t, debug_info_data[offset:offset + length])
            exprloc_form_val = exprloc_form_val[0]
            offset += length
            # info_decoded[offset][info_abbrev][attr] = hex(exprloc_form_val)

        elif form in FLAG:
            print("DEBUG:: FLAG")
            flag_t = "B"

            if form == "DW_FORM_flag":
                # Expclicit, 0 indicates absence of attribute, 1 indicates flag exists
                flag_form_val = struct.unpack(flag_t, debug_info_data[offset:offset + 1])
                offset += 1
                attribute_list.append(tuple([attr, flag_form_val]))
            else:
                # Implicit, no value (flag exists)
                continue

        elif form in SEC_OFFSET:
            print("DEBUG:: SEC_OFFSET")
            # Refers to a location in the DWARF section that contains line number information
            # Includes macptr, lineptr, and loclist ptr
            if dwarf_format_64:
                secoffsetptr_t = LINEPTR64_STR
            else:
                secoffsetptr_t = LINEPTR32_STR
            lineptr_offset = struct.unpack(secoffsetptr_t, debug_info_data[offset:offset + struct.calcsize(secoffsetptr_t)])
            print(offset)
            offset += struct.calcsize(secoffsetptr_t)
            lineptr_offset = lineptr_offset[0]
            print(offset)
            attribute_list.append((attr, lineptr_offset))

            if ".debug_line" in dwarf_sections:
                continue

        elif form in RANGELISTPTR:
            rangelistptr_64_t = "Q"
            rangelistptr_32_t = "I"

            if dwarf_format_64:
                ranges_offset = struct.unpack(rangelistptr_64_t, debug_info_data[offset:offset + 8])
                offset += 8
            else:
                ranges_offset = struct.unpack(rangelistptr_32_t, debug_info_data[offset:offset + 4])
                offset += 4

            attribute_list.append(tuple([attr, ranges_offset]))

        elif form in STRING:
            # Sequence of contiguous non-null bytes followed by null byte
            STRP32_t = "I"
            STRP64_t = "Q"
            STR_t = "B"

            # String is located directly in DIE
            if form == "DW_FORM_string":
                check = 1
                str_val = []

                # Checking 1 byte at a time and appending to a list, ends with a null byte
                while check != 0:
                    str_char = struct.unpack(STR_t, debug_info_data[offset:offset + 1])
                    offset += 1
                    str_val.append(hex(str_char[0]))

                    if str_char[0] == 0:
                        check = 0

                # Convert hex list to string
                form_str = ''.join(chr(int(c, 16)) for c in str_val)
                attribute_list.append(tuple([attr, form_str]))

            elif form == "DW_FORM_strp":
                # DW_FORM_strp, offset into .debug_str section
                if dwarf_format_64:
                    strp_offset = struct.unpack(STRP64_t, debug_info_data[offset:offset + 8])
                    offset += 8
                else:
                    strp_offset = struct.unpack(STRP32_t, debug_info_data[offset:offset + 4])
                    offset += 4
                strp_offset = strp_offset[0]
                # Going into ".debug_str" and extracting attribute value
                if ".debug_str" in dwarf_sections:
                    str_val = ""

                # Checking 1 byte at a time and appending to a list, ends with a null byte
                while dwarf_sections[".debug_str"]["data"][strp_offset] != 0:
                    str_char = dwarf_sections[".debug_str"]["data"][strp_offset]
                    str_val += chr(str_char)
                    strp_offset += 1
                else:
                    str_val += chr(dwarf_sections[".debug_str"]["data"][strp_offset])

                attribute_list.append((attr, str_val))

        else:
            if form == "DW_FORM_ref1":
                ref_form_val = struct.unpack(REFERENCE1_STR, debug_info_data[offset:offset + 1])
                offset += 1
                ref_form_val = ref_form_val[0]
            elif form == "DW_FORM_ref2":
                ref_form_val = struct.unpack(REFERENCE2_STR, debug_info_data[offset:offset + 2])
                offset += 2
                ref_form_val = ref_form_val[0]
            elif form == "DW_FORM_ref4":
                ref_form_val = struct.unpack(REFERENCE4_STR, debug_info_data[offset:offset + 4])
                offset += 4
                ref_form_val = ref_form_val[0]
            elif form == "DW_FORM_ref8":
                ref_form_val = struct.unpack(REFERENCE8_STR, debug_info_data[offset:offset + 8])
                offset += 8
                ref_form_val = ref_form_val[0]
            elif form == "DW_FORM_strp":
                ref_form_val = struct.unpack(REFERENCE8_STR, debug_info_data[offset:offset + 8])
                offset += 8
                ref_form_val = ref_form_val[0]
            else:
                print("FIXME::", form)

            attribute_list.append((attr, ref_form_val))
    return attribute_list, offset


def _extract_debug_info(dwarf_sections: dict, abbrev_decoded: dict):
    """Extracts each CU's DIEs and their associated attribute pairs.
    Most of the DWARF information describing the program is contained
    within this section, or contains offsets into other (data) sections
    where the information can be extracted
    CU Offset
      DIE Offset
        Abbrev Number
        Attributes
        Tag
    """
    # result
    info_decoded = {'compile_unit': defaultdict(dict)}

    cu_count = 1
    cu_passed = 0
    offset = 0
    # info_abbrev_count = 0
    abbrev_zero_count = 0

    # section data
    debug_info_data = dwarf_sections[".debug_info"]["data"]

    # Peak at first 4, ffffffff is 64 bit dwarf format, while any other number is 32 bit
    dwarf_format_64 = (struct.unpack("I", debug_info_data[offset: offset + 4]) == 0xFFFFFFFF)
    if dwarf_format_64:
        logging.info("dwarf_format type 64")
        cu_str = CU64_STR
        offset += 4  # skip the ffffffff
    else:
        logging.info("dwarf_format type 32")
        cu_str = CU32_STR

    debug_info_header = struct.unpack(cu_str, debug_info_data[offset: offset + struct.calcsize(cu_str)])
    length, version, debug_abbrev_offset, addr_size = debug_info_header
    # initialize first CU, @ offset 0x0
    cu_offset = offset
    info_decoded['compile_unit'][cu_offset] = {'length': length, 'version': version, 'debug_abbrev_offset': debug_abbrev_offset, 'pointer_size': addr_size}
    info_decoded['compile_unit'][cu_offset]['dies'] = defaultdict(dict)
    # info_abbrev_offset = offset
    cu_offset = offset
    offset += struct.calcsize(cu_str)

    while offset < len(debug_info_data):
        # Info_abbrev is uLEB128 abbrev code, which is then followed by a series of attribute values
        # The abbreviation values for a CU end when an entry is 0
        info_abbrev_offset = offset
        data, offset = _uleb128_of_stream(debug_info_data, offset)
        info_abbrev = _decode_uleb128(data)
        print("offset, info_abbrev -> ", offset, info_abbrev)
        # Checking to see if there's a new CU
        if (info_abbrev == 0):
            abbrev_zero_count += 1

            # Checking the following abbrev value
            # This is used to determine if the next block is part of the same CU,
            # the next CU, or if the current CU is the last
            prev_offset = offset
            data, offset = _uleb128_of_stream(debug_info_data, offset)
            info_abbrev = _decode_uleb128(data)
            print(offset, info_abbrev)
            if (info_abbrev != 0) and (info_abbrev != 1) and (info_abbrev <= max_abbrev):
                offset = prev_offset
                continue
            elif info_abbrev == 0:
                offset = prev_offset
                break
            else:
                offset = prev_offset

            # 3 zero abbrev numbers in a row indicated end
            if (abbrev_zero_count == 3):
                break

            cu_count += 1
            cu_offset = offset
            cu_passed += 1
            debug_info_hdr = struct.unpack(cu_str, debug_info_data[offset: offset + struct.calcsize(cu_str)])
            length, version, debug_abbrev_offset, addr_size = debug_info_hdr
            offset += struct.calcsize(cu_str)
            info_decoded['compile_unit'][cu_offset] = {'length': length, 'version': version, 'dies': defaultdict(dict),
                                                       'debug_abbrev_offset': debug_abbrev_offset, 'pointer_size': addr_size}
            abbrev_zero_count = 0
            continue
        import pprint; pprint.pprint(info_decoded)

        attribute_list, offset = _parse_debug_info_attributes(dwarf_sections, debug_info_data, offset, abbrev_decoded, info_abbrev, debug_abbrev_offset, addr_size, dwarf_format_64)

        print(attribute_list)
        info_decoded['compile_unit'][cu_offset]['dies'][info_abbrev_offset] = {"tag": abbrev_decoded['compile_unit'][debug_abbrev_offset]["dies"][info_abbrev]["tag"],
                                                                               # "abbrev": abbrev_decoded['compile_unit'][offset_list[cu_count-1]]["dies"][attribute_list_tag_offset]["abbrev"],
                                                                               "attributes": attribute_list}
        print("DELETEME", info_decoded['compile_unit'][cu_offset]['dies'][info_abbrev_offset])
        print("DELETEME", offset, len(debug_info_data))

    return info_decoded


def _extract_debug_types(dwarf_sections: dict):
    """Parses the debug_types section. This section contains DIEs just as the .debug_info section does.
    """
    offset = 0
    dwarf_format_64 = struct.unpack("I", dwarf_sections[".debug_types"]["data"][offset: offset+4]) == 0xFFFFFFFF
    if dwarf_format_64:
        type_str = CU64_t
        offset += 4
    else:
        type_str = CU32_t
    length, version, abbrev, addr_size = struct.unpack(type_str, dwarf_sections[".debug_types"]["data"][offset: offset + struct.calcsize(type_str)])


def _extract_debug_pubnames(dwarf_sections: dict):
    """ Parses the .debug_pubtypes section which contains sets, where each set describes the names of
        global objects and functions whose definitions are represented by debugging information entries
        owned by a single compilation unit. Used for lookup by name.
        Used for "lookup by name". Consists of a table with sets of variable length entries, each
        describing names of global objects.
        Header
          Pair[Offset, Name]
    """
    PUBNAME_64_STR = "QHQQ"
    PUBNAME_32_STR = "=IHII"

    offset = 0
    dwarf_format_64 = struct.unpack("I", dwarf_sections[".debug_pubnames"]["data"][offset: offset+4]) == 0xFFFFFFFF
    if dwarf_format_64:
        pubname_str = PUBNAME_64_STR
        offset += 4
    else:
        pubname_str = PUBNAME_32_STR
    length, version, debug_info_offset, debug_info_length = struct.unpack(pubname_str, dwarf_sections[".debug_pubnames"]["data"][offset: offset + struct.calcsize(CU_t)])
    offset += struct.calcsize(pubname_str)

    # Following the header is a variable number of offset/name pairs
    pubnames_decoded["header"] = {"Length:": length, "Version:": version, "Offset in .debug_info:": debug_info_offset, "Area size in .debug_info:": debug_info_length}

    # Header is followed by a series of tuples (DWARFv4 pg. 177)
    table_list = []
    entry_offset_count = 0
    while (True):
        if dwarf_format_64:
            entry_offset = struct.unpack("I", dwarf_sections[".debug_pubnames"]["data"][offset:offset+8])
            entry_offset = entry_offset[0]
            offset += 8
        else:
            entry_offset = struct.unpack("I", dwarf_sections[".debug_pubnames"]["data"][offset:offset+4])
            entry_offset = entry_offset[0]

        # Signals end of set (i.e. sets are terminated by a offset value of 0)
        if entry_offset == 0:
            entry_offset_count += 1
            if entry_offset_count == 2:
                break
            continue

        entry_offset = hex(entry_offset)
        offset += 4

        name = bytearray()
        while dwarf_sections[".debug_pubnames"]["data"][offset:offset+1] != b'\x00':
            name += dwarf_sections[".debug_pubnames"]["data"][offset:offset+1]
            offset += 1
        offset += 1
        entry_name = name.decode()

        table_list.append(tuple([entry_offset, entry_name]))

    pubnames_decoded["Pairs"] = table_list


def _extract_debug_pubtypes(dwarf_sections: dict):
    """Parses the .debug_pubnames section which contains sets, where each set describes the names of
    global types whose definitions are represented by debugging information entries owned by a single
    compilation unit. Used for lookup by name.
    """
    offset = 0
    dwarf_format_64 = struct.unpack("I", dwarf_sections[".debug_pubtypes"]["data"][offset: offset+4]) == 0xFFFFFFFF
    if dwarf_format_64:
        CU_t = CU64_t
        offset += 4
    else:
        CU_t = CU32_t
    length, version, debug_info_offset, debug_info_length = struct.unpack(CU_t, dwarf_sections[".debug_pubtypes"]["data"][offset: offset + struct.calcsize(CU_t)])
    offset += struct.calcsize(CU_t)

    # Following the header is a variable number of offset/name pairs
    pubtypes_decoded["header"] = {"Length:": length, "Version:": version, "Offset in .debug_info:": debug_info_offset, "Area size in .debug_info:": debug_info_length}

    # Header is followed by a series of tuples (DWARFv4 pg. 177)
    table_list = []
    entry_offset_count = 0
    while (True):
        if dwarf_format_64:
            entry_offset = struct.unpack("I", dwarf_sections[".debug_pubtypes"]["data"][offset:offset+8])
            entry_offset = entry_offset[0]
            offset += 8
        else:
            entry_offset = struct.unpack("I", dwarf_sections[".debug_pubtypes"]["data"][offset:offset+4])
            entry_offset = entry_offset[0]

        # Signals end of set (i.e. sets are terminated by a offset value of 0)
        if entry_offset == 0:
            entry_offset_count += 1
            if entry_offset_count == 2:
                break
            continue

        entry_offset = hex(entry_offset)
        offset += 4

        name = bytearray()
        while dwarf_sections[".debug_pubtypes"]["data"][offset:offset+1] != b'\x00':
            name += dwarf_sections[".debug_pubtypes"]["data"][offset:offset+1]
            offset += 1
        offset += 1
        entry_name = name.decode()

        table_list.append(tuple([entry_offset, entry_name]))

    pubnames_decoded["Pairs"] = table_list


def _extract_debug_aranges(dwarf_sections: dict):
    """ Parses the .debug_aranges section, which contains a table that consists of sets of variable
        length entries, each set describing the portion of the program’s address space that is covered
        by a single compilation unit. Used for lookup by address.

        Used by "lookup for address". Consists of a table with sets of variable length entries,
        each set describing a portion of the program's address space covered by a CU
        Header
        Tuple+[?Segment, Address, Length]
    """
    offset = 0
    dwarf_format_64 = struct.unpack("I", dwarf_sections[".debug_aranges"]["data"][offset: offset+4]) == 0xFFFFFFFF
    if dwarf_format_64:
        arange_str = ARANGE_64_STR
        offset += 4
    else:
        arange_str = ARANGE_32_STR
    header = "Header_" + str(offset)
    unit_length, version, debug_info_offset, addr_size, segment_size = struct.unpack(arange_str, dwarf_sections[".debug_aranges"]["data"][offset: offset + struct.calcsize(CU_t)])
    offset += struct.calcsize(arange_str)

    # First tuple following header in each set begings at an offset that is a multiple of the size of a single tuple
    # That is, the size of a segment selector plus twice the size of an address
    while offset % (segment_size + 2*addr_size) != 0:
        offset += 1

    if addr_size == 1:
        addr_t = "B"
    elif addr_size == 2:
        addr_t = "H"
    elif addr_size == 4:
        addr_t = "I"
    elif addr_size == 8:
        addr_t = "Q"

    table_list = []
    zero_count = 0

    # Header is followed by a series of tuples (DWARFv4 pg. 178)
    # Without examples, not sure when to know one set ends and another beings
    while (True):
        if segment_size == 0:
            address = struct.unpack(addr_t, dwarf_sections[".debug_aranges"]["data"][offset:offset+addr_size])
            offset += addr_size
            address = hex(address[0])

            length = struct.unpack(addr_t, dwarf_sections[".debug_aranges"]["data"][offset:offset+addr_size])
            offset += addr_size
            length = hex(length[0])

            # Each set of tuples is terminated by a 0 for segment and a 0 for length
            if (address == '0x0') and (length =='0x0'):
                # We only have one aranges table and have reached the end, stop here
                if (dwarf_sections[".debug_aranges"]["data"][offset:offset+addr_size] == b''):
                    break

                # We have more tables
                zero_count += 1
                # See DWARFv4 pg. 178 to find out more on what comes after header
                aranges_decoded[header] = {"Length:": unit_length,
                                            "Version:": version,
                                            "Offset in .debug_info:": debug_info_offset,
                                            "Addr Size:": addr_size,
                                            "Segment Size:": segment_size,
                                            "Offset/Length Table": table_list}
                table_list = []

                if zero_count == 2:
                    break

                header = "Header_" + str(offset)
                unit_length, version, debug_info_offset, addr_size, segment_size = struct.unpack(CU_t, dwarf_sections[".debug_aranges"]["data"][offset: offset + struct.calcsize(CU_t)])
                offset += struct.calcsize(CU_t)

                while offset % (segment_size + 2*addr_size) != 0:
                    offset += 1

                continue

            table_list.append(tuple([address, length]))

        else:
            segment = struct.unpack(addr_t, dwarf_sections[".debug_aranges"]["data"][offset:offset+addr_size])
            offset += addr_size
            segment = hex(segment[0])

            address = struct.unpack(addr_t, dwarf_sections[".debug_aranges"]["data"][offset:offset+addr_size])
            offset += addr_size
            address = hex(address[0])

            length = struct.unpack(addr_t, dwarf_sections[".debug_aranges"]["data"][offset:offset+addr_size])
            offset += addr_size
            length = hex(length[0])

            # Each set of tuples is terminated by a 0 for segment and a 0 for length
            if (segment == '0x0') and (address == '0x0') and (length =='0x0'):
                zero_count += 1
                # See DWARFv4 pg. 178 to find out more on what comes after header
                aranges_decoded[header] = {"Length:": unit_length,
                                            "Version:": version,
                                            "Offset in .debug_info:": debug_info_offset,
                                            "Addr Size:": addr_size,
                                            "Segment Size:": segment_size,
                                            "Segment/Offset/Length Table": table_list}
                table_list = []

                if zero_count == 2:
                    break

                header = "Header_" + str(offset)
                length, version, debug_info_offset, addr_size, segment_size = struct.unpack(CU_t, dwarf_sections[".debug_aranges"]["data"][offset: offset + struct.calcsize(CU_t)])
                offset += struct.calcsize(CU_t)

                while offset % (segment_size + 2*addr_size) != 0:
                    offset += 1

                continue

            table_list.append(tuple([segment, address, length]))


def _extract_debug_line(dwarf_sections: dict):
    """Parses the .debug_line section. Defined in section 6 of DWARFv4
    This section contains line number information. Each CU has a corresponding matrix
    containing, with one row for each instruction and columns describing characteristics
    or properties.
    """
    cu_count = 0
    offset = 0
    dwarf_format_64 = struct.unpack("I", dwarf_sections[".debug_line"]["data"][offset: offset+4]) == 0xFFFFFFFF
    if dwarf_format_64:
        debug_line_str = DEBUG_LINE_64_STR
        offset += 4
    else:
        debug_line_str = DEBUG_LINE_32_STR
    header = "Header_" + str(offset)

    while True:
        cu_offset = offset
        cu_count += 1
        print("cu offset:", cu_offset)
        # Header information. There are 12 fields to this header. These are the first 8
        unit_length, version, header_length, min_instr_length, default_is_stmt, line_base, line_range, opcode_base = struct.unpack(debug_line_str, dwarf_sections[".debug_line"]["data"][offset: offset + struct.calcsize(debug_line_str)])
        print ("unit_length", unit_length, "version", version, "header_length", header_length, "min", min_instr_length,
               "default_is_statement", default_is_stmt, "line_base", line_base, "line_range", line_range, "opcode_base", opcode_base)
        offset += struct.calcsize(CU_t)

        # The next header fields is a array specifiying the number of LEB128 operands for each of the standard opcodes
        # The length of this array is opcode_base - 1
        opcode_lengths = []
        for i in range(1, opcode_base):
            data, offset = _uleb128_of_stream(dwarf_sections[".debug_line"]["data"], offset)
            op_code = _decode_uleb128(data)
            opcode_lengths.append(op_code)

            logger.info("opcode: %s", op_code)

        # The next header field is a sequence of path names "that was searched for included source files in this compilation".
        # The last entry is followed by a single null byte
        include_directories_check = struct.unpack("B", dwarf_sections[".debug_line"]["data"][offset:offset+1])
        include_directories_check = include_directories_check[0]
        offset += 1

        # If this value is 0, then the directory table is empty
        if include_directories_check:
            while True:
                path = bytearray()
                while dwarf_sections[".debug_line"]["data"][offset] != b'\00':
                    path += bytearray(dwarf_sections[".debug_line"]["data"][offset])
                    offset += 1
                offset += 1  # is this extra
                path = path.decode("utf-8")
                logger.info("path: %s", path)

                if dwarf_sections[".debug_line"]["data"][offset:offset+1] == b'\00':
                    offset += 1
                    break

        # The last header field is a sequence of entries describing source files that contribute to the line number information for this CU (or other contexts)
        # The line number program assigns numbers to each of the file entires in order, beginning with 1, and uses those numbers instead of file names in the file
        # register
        last_entry = 1
        while last_entry:
            # Null terminated string containing full or relative path name of a source file
            source_file_string = bytearray()
            while dwarf_sections[".debug_line"]["data"][offset:offset+1] != b'\00':
                source_file_string += bytearray(dwarf_sections[".debug_line"]["data"][offset:offset+1])
                offset += 1
            offset += 1

            source_file_string = source_file_string.decode("utf-8")
            print("source_file_string:", source_file_string)

            # Directory index of a directory in the include_directories section.
            # 0 if found in current directory of compilation
            # 1 if it was found in the first directory in the include_directories section, and so on
            data, offset = _uleb128_of_stream(dwarf_sections[".debug_line"]["data"], offset)
            dir_index = _decode_uleb128(data)
            print("dir index:", dir_index)

            # Implementation defined time of last modification for the file (0 if not available)
            data, offset = _uleb128_of_stream(dwarf_sections[".debug_line"]["data"], offset)
            time = _decode_uleb128(data)
            print("time::", time)

            # Length, in bytes, of file (0 if not available)
            data, offset = _uleb128_of_stream(dwarf_sections[".debug_line"]["data"], offset)
            size = _decode_uleb128(data)
            print("size:", size)

            # Last entry is followed by a single null byte
            if dwarf_sections[".debug_line"]["data"][offset:offset+1] == b'\00':
                offset += 1
                last_entry = 0

        # What follows is the line number program, where the matrix is represented for a CU

        # It would seem that the only way to know if a CU has line number programs encoded within, is
        # to check the length in the header. If by the end of the header you have not consumed the length
        # of the CU, then the rest of the CU .debug_line information will be line number programs. If you
        # have consumed the header, then there is no line number programs present in the CU

        # -4 to account for the header field "unit_length" size
        if (((offset - cu_offset)-4) == unit_length):
            print("Current CU ends here")
            continue
        print("Current CU contains more")

        # The next byte after the header seems to be null, so let's skip over it
        offset += 1

        # CONSUMING
        sm = StateMachine()

        # Value of the first special opcode is opcode_base
        curr_opcode = opcode_base

        sm.update_registers(curr_opcode)

        # ToDo: Add function for updating state machine registers
        #update_registers(curr_opcode)

        #adjusted_opcode = opcode - opcode_base
        #operation_advance = adjusted_opcode / line_range

        curr_opcode = struct.unpack("B", dwarf_sections[".debug_line"]["data"][offset:offset+1])
        curr_opcode = curr_opcode[0]
        offset += 1
        print("Current opcode:", curr_opcode)


def parse_dwarf(oid: str, data: bytes, header: dict) -> Optional[dict]:
    """ DWARF
            Section for extracting DWARF information
            To-Do:
               - Expand form conditionals for:
                    - Exprloc
                    - Lineptr
                    - Localistptr
                    - Macinfo
                    - Rangelistptr
               - LE vs BE, 32 vs 64
               - Adding high level information gathering
                   - Lines of source
            Structure:
               - .debug_info
                   | CU Header | Abbrev Code | Attr Values | ...
               - .debug_abbrev
                   | Abbrev Code | Attr Name, Attr Value | ...
               - Other data sections (.debug<str|loc|ranges|macinfo|line>) contain information based on offsets from these 2
            DWARFv4 Section 7 (pg. 139) contains all data representation information
            DWARFv5... ?
    """
    sections = header.section_info
    if not sections:
        logger.info("No sections found for oid (%s)", oid)
        return None

    # Pull out only relevant sections
    dwarf_sections = _initialize_sections(data, sections)

    parsed_dwarf = _parse_debug_sections(dwarf_sections)

    # FIXME:: move to high dwarf
    # Create mapping between functions and their addresses
    # parsed_dwarf["func_mapping"] = _addr2func(parsed_dwarf['.debug_info'])

    return parsed_dwarf

# --------------------- Utility Functions --------------------------------------------------------


def _decode_uleb128(byte_arr):
    """Decode a uLEB128 number one byte at a time, which is up to 3 bytes of data from a stream
    Credit to github.com/mohanson/leb128
    :param byte_arr: The byte array containg an encoded uLEB number
    """
    result = 0

    for i, e in enumerate(byte_arr):
        result = result + ((e & 0x7f) << (i * 7))

    return result


def _not_bitwise_and_bytes(a: bytes, mask: int) -> bool:
    """Credit to techoverflow.net/2020/09/27/how-to-perform-bitwise-boolean-operations-on-bytes-in-python3/
    :param a: the byte to AND with 0x80
    """
    flag = int.from_bytes(a, byteorder="big") & mask

    return (not flag)


def _uleb128_of_stream(stream: bytes, offset: int) -> Tuple[bytes, int]:
    """Takes a stream of bytes and returns only the bytes that compose a
    uLEB encoded number.
    :param stream: Stream of bytes
    :param offset: Current section offset
    :return: The stream of bytes that make up the uLEB number and the new offset
    """
    data = bytearray()
    for i in range(0, 3):
        curr_byte = stream[offset:offset+1]
        offset += 1
        data += bytearray(curr_byte)
        if _not_bitwise_and_bytes(curr_byte, 0x80):
            break

    return data, offset


# FIXME:: Move this to high dwarf
# Initialize empty dwarf dict
addr2func_dict = {}


def _addr2func(info_decoded: dict) -> Optional[dict]:
    """ Finds every DIE with tag "DW_TAG_subprogram", then takes the tag's
        high_pc and low_pc attributes and subtracts the two. The result is the
        address range of the function.
    """
    if not info_decoded:
        return None

    function_mapping = {}
    # Loop through each CU and each DIE for DW_TAG_subprogram and it's attributes
    # Note: High PC is offset from low
    for cu_offset in info_decoded:
        for die_offset in info_decoded[cu_offset]:
            if info_decoded[cu_offset][die_offset]["tag"] == 'DW_TAG_subprogram':
                high_pc = None
                low_pc = None
                name = None
                for attr, val in info_decoded[cu_offset][die_offset]["attributes"]:
                    if attr == 'DW_AT_low_pc':
                        low_pc = int(val, 16)
                    if attr == 'DW_AT_high_pc':
                        high_pc = int(val, 16) + low_pc
                    if attr == 'DW_AT_name':
                        name = val

                if high_pc and low_pc and name:
                    addr2func_dict[name] = {"high_pc": high_pc,
                                                   "low_pc": low_pc,
                                                   "func_size": high_pc - low_pc}
                else:
                    print("not complete info", name,
                                                                 high_pc,
                                                                 low_pc,
                                                                 high_pc - low_pc)

            elif info_decoded[cu_offset][die_offset]["tag"] == 'DW_TAG_inline_subroutine':
                abst_origin = None
                low_pc = None
                high_pc = None
                for attr, val in info_decoded[cu_offset][die_offset]["attributes"]:
                    if attr == 'DW_AT_abstract_origin':
                        abst_origin = val
                    if attr == 'DW_AT_low_pc':
                        low_pc = val
                    if attr == 'DW_AT_high_pc':
                        high_pc = val + low_pc

                if high_pc and low_pc and abst_origin:
                    addr2func_dict[abst_origin] = {"high_pc": high_pc,
                                                   "low_pc": low_pc,
                                                   "func_size": high_pc - low_pc}
                else:
                   print("not complete info", abst_origin,
                                                                 high_pc,
                                                                 low_pc,
                                                                 high_pc - low_pc)
    return function_mapping
