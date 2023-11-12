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

""" parse_pe.py
"""

NAME = "parse_pe"
import struct
import logging
from collections import defaultdict

from typing import Dict, Any, Optional, Tuple

from pe_enums import (SUBSYSTEM_ENUM,  # noqa
                      IMAGE_OPTIONAL_HDR_BASE_STR, IMAGE_OPTIONAL_HDR_BASE_SPEC,
                      IMAGE_OPTIONAL_HDR_PE32_STR, IMAGE_OPTIONAL_HDR_PE32_SPEC,
                      IMAGE_OPTIONAL_HDR_PE32_PLUS_STR,
                      IMAGE_OPTIONAL_HDR_PE32_PLUS_SPEC, MACHINE_ENUM,
                      EXPORTS_DIRECTORY_TABLE_STR, EXPORTS_DIRECTORY_TABLE_SPEC,
                      BASE_RELOCATION_BLOCK_STR, BASE_RELOCATION_BLOCK_SPEC,
                      DATA_DIRECTORY_STR, DATA_DIRECTORY_SPEC,
                      IMPORT_TABLE_STR, IMPORT_TABLE_SPEC,
                      CERTIFICATE_TABLE_STR, CERTIFICATE_TABLE_SPEC,
                      IMAGE_COFF_HDR_STR, IMAGE_COFF_HDR_SPEC,
                      IMAGE_DOS_HDR_STR, IMAGE_DOS_HDR_SPEC,
                      DLL_CHARACTERISTICS_MASK,
                      SECTION_HEADER_STR, SECTION_HEADER_SPEC,
                      SECTION_CHARACTERISTICS_MASK,
                      IMAGE_COFF_CHARACTERISTIC_MASK,
                      DELAY_IMPORT_TABLE_STR, DELAY_IMPORT_TABLE_SPEC,
                      IMPORT_LOOKUP_TABLE_32_STR, IMPORT_LOOKUP_TABLE_64_STR,
                      BASE_RELOCATION_STR, EXPORTS_NAME_POINTER_TABLE_STR,
                      EXPORTS_ORDINAL_TABLE_STR, EXPORTS_ADDRESS_TABLE_STR,
                      # Unused Imports
                      EXPORTS_ORDINAL_TABLE_SPEC, EXPORTS_ADDRESS_TABLE_SPEC,
                      BASE_RELOCATION_SPEC, EXPORTS_NAME_POINTER_TABLE_SPEC,
                      IMPORT_LOOKUP_TABLE_32_SPEC, IMPORT_LOOKUP_TABLE_64_SPEC,
                      BASE_RELOCATION_TYPE_ENUM)


logger = logging.getLogger(NAME)
logger.debug("init")


def parse_pe(data: bytes, oid: str) -> Dict[str, Any]:
    header = {}
    header["dos_header"] = None
    header["coff_header"] = None
    header["optional_header"] = None
    offsets = defaultdict(list)

    dos_header, dos_header_offsets = parse_dos_header(data)
    offsets.update(dos_header_offsets)
    if not dos_header:
        logger.info("DOS Header not found in %s", oid)
        return None
    header["dos_header"] = dos_header

    pe_sig_offset = dos_header["lfanew"]
    pe_signature, pe_sig_offsets = parse_pe_signature(pe_sig_offset, data)
    offsets.update(pe_sig_offsets)

    if not pe_signature:
        logger.info("PE signature not found in %s", oid)
        return header

    header["pe_signature"] = pe_signature

    pe_base = pe_sig_offset + len(pe_signature)
    coff_header, coff_header_offsets = parse_coff_header(pe_base, data)
    offsets.update(coff_header_offsets)

    if not coff_header:
        return header

    header["coff_header"] = coff_header

    opt_header, data_dir_offset, data_dir_offsets = parse_optional_header_fixed(pe_base, data)
    offsets.update(data_dir_offsets)
    header["optional_header"] = opt_header
    file_alignment = opt_header["file_alignment"]

    if not header["optional_header"]:
        logger.info("Optional header not found in %s", oid)
        return header

    if not data_dir_offset:
        logger.info("Section table not found in %s", oid)
        return header

    section_table, sec_table_offsets = parse_section_header_table(coff_header, pe_base, data)
    offsets.update(sec_table_offsets)
    if section_table:
        for _, sec_info in section_table.items():
            if file_alignment and sec_info["pointer_to_raw_data"] % file_alignment:
                logger.info("Misaligned section in %s", oid)

    header["section_table"] = section_table

    # section was passed in
    dd, data_dir_offsets = parse_data_directory(data_dir_offset, opt_header, data)
    offsets.update(data_dir_offsets)
    header["data_directories"] = dd

    certificate_table, cert_offsets = parse_certificate_table(dd, data)
    offsets.update(cert_offsets)
    header["certificate_table"] = certificate_table

    import_table, import_offsets = parse_import_table(dd, section_table, opt_header, data)
    offsets.update(import_offsets)
    header["import_table"] = import_table

    delay_import_table, delay_imp_offsets = parse_delay_import_table(dd, section_table, opt_header, data)
    offsets.update(delay_imp_offsets)
    header["delay_import_table"] = delay_import_table

    relocs, reloc_offsets = parse_base_relocations(dd, section_table, data)
    offsets.update(reloc_offsets)
    header["relocations"] = relocs

    exports, export_dir_offsets = parse_exports_directory_table(dd, section_table, opt_header, data)
    offsets.update(export_dir_offsets)
    header["exports_table"] = exports

    header["offsets"] = offsets

    return header


def rva_to_offset(rva: int, sections: dict, image_base: int = 0) -> Optional[int]:
    if not sections:
        return None

    for _, sec_info in sections.items():
        v_add = sec_info["virtual_address"]
        v_size = sec_info["virtual_size"]
        if rva >= v_add and rva < v_add + v_size:
            f_add = sec_info["pointer_to_raw_data"] + rva - v_add
            return f_add
    if image_base and rva > image_base:
        return rva_to_offset(rva - image_base, sections, image_base=0)
    return None


def parse_coff_header(pe_base: int, data: bytes) -> Tuple[Optional[dict], dict]:
    vals = {}
    offsets = defaultdict(list)
    spec_len = struct.calcsize(IMAGE_COFF_HDR_STR)
    if len(data) < pe_base + spec_len:
        return None, {}

    val_data = struct.unpack(IMAGE_COFF_HDR_STR, data[pe_base: pe_base + spec_len])
    for offset, elem in enumerate(IMAGE_COFF_HDR_SPEC):
        vals[elem[0]] = val_data[offset]

    # bit-encoded integer containing fields
    characteristics = vals["characteristics"]

    vals["characteristics"] = {}
    for elem in IMAGE_COFF_CHARACTERISTIC_MASK:
        vals["characteristics"][elem[0]] = bool(characteristics & elem[1])

    try:
        vals["machine_description"] = MACHINE_ENUM[vals["machine"]]
    except KeyError:
        vals["subsystem_description"] = "Not Valid"

    offsets = build_coff_offset_strings(vals, pe_base)

    return vals, offsets


def parse_pe_signature(pe_base: int, data: bytes) -> Tuple[Optional[bytes], dict]:
    offsets = defaultdict(list)
    if pe_base >= len(data) - 4:
        return None, {}
    sig = data[pe_base: pe_base + 4]
    if sig[0:2] in [b"NE", b"LE", b"MZ"]:
        sig = sig[:2]
    offsets[pe_base].append({"len": len(sig), "string": "PE Signature"})
    return sig, offsets


def build_coff_offset_strings(coff_header: dict, base: int) -> dict:
    offsets = defaultdict(list)
    offset = base
    for elem in IMAGE_COFF_HDR_SPEC:
        length = elem[1]
        if length > 4:
            desc = "{} ({})".format(elem[0], elem[2])
        else:
            desc = "{}: {}  ({})".format(elem[0], coff_header[elem[0]], elem[2])
        offsets[offset].append({"len": length, "string": desc})
        offset += length
    return offsets


def parse_dos_header(data: bytes) -> Tuple[Optional[dict], dict]:
    offsets = defaultdict(list)
    vals = {}
    spec_len = struct.calcsize(IMAGE_DOS_HDR_STR)
    if len(data) < spec_len:
        logger.info("DOS Header not found")
        return None, {}

    val_data = struct.unpack(IMAGE_DOS_HDR_STR, data[:spec_len])
    for offset, elem in enumerate(IMAGE_DOS_HDR_SPEC):
        vals[elem[0]] = val_data[offset]
    if vals["magic"] != b"MZ" and vals["magic"] != b"ZM":
        logger.info("DOS Signature not found")
        return None, {}

    offsets = build_dos_offset_strings(vals, 0)

    vals['dos_stub'], header_len, stub_len = parse_dos_stub(vals, data)
    if stub_len:
        offsets[header_len].append({"len": stub_len, "string": "dos_stub"})
        parse_rich_signature(vals, offsets)
    return vals, offsets


def parse_dos_stub(dos_header: dict, data: bytes) -> Tuple[bytes, int, int]:
    header_len = struct.calcsize(IMAGE_DOS_HDR_STR)
    dos_stub_offset = dos_header["cparhdr"] * 16
    if dos_stub_offset != header_len:
        logger.info("Unusual cparhdr value pointing to DOS header")
    lfanew = dos_header["lfanew"]
    dos_stub_len = lfanew - header_len
    if dos_stub_len > 0:
        return data[dos_stub_offset:lfanew], header_len, dos_stub_len
    else:
        return None, header_len, 0


def parse_rich_signature(dos_header: dict, offsets: dict) -> None:
    dos_stub = dos_header['dos_stub']
    if len(dos_stub) <= 64 + 64:  # 1024:  TODO: Not sure what this should be?
        return
    else:
        rich_sig = dos_stub[64:]

    # Algorithm adapted from http://ntcore.com/files/richsign.htm
    n_sign_dwords = None
    for i in range(100):
        if (i*4 + 4) > len(rich_sig):
            # no rich header found
            break
        dw = struct.unpack("=L", rich_sig[i * 4: (i * 4) + 4])[0]
        if dw == 0x68636952:
            n_sign_dwords = i
            break

    if not n_sign_dwords:
        return

    mask = struct.unpack("=L", rich_sig[(n_sign_dwords + 1) * 4: (n_sign_dwords + 1) * 4 + 4])[0]
    str_info = "Rich Signature - VC++ tools used: "
    for i in range(4, n_sign_dwords, 2):
        dw = struct.unpack("=L", rich_sig[i * 4: i * 4 + 4])[0] ^ mask
        id = dw >> 16
        minver = dw & 0xFFFF
        vnum = struct.unpack("=L", rich_sig[(i + 1) * 4: (i + 1) * 4 + 4])[0] ^ mask
        str_info += "%s: ID: %d, Version: %d Times: %d" % (str_info, id, minver, vnum)
    offsets[0x80].append({"string": str_info, "len": n_sign_dwords * 4})
    dos_header["rich_signature"] = str_info


def build_dos_offset_strings(dos_header: dict, base: int) -> dict:
    offsets = defaultdict(list)
    offset = base
    for elem in IMAGE_DOS_HDR_SPEC:
        length = elem[1]
        if length > 4:
            s = "{} ({})".format(elem[0], elem[2])
        else:
            s = "{}: {}  ({})".format(elem[0], dos_header[elem[0]], elem[2])
        offsets[offset].append({"len": length, "string": s})
        offset += length
    return offsets


def parse_section_header_table(coff_header: dict, pe_base: int, data: bytes) -> Tuple[Optional[dict], dict]:
    offsets = {}
    vals = {}
    section_table_base = coff_header["size_of_optional_header"] + \
        pe_base + struct.calcsize(IMAGE_COFF_HDR_STR)
    number_of_sections = coff_header["number_of_sections"]
    section_header_len = struct.calcsize(SECTION_HEADER_STR)

    if section_table_base is None or number_of_sections is None:
        return None, {}
    if section_table_base + number_of_sections * section_header_len > len(data):
        logger.info("Invalid number of sections")
        return None, {}

    current_offset = section_table_base
    for _ in range(number_of_sections):
        section, sec_header_offsets = parse_section_header(current_offset, data)
        vals[section["name"]] = section
        offsets.update(sec_header_offsets)
        # offsets[current_offset] = [{"len": section_header_len, "string": "Section Definition: " + section["name"]}]   # noqa
        current_offset += section_header_len
    return vals, offsets


def parse_section_header(section_header_base: int, data: bytes) -> Tuple[Optional[dict], dict]:
    offsets = defaultdict(list)
    vals = {}
    section_header_len = struct.calcsize(SECTION_HEADER_STR)
    if section_header_base + section_header_len > len(data):
        return None, {}

    val_data = struct.unpack(SECTION_HEADER_STR, data[section_header_base: section_header_base + section_header_len])

    for offset, elem in enumerate(SECTION_HEADER_SPEC):
        vals[elem[0]] = val_data[offset]

    characteristics = vals["characteristics"]
    vals["characteristics"] = {}
    for elem in SECTION_CHARACTERISTICS_MASK:
        vals["characteristics"][elem[0]] = bool(characteristics & elem[1])
    offsets = build_section_offsets(section_header_base, vals, offsets)
    return vals, offsets


def parse_data_directory(dd_offset: int, optional_header: dict, data: bytes) -> Tuple[Optional[dict], dict]:
    offsets = defaultdict(list)
    vals = {}
    num = optional_header["number_of_data_directories"]
    entry_len = struct.calcsize(DATA_DIRECTORY_STR)
    if dd_offset + entry_len * num > len(data):
        return None, {}
    if num > 16:
        num = 16
    current = dd_offset
    for index, elem in enumerate(DATA_DIRECTORY_SPEC):
        if index > num:
            break
        addr, length = struct.unpack(DATA_DIRECTORY_STR, data[current: current + entry_len])

        offset = addr
        if not offset:
            offset = 0

        entry = {"virtual_address": addr, "length": length, "offset": offset, "name": elem[0]}
        vals[elem[0]] = entry
        desc = "Data Directory Entry: {} at {} (RVA), length {}".format(elem[0], addr, length)
        offsets[current].append({"len": entry_len, "string": desc})
        current += entry_len

    return vals, offsets


def parse_optional_header_fixed(pe_base: int, data: bytes) -> Tuple[Optional[dict], int, dict]:
    offsets = defaultdict(list)
    vals = {}
    coff_len = struct.calcsize(IMAGE_COFF_HDR_STR)
    base_offset = pe_base + coff_len
    base_len = struct.calcsize(IMAGE_OPTIONAL_HDR_BASE_STR)
    pe32_len = struct.calcsize(IMAGE_OPTIONAL_HDR_PE32_STR)
    opt_len = base_len + pe32_len
    opt_end = base_offset + opt_len

    if len(data) < opt_end:
        # if PE is less than one page, it will be allocated a page
        if len(data) < 4096:
            # In case of very small PE (TinyPE)
            data += b"\x00" * (4096 - len(data))
        else:
            return None, None, {}

    val_data = struct.unpack(IMAGE_OPTIONAL_HDR_BASE_STR, data[base_offset:base_offset + base_len])
    for offset, elem in enumerate(IMAGE_OPTIONAL_HDR_BASE_SPEC):
        vals[elem[0]] = val_data[offset]
    pe32_offset = base_offset + base_len
    if vals["magic_type"] == 0x20B:
        # Use 64-bit pe+ header structure (do additional length checking)
        pe32_plus_len = struct.calcsize(IMAGE_OPTIONAL_HDR_PE32_PLUS_STR)
        opt_len = base_len + pe32_plus_len
        opt_end = base_offset + opt_len
        if len(data) < opt_end:
            return None, None, {}

        val_data = struct.unpack(IMAGE_OPTIONAL_HDR_PE32_PLUS_STR, data[pe32_offset: pe32_offset + pe32_plus_len])
        for offset, elem in enumerate(IMAGE_OPTIONAL_HDR_PE32_PLUS_SPEC):
            vals[elem[0]] = val_data[offset]
    else:
        # Use 32-bi pe header structure
        val_data = struct.unpack(IMAGE_OPTIONAL_HDR_PE32_STR,
                                 data[pe32_offset:pe32_offset + pe32_len])
        for offset, elem in enumerate(IMAGE_OPTIONAL_HDR_PE32_SPEC):
            vals[elem[0]] = val_data[offset]
    characteristics = vals["dll_characteristics"]
    vals["dll_characteristics"] = {}
    for elem in DLL_CHARACTERISTICS_MASK:
        vals["dll_characteristics"][elem[0]] = bool(characteristics & elem[1])
    try:
        vals["subsystem_description"] = SUBSYSTEM_ENUM[vals["subsystem"]]
    except KeyError:
        vals["subsystem_description"] = "Not valid"

    offsets = build_opt_offset_strings(vals, base_offset, offsets)
    return vals, opt_end, offsets


def build_section_offsets(base: int, section: dict, offsets: dict) -> dict:
    offset = base
    for elem in SECTION_HEADER_SPEC:
        length = elem[1]
        desc = "{}: {}  ({})".format(elem[0], str(section[elem[0]]).strip('\x00'), elem[2])
        offsets[offset].append({"len": length, "string": desc})
        offset += length
    return offsets


def build_opt_offset_strings(opt_header: dict, base: int, offsets: dict) -> dict:
    offset = base
    for elem in IMAGE_OPTIONAL_HDR_BASE_SPEC:
        length = elem[1]
        if length > 4:
            s = "{} ({})".format(elem[0], elem[2])
        else:
            s = "{}: {}  ({})".format(elem[0], opt_header[elem[0]], elem[2])
        offsets[offset].append({"len": length, "string": s})
        offset += length

    # If 64 bit pe (pe+)
    if opt_header["magic_type"] == 0x20B:
        for elem in IMAGE_OPTIONAL_HDR_PE32_PLUS_SPEC:
            length = elem[1]
            if length > 4:
                s = "{} ({})".format(elem[0], elem[2])
            else:
                s = "{}: {}  ({})".format(elem[0], opt_header[elem[0]], elem[2])
            offsets[offset].append({"len": length, "string": s})
            offset += length
    else:
        # 32-bit pe
        for elem in IMAGE_OPTIONAL_HDR_PE32_SPEC:
            length = elem[1]
            if length > 4:
                s = "{} ({})".format(elem[0], elem[2])
            else:
                s = "{}: {}  ({})".format(elem[0], opt_header[elem[0]], elem[2])
            offsets[offset].append({"len": length, "string": s})
            offset += length

    return offsets


def parse_certificate_table(dd, data) -> Tuple[Optional[dict], dict]:
    offsets = defaultdict(list)
    if not dd or "certificate_table" not in dd:
        return None, {}
    base, table_len = dd["certificate_table"]["offset"], dd["certificate_table"]["length"]
    if base == 0 and table_len == 0:
        return None, {}
    if base + table_len > len(data):
        return None, {}

    vals = []
    entry_len = struct.calcsize(CERTIFICATE_TABLE_STR)
    current_offset = base
    while current_offset - base < table_len and current_offset + entry_len < len(data):
        certificate = {}
        val_data = struct.unpack(CERTIFICATE_TABLE_STR,
                                 data[current_offset:current_offset + entry_len])
        for offset, elem in enumerate(CERTIFICATE_TABLE_SPEC):
            certificate[elem[0]] = val_data[offset]
        length = certificate["length"]
        if not length:
            break

        if current_offset + length < len(data):
            certificate["data"] = data[current_offset + entry_len:current_offset + length]
        else:
            certificate["data"] = None

        offsets[current_offset] = [{"len": length, "string": "Certificate"}]
        if length % 8 > 0:
            length += 8 - (length % 8)
        current_offset += length
        vals.append(certificate)
    return vals, offsets


def rva_import_string_lookup(rva, sections, image_base, data, offsets) -> Optional[bytes]:
    if not rva:
        return None

    f_offset = rva_to_offset(rva, sections, image_base)
    if not f_offset:
        return None

    string_end = data[f_offset:].find(b"\x00")
    offsets[f_offset] = [{"len": string_end, "string": "Import Name"}]
    return data[f_offset:f_offset + string_end]


def parse_import_lookup_table(base: int, optional_header: dict, sections: dict, data: bytes) -> Optional[dict]:
    """ TODO::base_rva not used
    """
    offsets = defaultdict(list)
    if not base:
        return None, {}

    pe_type = optional_header["magic_type"]
    if pe_type == 0x20b:
        s = IMPORT_LOOKUP_TABLE_64_STR
    else:
        s = IMPORT_LOOKUP_TABLE_32_STR

    entry_len = struct.calcsize(s)
    vals = []
    offset = base
    while offset + entry_len < len(data):
        val_data = struct.unpack(s, data[offset: offset + entry_len])
        if val_data[0] == 0:
            break

        # import lookup for ordinal
        if ((pe_type == 0x20b and val_data[0] & 0x8000000000000000) or (pe_type != 0x20b and val_data[0] & 0x80000000)):
            ordinal = val_data[0] & 0xff
            vals.append(ordinal)
            offsets[offset].append({"len": entry_len, "string": "Import ordinal"})
        else:
            # import lookup for name
            name_rva = val_data[0]
            name = rva_import_string_lookup(name_rva + 2, sections, optional_header["image_base"], data, offsets)
            if not name:
                break
            vals.append(name)
            offsets[offset].append({"len": entry_len, "string": "RVA to import name"})

        offset += entry_len

    return vals, offsets


def parse_import_address_table(base: int, base_rva: int, optional_header: dict, sections: dict, data: bytes) -> Tuple[Optional[dict], dict]:
    offsets = defaultdict(list)
    if not base:
        return None, {}

    pe_type = optional_header["magic_type"]
    if pe_type == 0x20b:
        s = IMPORT_LOOKUP_TABLE_64_STR
    else:
        s = IMPORT_LOOKUP_TABLE_64_STR

    entry_len = struct.calcsize(s)
    vals = {}
    offset = base
    rva = base_rva
    while offset + entry_len < len(data):
        val_data = struct.unpack(s, data[offset:offset + entry_len])
        if not val_data[0]:
            break

        # import address table entry for ordinal
        if ((pe_type == 0x20b and val_data[0] & 0x8000000000000000) or (pe_type != 0x20b and val_data[0] & 0x80000000)):
            ordinal = val_data[0] & 0xff
            vals[rva + optional_header["image_base"]] = ordinal
        else:
            # import address table entry for name
            name_rva = val_data[0]
            name = rva_import_string_lookup(name_rva + 2, sections, optional_header["image_base"], data, offsets)
            if not name:
                break
            vals[rva + optional_header["image_base"]] = name
        offset += entry_len
        rva += entry_len

    return vals, offsets


def parse_import_table(dd: int, sections: dict, optional_header: dict, data: bytes) -> Optional[dict]:
    offsets = defaultdict(list)
    if not dd or "import_table" not in dd:
        return None, {}
    base_rva, table_len = dd["import_table"]["virtual_address"], dd["import_table"]["length"]
    if not base_rva or not table_len:
        return None, {}

    base = rva_to_offset(base_rva, sections)
    if not base or base + table_len > len(data):
        return None, {}

    vals = {}
    entry_len = struct.calcsize(IMPORT_TABLE_STR)
    current_offset = base
    while current_offset - base < table_len and current_offset + entry_len < len(data):
        val_data = struct.unpack(IMPORT_TABLE_STR, data[current_offset:current_offset + entry_len])
        check = 0
        for v in val_data:
            if v != 0:
                check = 1
                break
        if not check:
            break

        import_entry = {}
        for offset, elem in enumerate(IMPORT_TABLE_SPEC):
            import_entry[elem[0]] = val_data[offset]
        name_rva = import_entry["name_rva"]
        if not name_rva:
            continue

        name = rva_import_string_lookup(name_rva, sections, optional_header["image_base"], data, offsets)
        lookup_table_rva = import_entry["import_lookup_table"]
        lookup_table_offset = rva_to_offset(lookup_table_rva, sections, optional_header["image_base"])
        function_names, offsets = parse_import_lookup_table(
            lookup_table_offset, optional_header, sections, data)
        address_table_rva = import_entry["import_address_table"]
        address_table_offset = rva_to_offset(address_table_rva, sections, optional_header["image_base"])
        addresses, offsets = parse_import_address_table(
            address_table_offset, address_table_rva, optional_header, sections, data)

        import_entry["function_names"] = function_names
        import_entry["addresses"] = addresses

        if name:
            vals[name] = import_entry
        else:
            vals[current_offset] = import_entry
        offsets = build_import_offset_strings(import_entry, current_offset, name, offsets)
        current_offset += entry_len

    return vals, offsets


def parse_delay_import_table(dd: dict, sections: dict, optional_header: dict, data: bytes) -> Tuple[Optional[dict], dict]:
    offsets = defaultdict(list)
    if not dd or "delay_import_table" not in dd:
        return None, {}
    base_rva, table_len = dd["delay_import_table"]["virtual_address"], dd["delay_import_table"]["length"]  # noqa
    if not base_rva or not table_len:
        return None, {}

    base = rva_to_offset(base_rva, sections)
    if not base or base + table_len > len(data):
        return None, {}

    vals = {}
    entry_len = struct.calcsize(DELAY_IMPORT_TABLE_STR)
    current_offset = base
    while current_offset - base < table_len and current_offset + entry_len < len(data):
        val_data = struct.unpack(DELAY_IMPORT_TABLE_STR,
                                 data[current_offset: current_offset + entry_len])
        check = 0
        for v in val_data:
            if v != 0:
                check = 1
                break
        if not check:
            break
        import_entry = {}
        for offset, elem in enumerate(DELAY_IMPORT_TABLE_SPEC):
            import_entry[elem[0]] = val_data[offset]
        name_rva = import_entry["name_rva"]
        if not name_rva:
            continue
        name = rva_import_string_lookup(name_rva, sections, optional_header["image_base"], data, offsets)
        lookup_table_rva = import_entry["delay_import_name_table"]
        lookup_table_offset = rva_to_offset(lookup_table_rva, sections, optional_header["image_base"])
        function_names, import_lut_offsets = parse_import_lookup_table(
            lookup_table_offset, optional_header, sections, data)
        offsets.update(import_lut_offsets)

        address_table_rva = import_entry["delay_import_address_table"]

        # Delay imports only have addresses in the file at the lookup table.
        # The address table is populated on demand in the image.
        addresses, import_lut_offsets = parse_import_address_table(
            lookup_table_offset, address_table_rva, optional_header, sections, data)
        offsets.update(import_lut_offsets)

        import_entry["function_names"] = function_names
        import_entry["addresses"] = addresses

        if name:
            vals[name] = import_entry
        else:
            vals[current_offset] = import_entry
        delay_offset_str_offsets = build_delay_offset_strings(import_entry, current_offset, name, offsets)
        offsets.update(delay_offset_str_offsets)
        current_offset += entry_len

    return vals, offsets


def build_import_offset_strings(imports, base, name, offsets):
    offset = base
    for elem in IMPORT_TABLE_SPEC:
        length = elem[1]
        s = "{} - {}: {} ({})".format(name, elem[0], imports[elem[0]], elem[2])
        offsets[offset].append({"len": length, "string": s})
        offset += length
    return offsets


def build_delay_offset_strings(imports, base, name, offsets) -> dict:
    offset = base
    for elem in DELAY_IMPORT_TABLE_SPEC:
        length = elem[1]
        s = "{} - {}: {} ({})".format(name, elem[0], imports[elem[0]], elem[2])
        offsets[offset].append({"len": length, "string": s})
        offset += length
    return offsets


def rva_export_string_lookup(rva: int, sections: dict, image_base: int, data: bytes) -> Optional[bytes]:
    rva_offsets = {}
    if not rva:
        return None, {}
    f_offset = rva_to_offset(rva, sections, image_base)
    if not f_offset:
        return None, {}
    string_end = data[f_offset:].find(b"\x00")
    rva_offsets[f_offset] = [{"len": string_end, "string": "Export Name"}]
    return data[f_offset:f_offset + string_end], rva_offsets


def parse_exports_directory_table(dd, sections, optional_header, data: bytes) -> Tuple[Optional[dict], dict]:
    offsets = defaultdict(list)
    if not dd or "export_table" not in dd:
        return None, {}
    base_rva, table_len = dd["export_table"]["virtual_address"], dd["export_table"]["length"]
    if base_rva == 0 and table_len == 0:
        return None, {}

    str_len = struct.calcsize(EXPORTS_DIRECTORY_TABLE_STR)
    base = rva_to_offset(base_rva, sections)
    if not base or base + str_len >= len(data):
        return None, {}

    vals = {}
    val_data = struct.unpack(EXPORTS_DIRECTORY_TABLE_STR, data[base: base + str_len])
    for n, elem in enumerate(EXPORTS_DIRECTORY_TABLE_SPEC):
        vals[elem[0]] = val_data[n]

    build_exports_offset_strings(vals, base)

    base_rva = vals["export_address_table_rva"]
    base = rva_to_offset(base_rva, sections)
    entry_len = struct.calcsize(EXPORTS_ADDRESS_TABLE_STR)
    addresses = []
    for i in range(vals["address_table_entries"]):
        if not base or base + entry_len >= len(data):
            break
        address = struct.unpack(EXPORTS_ADDRESS_TABLE_STR, data[base:base + entry_len])
        addresses.append(address[0])
        base += entry_len

    base_rva = vals["name_pointer_rva"]
    base = rva_to_offset(base_rva, sections)
    if not base:
        return None, {}

    entry_len = struct.calcsize(EXPORTS_NAME_POINTER_TABLE_STR)
    export_names = []
    for i in range(vals["number_of_name_pointers"]):
        if base + entry_len >= len(data):
            break
        name_ptr = struct.unpack(EXPORTS_NAME_POINTER_TABLE_STR, data[base:base + entry_len])
        name, rva_offsets = rva_export_string_lookup(name_ptr[0], sections, optional_header["image_base"], data)  # noqa
        offsets.update(rva_offsets)
        base += entry_len
        if name:
            export_names.append(name)

    base_rva = vals["ordinal_table_rva"]
    base = rva_to_offset(base_rva, sections)
    entry_len = struct.calcsize(EXPORTS_ORDINAL_TABLE_STR)
    ords = []
    for i in range(vals["number_of_name_pointers"]):
        if not base or base + entry_len >= len(data):
            break
        ord_val = struct.unpack(EXPORTS_ORDINAL_TABLE_STR, data[base:base + entry_len])
        ords.append(ord_val[0])
        base += entry_len

    exports = {}

    for n, o in zip(export_names, ords):
        if o < len(addresses):
            exports[n] = {"ord": o, "address": addresses[o]}

    vals["export_names"] = exports
    return vals, offsets


def build_exports_offset_strings(exports: dict, base: int) -> dict:
    offsets = defaultdict(list)
    offset = base
    for elem in EXPORTS_DIRECTORY_TABLE_SPEC:
        length = elem[1]
        s = "{}: {} ({})".format(elem[0], exports[elem[0]], elem[2])
        offsets[offset].append({"len": length, "string": s})
        offset += length
    return offsets


def parse_base_relocations(dd: dict, sections: dict, data: bytes) -> Tuple[Optional[dict], dict]:
    offsets = defaultdict(list)
    if not dd or "base_relocation_table" not in dd:
        return None, {}
    base, table_len = dd["base_relocation_table"]["virtual_address"], dd["base_relocation_table"]["length"]  # noqa

    if base == 0 and table_len == 0:
        return None, {}

    entry_len = struct.calcsize(BASE_RELOCATION_BLOCK_STR)
    base = rva_to_offset(base, sections)
    if not base:
        return None, {}

    offset = base
    relocations = []
    while offset - base < table_len and offset + entry_len < len(data):
        val_data = struct.unpack(BASE_RELOCATION_BLOCK_STR, data[offset: offset + entry_len])
        block = {}
        for n, elem in enumerate(BASE_RELOCATION_BLOCK_SPEC):
            block[elem[0]] = val_data[n]

        o = offset
        for elem in BASE_RELOCATION_BLOCK_SPEC:
            length = elem[1]
            s = "{}: {} ({})".format(elem[0], block[elem[0]], elem[2])
            offsets[o].append({"len": length, "string": s})
            o += length

        rels = []
        s = block["block_size"]
        offset += entry_len
        s -= entry_len
        rlen = struct.calcsize(BASE_RELOCATION_STR)
        num_entries = s // rlen
        for i in range(num_entries):
            if offset + rlen >= len(data):
                break

            type_offset = struct.unpack(BASE_RELOCATION_STR, data[offset: offset + rlen])
            type_val = (type_offset[0] & 0b1111000000000000) >> 12
            offset_val = type_offset[0] & 0b0000111111111111
            rels.append((type_val, offset_val))

            offsets[offset].append({"len": rlen,
                                    "string": "Type: {}, Offset: {}".format(type_val, offset_val)})

            offset += rlen
        block["relocations"] = rels

        relocations.append(block)

    return relocations, offsets
