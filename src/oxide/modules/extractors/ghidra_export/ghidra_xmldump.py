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

""" Interface with Ghidra script which uses standard ghidra XML provider to generate
    parsable ghidra database that contains things like symbol references and data.
"""

import os
import subprocess
import logging
import time
import xml.etree.ElementTree as et

from typing import Optional

from oxide.core import sys_utils

NAME = "ghidra_xml"
logger = logging.getLogger(NAME)


def extract_ghidra_export(file_test: str) -> Optional[str]:
    """ Run ghidra script by executing shell command with filled arguments
    """
    cmd = "{} {} {} ".format(GHIDRA_PATH, GHIDRA_Project_PATH, GHIDRA_Project_NAME) + \
          "-import {} -overwrite -scriptPath {} ".format(file_test, SCRIPTS_PATH) + \
          "-postScript {} {}".format(EXPORT_SCRIPT, GHIDRA_TMP_FILE)  # noqa
    output = None
    with open(os.devnull, "w") as null:
        try:
            output = subprocess.check_output(cmd, universal_newlines=True, shell=True, stderr=null)
        except subprocess.CalledProcessError as e:
            logger.debug(e.output)
        return output


def parse_processor(output_map: dict, root: et.Element) -> None:
    output_map.update(root.attrib)


def parse_datatype_typedef(output_map: dict, datatype: et.Element) -> None:
    data_key = datatype.attrib["NAME"]
    typedef_attributes = datatype.attrib
    if "NAME" in typedef_attributes: del typedef_attributes["NAME"]
    output_map[data_key] = typedef_attributes


def parse_datatype_struct(output_map: dict, root: et.Element) -> None:
    data_key = root.attrib["NAME"]
    struct_attributes = root.attrib
    del struct_attributes["NAME"]

    members = root.findall("MEMBER")
    struct_attributes["MEMBERS"] = {}
    for memb in members:
        memb_key = memb.attrib["OFFSET"]
        member_attributes = memb.attrib
        del member_attributes["OFFSET"]

        regcmt = root.find("REGULAR_CMT")
        if regcmt is not None:
            member_attributes["REGULAR_CMT"] = regcmt.text

        struct_attributes["MEMBERS"][memb_key] = member_attributes

    output_map[data_key] = struct_attributes


def parse_datatype_union(output_map: dict, root: et.Element) -> None:
    data_key = root.attrib["NAME"]
    struct_attributes = root.attrib
    del struct_attributes["NAME"]

    members = root.findall("MEMBER")
    for memb in members:
        memb_key = memb.attrib["NAME"]
        member_attributes = memb.attrib
        del member_attributes["NAME"]

        regcmt = root.find("REGULAR_CMT")
        if regcmt is not None:
            member_attributes["REGULAR_CMT"] = regcmt.text

        struct_attributes[memb_key] = member_attributes

    output_map[data_key] = struct_attributes


def parse_datatype_enum(output_map: dict, root: et.Element) -> None:
    data_key = root.attrib["NAME"]
    enum_attributes = root.attrib
    del enum_attributes["NAME"]

    enums = root.findall("ENUM_ENTRY")
    enum_attributes["ENUMS"] = {}
    for en in enums:
        enum_attributes["ENUMS"][en.attrib["NAME"]] = en.attrib["VALUE"]

    output_map[data_key] = enum_attributes


def parse_datatype_fundef(output_map: dict, root: et.Element) -> None:
    fun_key = root.attrib["NAME"]
    fundef_attributes = root.attrib
    del fundef_attributes["NAME"]

    regcmt = root.find("REGULAR_CMT")
    if regcmt is not None:
        fundef_attributes["REGULAR_CMT"] = regcmt.text

    retype = root.find("RETURN_TYPE")
    if regcmt is not None:
        fundef_attributes["RETURN_TYPE"] = retype.attrib

    parms = root.findall("PARAMETER")
    fundef_attributes["PARAMETERS"] = {}
    for parm in parms:
        parm_key = parm.attrib["ORDINAL"]
        parm_attributes = parm.attrib
        del parm_attributes["ORDINAL"]

        fundef_attributes["PARAMETERS"][parm_key] = parm_attributes

    output_map[fun_key] = fundef_attributes


def parse_datatypes(output_map: dict, root: et.Element) -> None:
    datatype_roots = root.findall("TYPE_DEF")
    output_map["TYPEDEFS"] = {}
    for typedef in datatype_roots:
        parse_datatype_typedef(output_map["TYPEDEFS"], typedef)

    datatype_roots = root.findall("STRUCTURE")
    output_map["STRUCTS"] = {}
    for struc in datatype_roots:
        parse_datatype_struct(output_map["STRUCTS"], struc)

    # Union have same structure as STRUCTURE, except name vs union unique
    datatype_roots = root.findall("UNION")
    output_map["UNIONS"] = {}
    for uni in datatype_roots:
        parse_datatype_union(output_map["UNIONS"], uni)

    datatype_roots = root.findall("ENUM")
    output_map["ENUMS"] = {}
    for enu in datatype_roots:
        parse_datatype_enum(output_map["ENUMS"], enu)

    datatype_roots = root.findall("FUNCTION_DEF")
    output_map["FUNCTION_DEFS"] = {}
    for fun in datatype_roots:
        parse_datatype_fundef(output_map["FUNCTION_DEFS"], fun)


def parse_memmap(output_map: dict, root: et.Element) -> None:
    mem_sects = root.findall("MEMORY_SECTION")
    for sec in mem_sects:
        mem_key = sec.attrib["START_ADDR"]
        mem_attributes = sec.attrib
        del mem_attributes["START_ADDR"]
        output_map[mem_key] = mem_attributes
        mem_contents = sec.findall("MEMORY_CONTENTS")
        for cont in mem_contents:
            output_map[mem_key]["MEM_CONTENTS"] = cont.attrib


def parse_regvals(output_map: dict, root: et.Element) -> None:
    pass


def parse_code(output_map: dict, root: et.Element) -> None:
    code_roots = root.findall("CODE_BLOCK")
    for cod in code_roots:
        code_key = cod.attrib["START"]
        code_attributes = cod.attrib
        output_map[code_key] = code_attributes


def parse_data(output_map: dict, root: et.Element) -> None:
    defined_roots = root.findall("DEFINED_DATA")
    for dat in defined_roots:
        data_key = dat.attrib["ADDRESS"]
        data_attributes = dat.attrib
        del data_attributes["ADDRESS"]
        output_map[data_key] = data_attributes


def parse_equates(output_map: dict, root: et.Element) -> None:
    pass


def parse_comments(output_map: dict, root: et.Element) -> None:
    comment_roots = root.findall("COMMENT")
    for comm in comment_roots:
        comment_key = comm.attrib["ADDRESS"]
        comment_attributes = comm.attrib
        del comment_attributes["ADDRESS"]
        comment_attributes["BODY"] = comm.text
        output_map[comment_key] = comment_attributes


def parse_properties(output_map: dict, root: et.Element) -> None:
    prop_roots = root.findall("PROPERTY")
    for prop in prop_roots:
        prop_key = prop.attrib["NAME"]
        prop_attributes = prop.attrib
        del prop_attributes["NAME"]
        output_map[prop_key] = prop_attributes


def parse_bookmarks(output_map: dict, root: et.Element) -> None:
    bkmrk_roots = root.findall("BOOKMARK")
    for bkmrk in bkmrk_roots:
        bkmrk_key = bkmrk.attrib["ADDRESS"]
        bkmrk_attributes = bkmrk.attrib
        del bkmrk_attributes["ADDRESS"]
        output_map[bkmrk_key] = bkmrk_attributes


def parse_fncts(output_map: dict, root: et.Element) -> None:
    fncts_roots = root.findall("FUNCTION")
    for fnct in fncts_roots:
        fnct_key = fnct.attrib["ENTRY_POINT"]
        fnct_attributes = fnct.attrib
        del fnct_attributes["ENTRY_POINT"]

        # Information on return type of function
        return_root = fnct.find("RETURN_TYPE")
        if return_root is not None:
            fnct_attributes["RETURN_TYPE"] = return_root.attrib

        # Function Signature information
        typecmnt = fnct.find("TYPEINFO_CMT")
        if typecmnt is not None:
            fnct_attributes["TYPEINFO_CMT"] = typecmnt.text

        regcmnt = fnct.find("REGULAR_CMT")
        if regcmnt is not None:
            fnct_attributes["REGULAR_CMT"] = regcmnt.text

        fnct_attributes["ADDRESS_RANGE"] = fnct.find("ADDRESS_RANGE").attrib

        # Stack frame related information
        stk_frame = fnct.find("STACK_FRAME")
        if stk_frame:
            fnct_attributes["STACK_FRAME"] = stk_frame.attrib

            # for all local variables found on stack, fill in info
            stk_vars = stk_frame.findall("STACK_VAR")
            for stk_var in stk_vars:
                offset = stk_var.attrib["STACK_PTR_OFFSET"]
                del stk_var.attrib["STACK_PTR_OFFSET"]
                fnct_attributes["STACK_FRAME"][offset] = stk_var.attrib

        # Register Variable related info
        fnct_attributes["REGISTER_VARS"] = {}
        reg_vars = fnct.findall("REGISTER_VAR")
        for reg_var in reg_vars:
            regvar_key = reg_var.attrib["NAME"]
            regvar_attributes = reg_var.attrib
            del regvar_attributes["NAME"]
            fnct_attributes["REGISTER_VARS"][regvar_key] = regvar_attributes

        output_map[fnct_key] = fnct_attributes


def parse_progtree(output_map, root: et.Element) -> None:
    pass


def parse_entrypts(output_map: dict, root: et.Element) -> None:
    enter_roots = root.findall("PROGRAM_ENTRY_POINT")
    for ent in enter_roots:
        ent_key = ent.attrib["ADDRESS"]
        output_map[ent_key] = ""


def parse_relocations(output_map: dict, root: et.Element) -> None:
    reloc_roots = root.findall("RELOCATION")
    for reloc in reloc_roots:
        reloc_key = reloc.attrib["ADDRESS"]
        reloc_attributes = reloc.attrib
        del reloc_attributes["ADDRESS"]
        output_map[reloc_key] = reloc_attributes


def parse_symtable(output_map: dict, root: et.Element) -> None:
    symtab_roots = root.findall("SYMBOL")
    for sym in symtab_roots:
        sym_key = sym.attrib["ADDRESS"]
        sym_attributes = sym.attrib
        del sym_attributes["ADDRESS"]
        output_map[sym_key] = sym_attributes


def parse_markup(output_map: dict, root: et.Element) -> None:
    markup_roots = root.findall("EXT_LIBRARY_REFERENCE")
    for mrkup in markup_roots:
        mrkup_key = mrkup.attrib["ADDRESS"]
        mrkup_attributes = mrkup.attrib
        del mrkup_attributes["ADDRESS"]
        output_map[mrkup_key] = mrkup_attributes


def parse_extlib(output_map: dict, root: et.Element) -> None:
    extlib_roots = root.findall("EXT_LIBRARY")
    for extlib in extlib_roots:
        extlib_key = extlib.attrib["NAME"]
        extlib_attributes = extlib.attrib
        del extlib_attributes["NAME"]
        output_map[extlib_key] = extlib_attributes


def parse_xml(output_map: dict) -> None:
    # Read raw text
    try:
        raw = sys_utils.get_contents_of_file(GHIDRA_TMP_FILE).decode("utf-8")
    except AttributeError:
        return

    # Parse xml string and access root
    root = et.fromstring(raw)

    # Root attributes, listing object file type, and name
    output_map["PROG_INFO"] = root.attrib

    processor_root = root.find("PROCESSOR")
    if processor_root is not None:
        output_map['PROCESSOR'] = {}
        parse_processor(output_map['PROCESSOR'], processor_root)

    datatypes_root = root.find("DATATYPES")
    if datatypes_root is not None:
        output_map["DATATYPES"] = {}
        parse_datatypes(output_map["DATATYPES"], datatypes_root)

    memmap_root = root.find("MEMORY_MAP")
    if memmap_root is not None:
        output_map["MEMORY_MAP"] = {}
        parse_memmap(output_map["MEMORY_MAP"], memmap_root)

    regvals_root = root.find("REGISTER_VALUES")
    if regvals_root is not None:
        output_map["REGISTER_VALUES"] = {}
        parse_regvals(output_map, regvals_root)

    code_root = root.find("CODE")
    if code_root is not None:
        output_map["CODE"] = {}
        parse_code(output_map["CODE"], code_root)

    data_root = root.find("DATA")
    if data_root is not None:
        output_map["DATA"] = {}
        parse_data(output_map["DATA"], data_root)

    equates_root = root.find("EQUATES")
    if equates_root is not None:
        output_map["EQUATES"] = {}
        parse_equates(output_map["EQUATES"], equates_root)

    comments_root = root.find("COMMENTS")
    if comments_root is not None:
        output_map["COMMENTS"] = {}
        parse_comments(output_map["COMMENTS"], comments_root)

    properties_root = root.find("PROPERTIES")
    if properties_root is not None:
        output_map["PROPERTIES"] = {}
        parse_properties(output_map["PROPERTIES"], properties_root)

    bookmarks_root = root.find("BOOKMARKS")
    if bookmarks_root is not None:
        output_map["BOOKMARKS"] = {}
        parse_bookmarks(output_map["BOOKMARKS"], bookmarks_root)

    fncts_root = root.find("FUNCTIONS")
    if fncts_root is not None:
        output_map["FUNCTIONS"] = {}
        parse_fncts(output_map["FUNCTIONS"], fncts_root)

    progtree_root = root.find("PROGRAM_TREES")
    if progtree_root is not None:
        output_map["PROGRAM_TREES"] = {}
        parse_progtree(output_map["PROGRAM_TREES"], progtree_root)

    entrypts_root = root.find("PROGRAM_ENTRY_POINTS")
    if entrypts_root is not None:
        output_map["PROGRAM_ENTRY_POINTS"] = {}
        parse_entrypts(output_map["PROGRAM_ENTRY_POINTS"], entrypts_root)

    relocations_root = root.find("RELOCATION_TABLE")
    if relocations_root is not None:
        output_map["RELOCATION_TABLE"] = {}
        parse_relocations(output_map["RELOCATION_TABLE"], relocations_root)

    symtable_root = root.find("SYMBOL_TABLE")
    if symtable_root is not None:
        output_map["SYMBOL_TABLE"] = {}
        parse_symtable(output_map["SYMBOL_TABLE"], symtable_root)

    markup_root = root.find("MARKUP")
    if markup_root is not None:
        output_map["MARKUP"] = {}
        parse_markup(output_map["MARKUP"], markup_root)

    extlib_root = root.find("EXT_LIBRARY_TABLE")
    if extlib_root is not None:
        output_map["EXT_LIBRARY_TABLE"] = {}
        parse_extlib(output_map["EXT_LIBRARY_TABLE"], extlib_root)


def extract(file_test: str, header: dict) -> dict:
    """ Runs instruction extraction from ghidraHEADLESS using a java language script
        Input -
            file_test - Sample using bap.run() which runs analyses
            header_interface (header) - header object using header utiility lib
    """
    output_map = {}
    output_map["meta"] = {}

    if not header.known_format:
        logging.info("File Sample is of unknown format, Ghidra returning empty output.")
        return None

    start = time.time()

    # Create export file from ghidra
    extract_ghidra_export(file_test)

    parse_xml(output_map)

    raw = open(GHIDRA_TMP_FILE, "rb").read()

    # Clean up temp file
    sys_utils.delete_file(GHIDRA_TMP_FILE)

    end = time.time()
    output_map["meta"]["time"] = end - start
    output_map["raw"] = raw
    return output_map
