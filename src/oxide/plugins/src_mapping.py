""" Plugin: Scripts for mapping bytes to dasm to decomp to source line.
"""
import random
import logging
from subprocess import check_output
from difflib import SequenceMatcher

from alive_progress import alive_bar

from typing import List

from oxide.core import api

import pypcode
from pypcode import ArchLanguage
from pypcode import Arch, Context, PcodePrettyPrinter

from typing import Any, Dict, Optional, Tuple, Union


NAME = "src_mapping"
MAPPING_LOGGER = logging.getLogger(NAME)

""" Objectfile.py
"""
import xml.etree.ElementTree as ET

# from src.ghidra import XMLParser
# from src.utils.logging import debug, info, error

from typing import Dict, List, Optional

MAX_INST_SIZE = 32
THRESHOLD = 3


def _remove_index_from_dictionary(key: Any, dictionary: Dict) -> Dict:
    if key in dictionary: del dictionary[key]
    return dictionary


class XMLParser:
    def __init__(self):
        self.xml_map = {}

    def parse_processor(self, processor_root: ET.Element) -> None:
        self.xml_map['PROCESSOR'].update(processor_root.attrib)

    def parse_datatype_typedef(self, datatype: ET.Element) -> None:
        data_key = datatype.attrib["NAME"]
        typedef_attributes = datatype.attrib
        _remove_index_from_dictionary("NAME", typedef_attributes)
        self.xml_map["DATATYPES"]["TYPEDEFS"][data_key] = typedef_attributes

    def parse_datatype_struct(self, struc: ET.Element) -> None:
        data_key = struc.attrib["NAME"]
        struct_attributes = struc.attrib
        _remove_index_from_dictionary("NAME", struct_attributes)

        members = struc.findall("MEMBER")
        struct_attributes["MEMBERS"] = {}
        for memb in members:
            memb_key = memb.attrib["OFFSET"]
            member_attributes = memb.attrib
            _remove_index_from_dictionary("OFFSET", member_attributes)

            regcmt = struc.find("REGULAR_CMT")
            if regcmt is not None:
                member_attributes["REGULAR_CMT"] = regcmt.text

            struct_attributes["MEMBERS"][memb_key] = member_attributes

        self.xml_map["DATATYPES"]["STRUCTS"][data_key] = struct_attributes

    def parse_datatype_union(self, root: ET.Element) -> None:
        data_key = root.attrib["NAME"]
        struct_attributes = root.attrib
        _remove_index_from_dictionary("NAME", struct_attributes)

        members = root.findall("MEMBER")
        for memb in members:
            memb_key = memb.attrib["NAME"]
            member_attributes = memb.attrib
            _remove_index_from_dictionary("NAME", member_attributes)

            regcmt = root.find("REGULAR_CMT")
            if regcmt is not None:
                member_attributes["REGULAR_CMT"] = regcmt.text

            struct_attributes[memb_key] = member_attributes

        self.xml_map["DATATYPES"]["UNIONS"][data_key] = struct_attributes

    def parse_datatype_enum(self, root: ET.Element) -> None:
        data_key = root.attrib["NAME"]
        enum_attributes = root.attrib
        _remove_index_from_dictionary("NAME", enum_attributes)

        enums = root.findall("ENUM_ENTRY")
        enum_attributes["ENUMS"] = {}
        for en in enums:
            enum_attributes["ENUMS"][en.attrib["NAME"]] = en.attrib["VALUE"]

        self.xml_map["DATATYPES"]["ENUMS"][data_key] = enum_attributes

    def parse_datatype_fundef(self, root: ET.Element) -> None:
        fun_key = root.attrib["NAME"]
        fundef_attributes = root.attrib
        _remove_index_from_dictionary("NAME", fundef_attributes)

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
            _remove_index_from_dictionary("ORDINAL", parm_attributes)

            fundef_attributes["PARAMETERS"][parm_key] = parm_attributes

        self.xml_map["DATATYPES"]["FUNCTION_DEFS"][fun_key] = fundef_attributes

    def parse_datatypes(self, root: ET.Element) -> None:
        datatype_roots = root.findall("TYPE_DEF")
        self.xml_map["DATATYPES"]["TYPEDEFS"] = {}
        for typedef in datatype_roots:
            self.parse_datatype_typedef(typedef)

        datatype_roots = root.findall("STRUCTURE")
        self.xml_map["DATATYPES"]["STRUCTS"] = {}
        for struc in datatype_roots:
            self.parse_datatype_struct(struc)

        # Union have same structure as STRUCTURE, except name vs union unique
        datatype_roots = root.findall("UNION")
        self.xml_map["DATATYPES"]["UNIONS"] = {}
        for uni in datatype_roots:
            self.parse_datatype_union(uni)

        datatype_roots = root.findall("ENUM")
        self.xml_map["DATATYPES"]["ENUMS"] = {}
        for enu in datatype_roots:
            self.parse_datatype_enum(enu)

        datatype_roots = root.findall("FUNCTION_DEF")
        self.xml_map["DATATYPES"]["FUNCTION_DEFS"] = {}
        for fun in datatype_roots:
            self.parse_datatype_fundef(fun)

    def parse_memmap(self, root: ET.Element) -> None:
        mem_sects = root.findall("MEMORY_SECTION")
        for sec in mem_sects:
            mem_key = sec.attrib["START_ADDR"]
            mem_attributes = sec.attrib
            _remove_index_from_dictionary("START_ADDR", mem_attributes)

            self.xml_map["MEMORY_MAP"][mem_key] = mem_attributes
            mem_contents = sec.findall("MEMORY_CONTENTS")
            for cont in mem_contents:
                self.xml_map["MEMORY_MAP"][mem_key]["MEM_CONTENTS"] = cont.attrib

    def parse_regvals(self, root: ET.Element) -> None:
        # self.xml_map["REGISTER_VALUES"]
        pass

    def parse_code(self, root: ET.Element) -> None:
        code_roots = root.findall("CODE_BLOCK")
        for cod in code_roots:
            code_key = cod.attrib["START"]
            code_attributes = cod.attrib
            self.xml_map["CODE"][code_key] = code_attributes

    def parse_data(self, root: ET.Element) -> None:
        defined_roots = root.findall("DEFINED_DATA")
        for dat in defined_roots:
            data_key = dat.attrib["ADDRESS"]
            data_attributes = dat.attrib
            _remove_index_from_dictionary("ADDRESS", data_attributes)

            self.xml_map["DATA"][data_key] = data_attributes

    def parse_equates(self, root: ET.Element) -> None:
        # self.xml_map["EQUATES"]
        pass

    def parse_comments(self, root: ET.Element) -> None:
        comment_roots = root.findall("COMMENT")
        for comm in comment_roots:
            comment_key = comm.attrib["ADDRESS"]
            comment_attributes = comm.attrib
            _remove_index_from_dictionary("ADDRESS", comment_attributes)

            comment_attributes["BODY"] = comm.text
            self.xml_map["COMMENTS"][comment_key] = comment_attributes

    def parse_properties(self, root: ET.Element) -> None:
        prop_roots = root.findall("PROPERTY")
        for prop in prop_roots:
            prop_key = prop.attrib["NAME"]
            prop_attributes = prop.attrib
            _remove_index_from_dictionary("NAME", prop_attributes)

            self.xml_map["PROPERTIES"][prop_key] = prop_attributes

    def parse_bookmarks(self, root: ET.Element) -> None:
        bkmrk_roots = root.findall("BOOKMARK")
        for bkmrk in bkmrk_roots:
            bkmrk_key = bkmrk.attrib["ADDRESS"]
            bkmrk_attributes = bkmrk.attrib
            _remove_index_from_dictionary("ADDRESS", bkmrk_attributes)

            self.xml_map["BOOKMARKS"][bkmrk_key] = bkmrk_attributes

    def parse_fncts(self, root: ET.Element) -> None:
        fncts_roots = root.findall("FUNCTION")
        for fnct in fncts_roots:
            fnct_key = fnct.attrib["ENTRY_POINT"]
            fnct_attributes = fnct.attrib
            _remove_index_from_dictionary("ENTRY_POINT", fnct_attributes)

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
                    _remove_index_from_dictionary("STACK_PTR_OFFSET", stk_var.attrib)
                    fnct_attributes["STACK_FRAME"][offset] = stk_var.attrib

            # Register Variable related info
            fnct_attributes["REGISTER_VARS"] = {}
            reg_vars = fnct.findall("REGISTER_VAR")
            for reg_var in reg_vars:
                regvar_key = reg_var.attrib["NAME"]
                regvar_attributes = reg_var.attrib
                _remove_index_from_dictionary("NAME", regvar_attributes)

                fnct_attributes["REGISTER_VARS"][regvar_key] = regvar_attributes

            self.xml_map["FUNCTIONS"][fnct_key] = fnct_attributes

    def parse_progtree(self, root: ET.Element) -> None:
        # self.xml_map["PROGRAM_TREES"]
        pass

    def parse_entrypts(self, root: ET.Element) -> None:
        enter_roots = root.findall("PROGRAM_ENTRY_POINT")
        for ent in enter_roots:
            ent_key = ent.attrib["ADDRESS"]
            self.xml_map["PROGRAM_ENTRY_POINTS"][ent_key] = ""

    def parse_relocations(self, root: ET.Element) -> None:
        reloc_roots = root.findall("RELOCATION")
        for reloc in reloc_roots:
            reloc_key = reloc.attrib["ADDRESS"]
            reloc_attributes = reloc.attrib
            _remove_index_from_dictionary("ADDRESS", reloc_attributes)

            self.xml_map["RELOCATION_TABLE"][reloc_key] = reloc_attributes

    def parse_symtable(self, root: ET.Element) -> None:
        symtab_roots = root.findall("SYMBOL")
        for sym in symtab_roots:
            sym_key = sym.attrib["ADDRESS"]
            sym_attributes = sym.attrib
            _remove_index_from_dictionary("ADDRESS", sym_attributes)

            self.xml_map["SYMBOL_TABLE"][sym_key] = sym_attributes

    def parse_markup(self, root: ET.Element) -> None:
        markup_roots = root.findall("EXT_LIBRARY_REFERENCE")
        for mrkup in markup_roots:
            mrkup_key = mrkup.attrib["ADDRESS"]
            mrkup_attributes = mrkup.attrib
            _remove_index_from_dictionary("ADDRESS", mrkup_attributes)
            self.xml_map["MARKUP"][mrkup_key] = mrkup_attributes

    def parse_extlib(self, root: ET.Element) -> None:
        extlib_roots = root.findall("EXT_LIBRARY")
        for extlib in extlib_roots:
            extlib_key = extlib.attrib["NAME"]
            extlib_attributes = extlib.attrib
            _remove_index_from_dictionary("NAME", extlib_attributes)
            self.xml_map["EXT_LIBRARY_TABLE"][extlib_key] = extlib_attributes

    def parse_xml(self, xml_contents: str) -> Dict:
        # Parse xml string and access root
        root = ET.fromstring(xml_contents)

        # Root attributes, listing object file type, and name
        self.xml_map["PROG_INFO"] = root.attrib

        processor_root = root.find("PROCESSOR")
        if processor_root is not None:
            self.xml_map['PROCESSOR'] = {}
            self.parse_processor(processor_root)

        datatypes_root = root.find("DATATYPES")
        if datatypes_root is not None:
            self.xml_map["DATATYPES"] = {}
            self.parse_datatypes(datatypes_root)

        memmap_root = root.find("MEMORY_MAP")
        if memmap_root is not None:
            self.xml_map["MEMORY_MAP"] = {}
            self.parse_memmap(memmap_root)

        regvals_root = root.find("REGISTER_VALUES")
        if regvals_root is not None:
            self.xml_map["REGISTER_VALUES"] = {}
            self.parse_regvals(regvals_root)

        code_root = root.find("CODE")
        if code_root is not None:
            self.xml_map["CODE"] = {}
            self.parse_code(code_root)

        data_root = root.find("DATA")
        if data_root is not None:
            self.xml_map["DATA"] = {}
            self.parse_data(data_root)

        equates_root = root.find("EQUATES")
        if equates_root is not None:
            self.xml_map["EQUATES"] = {}
            self.parse_equates(equates_root)

        comments_root = root.find("COMMENTS")
        if comments_root is not None:
            self.xml_map["COMMENTS"] = {}
            self.parse_comments(comments_root)

        properties_root = root.find("PROPERTIES")
        if properties_root is not None:
            self.xml_map["PROPERTIES"] = {}
            self.parse_properties(properties_root)

        bookmarks_root = root.find("BOOKMARKS")
        if bookmarks_root is not None:
            self.xml_map["BOOKMARKS"] = {}
            self.parse_bookmarks(bookmarks_root)

        fncts_root = root.find("FUNCTIONS")
        if fncts_root is not None:
            self.xml_map["FUNCTIONS"] = {}
            self.parse_fncts(fncts_root)

        progtree_root = root.find("PROGRAM_TREES")
        if progtree_root is not None:
            self.xml_map["PROGRAM_TREES"] = {}
            self.parse_progtree(progtree_root)

        entrypts_root = root.find("PROGRAM_ENTRY_POINTS")
        if entrypts_root is not None:
            self.xml_map["PROGRAM_ENTRY_POINTS"] = {}
            self.parse_entrypts(entrypts_root)

        relocations_root = root.find("RELOCATION_TABLE")
        if relocations_root is not None:
            self.xml_map["RELOCATION_TABLE"] = {}
            self.parse_relocations(relocations_root)

        symtable_root = root.find("SYMBOL_TABLE")
        if symtable_root is not None:
            self.xml_map["SYMBOL_TABLE"] = {}
            self.parse_symtable(symtable_root)

        markup_root = root.find("MARKUP")
        if markup_root is not None:
            self.xml_map["MARKUP"] = {}
            self.parse_markup(markup_root)

        extlib_root = root.find("EXT_LIBRARY_TABLE")
        if extlib_root is not None:
            self.xml_map["EXT_LIBRARY_TABLE"] = {}
            self.parse_extlib(extlib_root)

        return self.xml_map


class ObjectFile():
    # Todo: replace with Ghidra export entirely through easy api
    # Sections Data
    def __init__(self, xml: str, file: Optional[str] = None) -> None:
        self.file = file
        self.root = ET.fromstring(xml)
        self.xml_map = {}
        self.xml = xml
        self.intfuncttab = None
        self.extfuncttab = None
        self.strtab = None
        self.xml_map = XMLParser().parse_xml(xml)
        self.construct_memmap()
        self.construct_functtab()

    def get_xml(self) -> str:
        return self.xml

    def get_xmlmap(self) -> Dict:
        """ Accessor to XML Map, providing results to exported Ghidra
        """
        return self.xml_map

    def get_memmap(self) -> Dict:
        return self.memmap

    def get_sleighspec(self) -> Optional[str]:
        """
        TODO:: parse xml_map and identify cspec relevant features if possible
        """
        if "PROCESSOR" not in self.xml_map or "LANGUAGE_PROVIDER" not in self.xml_map["PROCESSOR"]:
            return None

        return self.xml_map["PROCESSOR"]["LANGUAGE_PROVIDER"]

    def get_compilerspec(self) -> Optional[str]:
        """
        TODO:: parse xml_map and identify cspec relevant features if possible
        """
        if "PROCESSOR" not in self.xml_map or "LANGUAGE_PROVIDER" not in self.xml_map["PROCESSOR"]:
            return None

        try:
            cspec_index = self.xml_map["PROCESSOR"]["LANGUAGE_PROVIDER"].rindex(':')
        except:
            print(f'Invalid Language Provider found when trying to set calling convention '
                  f'{self.xml_map["PROCESSOR"]["LANGUAGE_PROVIDER"]}. Ensure proper XML is '
                   'being found or update processor definitions in data files.')
            return None

        return self.xml_map["PROCESSOR"]["LANGUAGE_PROVIDER"][cspec_index+1:]

    def get_imagebase(self) -> Optional[int]:
        """
        TODO:: parse xml_map and identify cspec relevant features if possible
        """
        if "PROG_INFO" not in self.xml_map or "IMAGE_BASE" not in self.xml_map["PROG_INFO"]:
            return None

        image_base = int(self.xml_map["PROG_INFO"]["IMAGE_BASE"], 16)
        return image_base

    def get_intfuncttab(self) -> Dict:
        """ Returns internal function table
            Maps names to addresses of user functions
        """
        return self.intfuncttab

    def get_extfuncttab(self) -> Dict:
        """ Returns external function table
            Maps addresses to names of library functions EXTERNAL::
        """
        return self.extfuncttab

    def get_entrypoints(self) -> Optional[List[int]]:
        """
        """
        if "PROGRAM_ENTRY_POINTS" not in self.xml_map:
            return None

        return [int(entry, 16) for entry in self.xml_map["PROGRAM_ENTRY_POINTS"]]

    def construct_memmap(self) -> None:
        """ From exported XML construct a memory map
        """
        self.memmap = {}
        if "MEMORY_MAP" not in self.xml_map:
            return None

        for start, contents in self.xml_map["MEMORY_MAP"].items():
            # Only care about segments, not sections
            if "MEM_CONTENTS" not in contents:
                continue

            section_ref = open(self.file, 'rb')
            try:
                start = int(start, 16)
            except ValueError:
                print(f'section \"{contents["NAME"]}\" did not have valid start ({start})')
                continue

            section_ref.seek(int(contents["MEM_CONTENTS"]["FILE_OFFSET"], 16))
            sec_data = section_ref.read(start)
            self.memmap[contents["NAME"]] = {'start': start,
                                             'end': start + int(contents['LENGTH'], 16),
                                             'permissions': contents['PERMISSIONS'],
                                             'value': sec_data
                                            }
            section_ref.close()

    def construct_functtab(self):
        self.intfuncttab = {}
        self.extfuncttab = {}
        if "FUNCTIONS" not in self.xml_map:
            print('functions entry in XML not found, no symbol map created.')
            return None

        for function, meta in self.xml_map["FUNCTIONS"].items():
            # Can't look for Library Call, as library calls show as n as well
            if '<EXTERNAL>::' in meta['NAME']:
                self.extfuncttab[int(function, 16)] = meta['NAME'].replace('<EXTERNAL>::', '')
            else:
                self.intfuncttab[meta['NAME']] = int(function, 16)

        # print(f'External symbolMap {self.extfuncttab}')
        # print(f'Internal symbolMap {self.intfuncttab}')


class Memory:
    """
        TODO, uninit
    """
    def __init__(self, binary_memory: Dict) -> None:
        self.segments: dict = binary_memory
        self.last_segment_access = None

        print(f'Constructed memory map with {len(self.segments)} segments of memory.')

    def find_segment_waddr(self, addr: int) -> Tuple[Optional[str], Optional[dict]]:
        """ Given an address, find the relevant section containg this address
        """
        for segment, contents in self.segments.items():
            # Commenting out to make analysis more readable
            # print(f'Memory access within {segment} segment.')
            if contents['start'] <= addr < contents['end']:
                if segment != self.last_segment_access:
                    # Low probability to sort sections based on last recently access
                    self._performance_sort_segments()
                return segment, contents
        return None, None

    def __getitem__(self, addr: Union[int, slice]) -> Optional[bytes]:
        """ From segment that contains address, return data at offset from start of segment
        """
        if isinstance(addr, int):
            segment_name, segment = self.find_segment_waddr(addr)
            if segment is None:
                print(addr, f'Invalid memory access into non-loaded memory at {addr}')
                return

            # Commenting out to make analysis more readable
            # debug(segment)
            offset = addr - segment['start']
            self.last_segment_access = segment_name

            return segment['value'][offset:offset+MAX_INST_SIZE]
        elif isinstance(addr, slice):
            addr_slice = addr
            addr = addr_slice.start
            end = addr_slice.stop
            stride = addr_slice.step
            segment_name, segment = self.find_segment_waddr(addr)
            if segment is None:
                print(addr, f'Invalid memory access into non-loaded memory at {addr}')
                return

            # Commenting out to make analysis more readable
            # debug(segment)
            offset = addr - segment['start']
            self.last_segment_access = segment_name

            return segment['value'][offset:offset+(end-addr)]
        else:
            raise TypeError("Invalid addr type")

    def _performance_sort_segments(self):
        if self.last_segment_access is None:
            return

        random_pick = int(100*random.random())
        # print(f'Attempting to order segments ({random_pick}:{THRESHOLD}) {self.last_segment_access}')
        if random_pick > THRESHOLD:
            # Usually do nothing
            return
        keys = list(self.segments.keys())

        # get index of last recent segment
        last_recent_index = keys.index(self.last_segment_access)
        # reorder list with last recent up front
        keys.insert(0, keys.pop(last_recent_index))

        self.segments = {k: self.segments[k] for k in self.segments}


def all_things(args, opts):
    """
        Collects all information Ghidra would have and debug info from instructions in binary
        Syntax: compare_funcs oid
        Options:
            file - specifies dumping to output file
            dir - specifies out directory to dump output files
            verbose - Includes breakdown of instuctions per tool
            color - Adds coloring to output to make easier to view
    """
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")
    valid = api.expand_oids(valid)

    print(opts)

    res = {}
    for oid in valid:
        print(oid)
        res[oid] = {}
        options = {'disassembler': 'ghidra_disasm'}

        src = api.source(oid)
        data = api.get_field(src, oid, "data", {})
        f_name = api.get_field("file_meta", oid, "names").pop()
        f_name = api.tmp_file(f_name, data)

        disasm = api.retrieve('disassembly', oid, options)
        if not disasm:
            continue

        disasm = disasm.pop(list(disasm.keys())[0])["instructions"]
        ghidra_disasm = api.get_field("ghidra_disasm", oid, "instructions", {'rebase-off': True})
        decomp_mapping = api.get_field("ghidra_decmap", oid, "decompile")
        xml = api.get_field("ghidra_export", oid, "raw", {})
        binary = ObjectFile(xml, f_name)
        sleighspec = binary.get_sleighspec()
        print(f"Detected architecture: {sleighspec}")
        image_base = binary.get_imagebase()
        print(f"Image Base {image_base}")

        file_cache = {}

        # account for no-cspec
        compiler_index = sleighspec.rindex(':')
        arch = sleighspec[:compiler_index]

        # List supported languages
        langs = {l.id:l for arch in Arch.enumerate() for l in arch.languages}

        # Get requested language
        if arch not in langs:
            print(f'Language "{arch}" not found.')
            print(f'Supported languages: {langs}')
            t = arch.upper()
            suggestions = [l for l in langs if SequenceMatcher(None, t, l.split()[0].upper()).ratio() > 0.25]
            if len(suggestions):
                print('\nSuggestions:')
                for langid in sorted(suggestions):
                    print('  %-35s - %s' % (langid, langs[langid].description))
                print('')
            exit(1)

        # Translate
        ctx = Context(langs[arch])
        memory = Memory(binary.get_memmap())

        i = len(disasm)
        j = 0
        with alive_bar(i) as bar:
            for (offset, addr) in zip(disasm, ghidra_disasm):
                if j > 800:
                    break
                j += 1
                disasm_instruction = disasm[offset]
                res[oid][offset] = {}
                lifted_result = ctx.translate(memory[addr], addr, 1)
                try:
                    res_insn = lifted_result.instructions[0]
                except:
                    # print('bad_lift')
                    res_insn = None

                # TODO, zfill?
                res[oid][offset]['address'] = addr
                res[oid][offset]['bytes'] = disasm_instruction['bytes'].hex()
                if res_insn is not None:
                    res[oid][offset]['insn'] = f'{res_insn.asm_mnem} {res_insn.asm_body}'
                    res[oid][offset]['pcode'] = []
                    for op in res_insn.ops:
                        res[oid][offset]['pcode'].append(str(op))

                # print(addr)
                # TODO:: replace with high_dwarf
                src_line = str(check_output(f"addr2line -e {f_name} -a {hex(offset)} -f", shell=True, universal_newlines=True))
                # ?? signifies missing symbol lookup, maybe mapping of address or usage, or no debug info
                res[oid][offset]['src'] = 'N/A'
                if '??' not in src_line:
                    print(src_line.split('\n'))
                    arg_address, func, file_and_line, _ = src_line.split('\n')
                    file, line = file_and_line.split(':')
                    res[oid][offset]['src'] = {"file": file, "line": line}
                    res[oid][offset]['mapped_src'] = {"file": file, "line": line}

                    res[oid][offset]['src_line'] = ""
                # res[oid][offset]['dbg_src'] = src_line
                if decomp_mapping and offset in decomp_mapping:
                    res[oid][offset]['decomp'] = decomp_mapping[offset]
                else:
                    res[oid][offset]['decomp'] = 'N/A'
                bar()

        for _, fd in file_cache.items():
            fd.close()

    import json
    print(json.dumps(res, indent=4))


exports = [all_things]