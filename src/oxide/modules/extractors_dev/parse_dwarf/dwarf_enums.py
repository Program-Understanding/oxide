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

""" DWARF Structure and ENUMS found here https://dwarfstd.org/doc/DWARF4.pdf
"""


# ------------------------------ DWARF -------------------------------------

CU64_STR = "IQHQB"  # len, version, abbrev, addr_size
CU32_STR = "=IHIB"  # len, version, abbrev, addr_size
# (must specify endianess to remove padding within struct)

DIE_STR = "BB"

DEBUG_LINE_64_STR = "IHQBBBbBB"
DEBUG_LINE_32_STR = "=IHIBBbBB"
ARANGE_64_STR = "IQHQBB"
ARANGE_32_STR = "=IHIBB"

ADDR_FORM_32_STR = "I"
ADDR_FORM_64_STR = "Q"

DATA1_STR = "B"   # DW_FORM_data1
DATA2_STR = "H"   # DW_FORM_data2
DATA4_STR = "I"   # DW_FORM_data4
DATA8_STR = "Q"   # DW_FORM_data8

# Type 1 References
REFERENCE1_STR = "B"  # DW_FORM_ref1
REFERENCE2_STR = "H"  # DW_FORM_ref2
REFERENCE4_STR = "I"  # DW_FORM_ref4
REFERENCE8_STR = "Q"  # DW_FORM_ref8

# Type 2 References
REFERENCE_ADDR_32_STR = "I"  # DW_FORM_ref_addr
REFERENCE_ADDR_64_STR = "Q"  # DW_FORM_ref_addr

# Type 3 References
REFERENCE_SIG8_STR = "Q"  # DW_FORM_ref_sig8

LINEPTR64_STR = "Q"
LINEPTR32_STR = "I"

# FORM classes. Each attr_form will be a part of one of these classes
# This is necessary to determine how attribute values will be decoded
ADDRESS = ["DW_FORM_addr"]
BLOCK = ["DW_FORM_block1", "DW_FORM_block2", "DW_FORM_block4", "DW_FORM_block"]
CONSTANT = ["DW_FORM_data1", "DW_FORM_data2", "DW_FORM_data4", "DW_FORM_data8", "DW_FORM_sdata",
            "DW_FORM_udata"]
EXPRLOC = ["DW_FORM_exprloc"]
FLAG = ["DW_FORM_flag", "DW_FORM_flag_present"]
# These all use generic offset
SEC_OFFSET = ["DW_FORM_sec_offset"]
RANGELISTPTR = ["DW_FORM_sec_offset"]
RANGE = ["DW_FORM_ref_addr", "DW_FORM_ref1", "DW_FORM_ref2", "DW_FORM_ref4", "DW_FORM_ref8",
         "DW_FORM_ref_udata", "DW_FORM_ref_sig8"]
STRING = ["DW_FORM_string", "DW_FORM_strp"]

# Following dictionaries map hex values to their appropriate names
DWARF_TAG_MAP_E = {
    0x1: "DW_TAG_array_type",
    0x2: "DW_TAG_class_type",
    0x3: "DW_TAG_entry_point",
    0x4: "DW_TAG_enumeration_point",
    0x5: "DW_TAG_formal_parameter",
    0x8: "DW_TAG_imported_declaration",
    0xa: "DW_TAG_label",
    0xb: "DW_TAG_lexical_block",
    0xd: "DW_TAG_member",
    0xf: "DW_TAG_pointer_type",
    0x10: "DW_TAG_reference_type",
    0x11: "DW_TAG_compile_unit",
    0x12: "DW_TAG_string_type",
    0x13: "DW_TAG_structure_type",
    0x15: "DW_TAG_subroutine_type",
    0x16: "DW_TAG_typedef",
    0x17: "DW_TAG_union_type",
    0x18: "DW_TAG_unspecified_parameters",
    0x19: "DW_TAG_variant",
    0x1a: "DW_TAG_common_block",
    0x1b: "DW_TAG_common_inclusion",
    0x1c: "DW_TAG_inheritance",
    0x1d: "DW_TAG_inlined_subroutine",
    0x1e: "DW_TAG_module",
    0x1f: "DW_TAG_ptr_to_member_type",
    0x20: "DW_TAG_set_type",
    0x21: "DW_TAG_subrange_type",
    0x22: "DW_TAG_with_stmt",
    0x23: "DW_TAG_access_declaration",
    0x24: "DW_TAG_base_type",
    0x25: "DW_TAG_catch_block",
    0x26: "DW_TAG_const_type",
    0x27: "DW_TAG_constant",
    0x28: "DW_TAG_enumerator",
    0x29: "DW_TAG_file_type",
    0x2a: "DW_TAG_friend",
    0x2b: "DW_TAG_namelist",
    0x2c: "DW_TAG_namelist_item",
    0x2d: "DW_TAG_packed_type",
    0x2e: "DW_TAG_subprogram",
    0x2f: "DW_TAG_template_type_parameter",
    0x30: "DW_TAG_template_value_parameter",
    0x31: "DW_TAG_thrown_type",
    0x32: "DW_TAG_try_block",
    0x33: "DW_TAG_variant_part",
    0x34: "DW_TAG_variable",
    0x35: "DW_TAG_volatile_type",
    0x36: "DW_TAG_dwarf_procedure",
    0x37: "DW_TAG_restrict_type",
    0x38: "DW_TAG_interface_type",
    0x39: "DW_TAG_namespace",
    0x3a: "DW_TAG_imported_module",
    0x3b: "DW_TAG_unspecified_type",
    0x3c: "DW_TAG_partial_unit",
    0x3d: "DW_TAG_imported_unit",
    0x3f: "DW_TAG_condition",
    0x40: "DW_TAG_shared_type",
    0x41: "DW_TAG_type_unit",
    0x42: "DW_TAG_rvalue_reference_type",
    0x43: "DW_TAG_template_alias",
    0x4080: "DW_TAG_lo_user",
    0xffff: "DW_TAG_hi_user"
}

DWARF_ATTR_MAP_E = {
    0x1: "DW_AT_sibling",
    0x2: "DW_AT_location",
    0x3: "DW_AT_name",
    0x9: "DW_AT_ordering",
    0xb: "DW_AT_byte_size",
    0xc: "DW_AT_bit_offset",
    0xd: "DW_AT_bit_size",
    0x10: "DW_AT_stmt_list",
    0x11: "DW_AT_low_pc",
    0x12: "DW_AT_high_pc",
    0x13: "DW_AT_language",
    0x15: "DW_AT_discr",
    0x16: "DW_AT_discr_value",
    0x17: "DW_AT_visibility",
    0x18: "DW_AT_import",
    0x19: "DW_AT_string_length",
    0x1a: "DW_AT_common_reference",
    0x1b: "DW_AT_comp_dir",
    0x1c: "DW_AT_const_value",
    0x1d: "DW_AT_containing_type",
    0x1e: "DW_AT_default_value",
    0x20: "DW_AT_inline",
    0x21: "DW_AT_is_optional",
    0x22: "DW_AT_lower_bound",
    0x25: "DW_AT_producer",
    0x27: "DW_AT_prototyped",
    0x2a: "DW_AT_return_addr",
    0x2c: "DW_AT_start_scope",
    0x2e: "DW_AT_bit_stride",
    0x2f: "DW_AT_upper_bound",
    0x31: "DW_AT_abstract_origin",
    0x32: "DW_AT_accessibility",
    0x33: "DW_AT_address_class",
    0x34: "DW_AT_artificial",
    0x35: "DW_AT_base_types",
    0x36: "DW_AT_calling_convention",
    0x37: "DW_AT_count",
    0x38: "DW_AT_data_member_location",
    0x39: "DW_AT_decl_column",
    0x3a: "DW_AT_decl_file",
    0x3b: "DW_AT_decl_line",
    0x3c: "DW_AT_declaration",
    0x3d: "DW_AT_discr_list",
    0x3e: "DW_AT_encoding",
    0x3f: "DW_AT_external",
    0x40: "DW_AT_frame_base",
    0x41: "DW_AT_friend",
    0x42: "DW_AT_identifier_base",
    0x43: "DW_AT_macro_info",
    0x44: "DW_AT_namelist_item",
    0x45: "DW_AT_priority",
    0x46: "DW_AT_segment",
    0x47: "DW_AT_specification",
    0x48: "DW_AT_static_link",
    0x49: "DW_AT_type",
    0x4a: "DW_AT_use_location",
    0x4b: "DW_AT_variable_parameter",
    0x4c: "DW_AT_virtuality",
    0x4d: "DW_AT_vtable_elem_location",
    0x4e: "DW_AT_allocated",
    0x4f: "DW_AT_associated",
    0x50: "DW_AT_data_location",
    0x51: "DW_AT_byte_stride",
    0x52: "DW_AT_entry_pc",
    0x53: "DW_AT_use_UTF8",
    0x54: "DW_AT_extension",
    0x55: "DW_AT_ranges",
    0x56: "DW_AT_trampoline",
    0x57: "DW_AT_call_column",
    0x58: "DW_AT_call_file",
    0x59: "DW_AT_call_line",
    0x5a: "DW_AT_description",
    0x5b: "DW_AT_binary_scale",
    0x5c: "DW_AT_decimal_scale",
    0x5d: "DW_AT_small",
    0x5e: "DW_AT_decimal_sign",
    0x5f: "DW_AT_digit_count",
    0x60: "DW_AT_picture_string",
    0x61: "DW_AT_mutable",
    0x62: "DW_AT_threads_scaled",
    0x63: "DW_AT_explicit",
    0x64: "DW_AT_object_pointer",
    0x65: "DW_AT_endianity",
    0x66: "DW_AT_elemental",
    0x67: "DW_AT_pure",
    0x68: "DW_AT_recursive",
    0x69: "DW_AT_siganture",
    0x6a: "DW_AT_main_subprogram",
    0x6b: "DW_AT_data_bit_offset",
    0x6c: "DW_AT_const_expr",
    0x6d: "DW_AT_enum_class",
    0x6e: "DW_AT_linkage_name",
    0x2000: "DW_AT_lo_user",
    0x3fff: "DW_AT_hi_user",
    0x2111: "DW_AT_GNU_call_site_value",
    0x2112: "DW_AT_GNU_call_site_data_value",
    0x2113: "DW_AT_GNU_call_site_target",
    0x2114: "DW_AT_GNU_call_site_target_clobbered",
    0x2115: "DW_AT_GNU_tail_call",
    0x2116: "DW_AT_GNU_all_tail_call_sites",
    0x2117: "DW_AT_GNU_all_call_sites",
    0x2118: "DW_AT_GNU_all_source_call_sites",
    0x2119: "DW_AT_GNU_macros",
}

DWARF_FORM_MAP_E = {
    0x1: "DW_FORM_addr",
    0x3: "DW_FORM_block2",
    0x4: "DW_FORM_block4",
    0x5: "DW_FORM_data2",
    0x6: "DW_FORM_data4",
    0x7: "DW_FORM_data8",
    0x8: "DW_FORM_string",
    0x9: "DW_FORM_block",
    0xa: "DW_FORM_block1",
    0xb: "DW_FORM_data1",
    0xc: "DW_FORM_flag",
    0xd: "DW_FORM_sdata",
    0xe: "DW_FORM_strp",
    0xf: "DW_FORM_udata",
    0x10: "DW_FORM_ref_addr",
    0x11: "DW_FORM_ref1",
    0x12: "DW_FORM_ref2",
    0x13: "DW_FORM_ref4",
    0x14: "DW_FORM_ref8",
    0x15: "DW_FORM_ref_udata",
    0x16: "DW_FORM_indirect",
    0x17: "DW_FORM_sec_offset",
    0x18: "DW_FORM_exprloc",
    0x19: "DW_FORM_flag_present",
    0x20: "DW_FORM_ref_sig8"
}

DWARF_LANGUAGE_MAP_E = {
    0x1: "C89",
    0x2: "C",
    0x3: "Ada83",
    0x4: "C++",
    0x5: "Cobol74++",
    0x6: "Cobol85",
    0x7: "Fortran77",
    0x8: "Fortran90",
    0x9: "Pascal83",
    0xa: "Modula2",
    0xb: "Java",
    0xc: "C99",
    0xd: "Ada95",
    0xe: "Fortran95",
    0xf: "PLI",
    0x10: "ObjC",
    0x11: "ObjC++",
    0x12: "UPC",
    0x13: "D",
    0x14: "Python",
    0x8000: "lo_user",
    0xffff: "hi_user"
}

DWARF_OP_MAP_E = {
    0x3: "DW_OP_addr",
    0x6: "DW_OP_deref",
    0x8: "DW_OP_const1u",
    0x9: "DW_OP_const1s",
    0xa: "DW_OP_const2u",
    0xb: "DW_OP_const2s",
    0xc: "DW_OP_const4u",
    0xd: "DW_OP_const4s",
    0xe: "DW_OP_const8u",
    0xf: "DW_OP_const8s",
    0x10: "DW_OP_constu",
    0x11: "DW_OP_consts",
    0x12: "DW_OP_dup",
    0x13: "DW_OP_drop",
    0x14: "DW_OP_over",
    0x15: "DW_OP_pick",
    0x16: "DW_OP_swap",
    0x17: "DW_OP_rot",
    0x18: "DW_OP_xderef",
    0x19: "DW_OP_abs",
    0x1a: "DW_OP_and",
    0x1b: "DW_OP_div",
    0x1c: "DW_OP_minus",
    0x1d: "DW_OP_mod",
    0x1e: "DW_OP_mul",
    0x1f: "DW_OP_neg",
    0x20: "DW_OP_not",
    0x21: "DW_OP_or",
    0x22: "DW_OP_plus",
    0x23: "DW_OP_plus_uconst",
    0x24: "DW_OP_shl",
    0x25: "DW_OP_shr",
    0x26: "DW_OP_shra",
    0x27: "DW_OP_xor",
    0x2f: "DW_OP_skip",
    0x28: "DW_OP_bra",
    0x29: "DW_OP_eq",
    0x2a: "DW_OP_ge",
    0x2b: "DW_OP_gt",
    0x2c: "DW_OP_le",
    0x2d: "DW_OP_lt",
    0x2e: "DW_OP_ne",
    0x30: "DW_OP_lit0",   # Things start to change a little here, refer to pg.166 of dwarfv4
    0x31: "DW_OP_lit1",
    0x4f: "DW_OP_lit31",
    0x50: "DW_OP_reg0",
    0x51: "DW_OP_reg1",
    0x6f: "DW_OP_reg31",
    0x70: "DW_OP_breg0",
    0x71: "DW_OP_breg1",
    0x8f: "DW_OP_breg31",
    0x90: "DW_OP_regx",
    0x91: "DW_OP_fbreg",
    0x92: "DW_OP_bregx",
    0x93: "DW_OP_piece",
    0x94: "DW_OP_deref_size",
    0x95: "DW_OP_xderef_size",
    0x96: "DW_OP_nop",
    0x97: "DW_OP_push_object_address",
    0x98: "DW_OP_call2",
    0x99: "DW_OP_call4",
    0x9a: "DW_OP_call_ref",
    0x9b: "DW_OP_form_tls_address",
    0x9c: "DW_OP_call_frame_cfa",
    0x9d: "DW_OP_bit_piece",
    0x9e: "DW_OP_implicit_value",
    0x9f: "DW_OP_stack_value",
    0xe0: "DW_OP_lo_user",
    0xff: "DW_OP_hi_user"
}

DWARF_LNS_MAP_E = {
    0x01: "DW_LNS_copy",
    0x02: "DW_LNS_advance_pc",
    0x03: "DW_LNS_advance_line",
    0x04: "DW_LNS_set_file",
    0x05: "DW_LNS_set_column",
    0x06: "DW_LNS_negate_stmt",
    0x07: "DW_LNS_set_basic_block",
    0x08: "DW_LNS_const_add_pc",
    0x09: "DW_LNS_fixed_advance_pc",
    0x0a: "DW_LNS_set_prologue_end",
    0x0b: "DW_LNS_set_epilogue_begin",
    0x0c: "DW_LNS_set_isa",
}

DWARF_LNE_MAP_E = {
    0x01: "DW_LNS_end_sequence",
    0x02: "DW_LNS_set_address",
    0x03: "DW_LNS_define_file",
    0x04: "DW_LNS_set_descriminator",
    0x80: "DW_LNS_lo_user",
    0xff: "DW_LNS_hi_user",
}
