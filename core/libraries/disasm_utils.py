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

""" disasm_utils.py
Utility file to handle xed, capstone, and in the future (zydis, libdasm, libbfd)
functions to read and translate xed and capstone interactions/disassemblies
"""

import logging
import ctypes

from typing import Optional, List, Dict, Any

NAME = "disasm_utils"
logger = logging.getLogger(NAME)
logger.debug("init")

AVAILABLE = ["xed", "capstone"]

try:
    import capstone
except ModuleNotFoundError:
    AVAILABLE.remove("capstone")
    logger.warning("Unable to import Capstone.")

try:
    import pyxed
except ModuleNotFoundError:
    AVAILABLE.remove("xed")
    logger.warning("Unable to import PyXED.")

if not AVAILABLE:
    raise ModuleNotFoundError("PyXED and Capstone are missing.")


def disassemble_wxed(file_size, data, header, tool_insns):
    """ Produce disassembly from XED

    Args:
        header (header_interface) - interface to program under test header
        tool_insns         (dict) - set of instructions found from chosen tool
    """
    if header.machine in ("x86", "x86_64"):
        if header.insn_mode == 32:
            mode = pyxed.XED_MACHINE_MODE_LEGACY_32
            addr_width = pyxed.XED_ADDRESS_WIDTH_32b
        elif header.insn_mode == 64:
            mode = pyxed.XED_MACHINE_MODE_LONG_64
            addr_width = pyxed.XED_ADDRESS_WIDTH_64b
    else:
        return None

    disasm = {}
    for offset in tool_insns.keys():
        # TODO:: move outside of loop and flush instruction buffer correctly
        # Initialized in loop to flush instruction buffer
        xed = pyxed.Decoder()
        xed.set_mode(mode, addr_width)

        if isinstance(offset, str): continue
        if not offset or offset > file_size: logger.error("BAD OFFSET in disassembly")

        xed.itext = data[offset:]
        # relevant for branches showing correct dests in rvia
        xed.runtime_address = header.get_rva(offset)
        try:
            inst = xed.decode()
            if str(inst.dump_intel_format()) == "invalid":
                inst = None
        except pyxed.InvalidInstructionError:
            inst = None

        if inst is None:
            logging.error("XED did not find instruction at offset %s", offset)
            continue
        # Result of dir on inst object
        # flags 'conditionally_writes_registers', 'is_immediate_signed', 'is_mem_read', 'is_mem_written', 'is_mem_written_only', 'uses_rflags'
        # functions 'dump_intel_format',
        # accessors 'get_attribute', 'get_base_reg', 'get_branch_displacement', 'get_branch_displacement_width',
        #           'get_branch_displacement_width_bits', 'get_category', 'get_category_str', 'get_extension',
        #           'get_extension_str', 'get_iclass', 'get_iclass_str', 'get_iform', 'get_iform_str',
        #           'get_immediate_width', 'get_immediate_width_bits', 'get_index_reg', 'get_isa_set',
        #           'get_isa_set_str', 'get_length', 'get_memory_displacement', 'get_memory_displacement_width',
        #           'get_memory_displacement_width_bits', 'get_memory_operand_length', 'get_modrm', 'get_noperands',
        #           'get_nprefixes', 'get_number_of_memory_operands', 'get_operand', 'get_operand_length',
        #           'get_operand_length_bits', 'get_reg', 'get_rflags_read', 'get_rflags_undefined', 'get_rflags_written',
        #           'get_scale', 'get_second_immediate', 'get_seg_reg', 'get_signed_immediate', 'get_unsigned_immediate',
        #           'runtime_address', 'set_branch_displacement', 'set_branch_displacement_bits', 'set_memory_displacement', 'set_memory_displacement_bits'
        disasm[offset] = {}
        disasm[offset]["str"] = inst.dump_intel_format()
        disasm[offset]["size"] = inst.get_length()
        disasm[offset]["groups"] = [inst.get_category_str()]
        disasm[offset]["operand_size"] = inst.get_immediate_width()

        # Compute read and written registers
        disasm[offset]["regs_write"] = []
        disasm[offset]["regs_read"] = []
        inst_list = disasm[offset]["str"].split()
        disasm[offset]["op_str"] = ' '.join(inst_list[1:]) if (len(inst_list) > 1) else ''
        disasm[offset]["op_val"] = ""
        for i in range(inst.get_noperands()):
            op = inst.get_operand(i)

            disasm[offset]["op_val"] += op.get_name_str()
            if op.is_register():
                reg_name = xed_get_reg_name(inst.get_reg(op.get_name()))
                if op.is_read_and_written():
                    disasm[offset]["regs_read"].append(reg_name)
                    disasm[offset]["regs_write"].append(reg_name)
                elif op.is_read_only():
                    disasm[offset]["regs_read"].append(reg_name)
                elif op.is_written_only():
                    disasm[offset]["regs_write"].append(reg_name)
    return disasm


def disassemble_wcap(file_size, data, header, tool_insns) -> Optional[dict]:
    """ Produce disassembly from capstone

    Args:
        file_size
        data
        header
        tool_insns
    """
    if header.machine == "ARM":
        logger.debug("ARM not well supported by this module")
        if header.insn_mode == 32:
            machine = capstone.CS_ARCH_ARM
            mode = capstone.CS_MODE_ARM
        elif header.insn_mode == 64:
            machine = capstone.CS_ARCH_ARM64
            mode = capstone.CS_MODE_ARM
        else:
            return None
    elif header.machine in ("x86", "x86_64"):
        machine = capstone.CS_ARCH_X86
        if header.insn_mode == 32:
            mode = capstone.CS_MODE_32
        elif header.insn_mode == 64:
            mode = capstone.CS_MODE_64
        else:
            return None
    else:
        # Unknown machine and instructino mode combo
        return None

    cap = capstone.Cs(machine, mode)

    cap.detail = True  # enable more information collected in capstone
    disasm = {}
    for offset in tool_insns.keys():
        # get offset from addresss in tool, or get offset from tool
        if not offset or isinstance(offset, str) or offset > file_size:
            logger.error("BAD OFFSET in disassembly %s (%s)", offset, hex(offset) if offset is not None else "NONE")
            continue

        # Fetch instruction
        try:
            insn = next(cap.disasm(data[offset:], offset, 1))
        except (StopIteration, ctypes.ArgumentError):
            save_mode = cap.mode
            try:
                if header.machine == "ARM":
                    # try decoding as thumb
                    cap.mode = capstone.CS_MODE_THUMB
                    insn = next(cap.disasm(data[offset:], offset, 1))
                    cap.mode = save_mode
            except (StopIteration, ctypes.ArgumentError, capstone.CsError):
                # restore mode for next instruction
                save_mode = cap.mode
                logger.debug("bad decode at offset %s bytes %s", offset,
                                                                 data[offset:offset + 8])
                continue

        if insn.id == 0:
            logger.info("insn id 0 at %s".format(addr))
            continue

        instruction = {}
        instruction['id']       = insn.id
        instruction['mnemonic'] = insn.mnemonic
        instruction['address']  = insn.address
        #instruction['bytes']    = insn.bytes
        instruction['op_str']   = insn.op_str
        instruction['size']     = insn.size
        instruction["str"]      = insn.mnemonic + " " + insn.op_str

        # instruction groups (control flow, arithmetic)
        try:
            instruction['groups'] = [insn.group_name(x) for x in insn.groups]
        except capstone.CsError:
            pass

        # Register access
        try:
            _regs_read = [insn.reg_name(x) for x in insn.regs_read]
            instruction['regs_read'] = _regs_read
        except capstone.CsError:
            _regs_read = None
        try:
            _regs_write = [insn.reg_name(x) for x in insn.regs_write]
            instruction['regs_write'] = _regs_write
        except capstone.CsError:
            _regs_write = None
        instruction['regs_access'] = (_regs_read, _regs_write)
        if machine == capstone.CS_ARCH_X86:
            dump_x86(insn, instruction)
            instruction['operands'] = dump_x86_operands(insn)
        elif machine == capstone.CS_ARCH_ARM64:
            dump_arm64(insn, instruction)
            instruction['operands'] = dump_arm64_operands(insn)
        elif machine == capstone.CS_ARCH_ARM:
            dump_arm(insn, instruction)
            instruction['operands'] = dump_arm_operands(insn)
        disasm[offset] = instruction

    return disasm


# ---- Dump instruction data ----

def get_eflag_name(eflag: int) -> str:
    """ Convert bit field in instruction flags to name of flag

        reference code: https://github.com/capstone-engine/capstone/blob/master/bindings/python/test_x86.py#L22
    """
    if eflag == capstone.x86.X86_EFLAGS_UNDEFINED_OF:
        return "UNDEF_OF"
    elif eflag == capstone.x86.X86_EFLAGS_UNDEFINED_SF:
        return "UNDEF_SF"
    elif eflag == capstone.x86.X86_EFLAGS_UNDEFINED_ZF:
        return "UNDEF_ZF"
    elif eflag == capstone.x86.X86_EFLAGS_MODIFY_AF:
        return "MOD_AF"
    elif eflag == capstone.x86.X86_EFLAGS_UNDEFINED_PF:
        return "UNDEF_PF"
    elif eflag == capstone.x86.X86_EFLAGS_MODIFY_CF:
        return "MOD_CF"
    elif eflag == capstone.x86.X86_EFLAGS_MODIFY_SF:
        return "MOD_SF"
    elif eflag == capstone.x86.X86_EFLAGS_MODIFY_ZF:
        return "MOD_ZF"
    elif eflag == capstone.x86.X86_EFLAGS_UNDEFINED_AF:
        return "UNDEF_AF"
    elif eflag == capstone.x86.X86_EFLAGS_MODIFY_PF:
        return "MOD_PF"
    elif eflag == capstone.x86.X86_EFLAGS_UNDEFINED_CF:
        return "UNDEF_CF"
    elif eflag == capstone.x86.X86_EFLAGS_MODIFY_OF:
        return "MOD_OF"
    elif eflag == capstone.x86.X86_EFLAGS_RESET_OF:
        return "RESET_OF"
    elif eflag == capstone.x86.X86_EFLAGS_RESET_CF:
        return "RESET_CF"
    elif eflag == capstone.x86.X86_EFLAGS_RESET_DF:
        return "RESET_DF"
    elif eflag == capstone.x86.X86_EFLAGS_RESET_IF:
        return "RESET_IF"
    elif eflag == capstone.x86.X86_EFLAGS_TEST_OF:
        return "TEST_OF"
    elif eflag == capstone.x86.X86_EFLAGS_TEST_SF:
        return "TEST_SF"
    elif eflag == capstone.x86.X86_EFLAGS_TEST_ZF:
        return "TEST_ZF"
    elif eflag == capstone.x86.X86_EFLAGS_TEST_PF:
        return "TEST_PF"
    elif eflag == capstone.x86.X86_EFLAGS_TEST_CF:
        return "TEST_CF"
    elif eflag == capstone.x86.X86_EFLAGS_RESET_SF:
        return "RESET_SF"
    elif eflag == capstone.x86.X86_EFLAGS_RESET_AF:
        return "RESET_AF"
    elif eflag == capstone.x86.X86_EFLAGS_RESET_TF:
        return "RESET_TF"
    elif eflag == capstone.x86.X86_EFLAGS_RESET_NT:
        return "RESET_NT"
    elif eflag == capstone.x86.X86_EFLAGS_PRIOR_OF:
        return "PRIOR_OF"
    elif eflag == capstone.x86.X86_EFLAGS_PRIOR_SF:
        return "PRIOR_SF"
    elif eflag == capstone.x86.X86_EFLAGS_PRIOR_ZF:
        return "PRIOR_ZF"
    elif eflag == capstone.x86.X86_EFLAGS_PRIOR_AF:
        return "PRIOR_AF"
    elif eflag == capstone.x86.X86_EFLAGS_PRIOR_PF:
        return "PRIOR_PF"
    elif eflag == capstone.x86.X86_EFLAGS_PRIOR_CF:
        return "PRIOR_CF"
    elif eflag == capstone.x86.X86_EFLAGS_PRIOR_TF:
        return "PRIOR_TF"
    elif eflag == capstone.x86.X86_EFLAGS_PRIOR_IF:
        return "PRIOR_IF"
    elif eflag == capstone.x86.X86_EFLAGS_PRIOR_DF:
        return "PRIOR_DF"
    elif eflag == capstone.x86.X86_EFLAGS_TEST_NT:
        return "TEST_NT"
    elif eflag == capstone.x86.X86_EFLAGS_TEST_DF:
        return "TEST_DF"
    elif eflag == capstone.x86.X86_EFLAGS_RESET_PF:
        return "RESET_PF"
    elif eflag == capstone.x86.X86_EFLAGS_PRIOR_NT:
        return "PRIOR_NT"
    elif eflag == capstone.x86.X86_EFLAGS_MODIFY_TF:
        return "MOD_TF"
    elif eflag == capstone.x86.X86_EFLAGS_MODIFY_IF:
        return "MOD_IF"
    elif eflag == capstone.x86.X86_EFLAGS_MODIFY_DF:
        return "MOD_DF"
    elif eflag == capstone.x86.X86_EFLAGS_MODIFY_NT:
        return "MOD_NT"
    elif eflag == capstone.x86.X86_EFLAGS_MODIFY_RF:
        return "MOD_RF"
    elif eflag == capstone.x86.X86_EFLAGS_SET_CF:
        return "SET_CF"
    elif eflag == capstone.x86.X86_EFLAGS_SET_DF:
        return "SET_DF"
    elif eflag == capstone.x86.X86_EFLAGS_SET_IF:
        return "SET_IF"
    else:
        return None


def dump_x86(insn, instruction) -> None:
    """ Compute x86 specific features of an insn, populate instruction dictionary

        reference code: https://github.com/capstone-engine/capstone/blob/master/bindings/python/test_x86.py#L133
            * Omits most functionality as specific to cpu arch

        # TODO:: integrate more
    """
    try:
        instruction['prefix']   = insn.prefix
    except ValueError:
        pass
    instruction['opcode']   = insn.opcode
    instruction['rex']      = insn.rex
    instruction['operand_size'] = insn.addr_size

    # operand size mode, and modrm
    instruction['modrm'] = insn.modrm

    if insn.eflags:
        updated_flags = []
        for i in range(0, 46):
            if insn.eflags & (1 << i):
                updated_flags.append(get_eflag_name(1 << i))
        instruction['eflags'] = updated_flags


def dump_arm(insn, instruction) -> None:
    """ Compute ARM specific features of an insn, populate instruction dictionary

        reference code: https://github.com/capstone-engine/capstone/blob/master/bindings/python/test_arm.py#L95
    """
    if insn.update_flags:
        instruction['update-flags'] = True
    if insn.writeback:
        instruction['write-back'] = True
    if insn.cc not in [capstone.arm.ARM_CC_AL, capstone.arm.ARM_CC_INVALID]:
        instruction['code-condition'] = insn.cc
    if insn.cps_mode:
        instruction['cpsi-mode'] = insn.cps_mode
    if insn.cps_flag:
        instruction['cpsi-flag'] = insn.cps_flag
    if insn.vector_data:
        instruction['vector-data'] = insn.vector_data
    if insn.vector_size:
        instruction['vector-size'] = insn.vector_size
    if insn.usermode:
        instruction['usermode'] = True
    if insn.mem_barrier:
        instruction['barrier'] = insn.mem_barrier


def dump_arm64(insn, instruction) -> None:
    """ Compute ARM64 specific features of an insn, populate instruction dictionary

        reference code: https://github.com/capstone-engine/capstone/blob/master/bindings/python/test_arm64.py#L86
    """
    if insn.writeback:
        instruction['write-back'] = True
    else:
        instruction['write-back'] = False

    instruction['code-condition'] = None
    if insn.cc not in [capstone.arm64.ARM64_CC_AL, capstone.arm64.ARM64_CC_INVALID]:
        instruction['code-condition'] = insn.cc

    if insn.update_flags:
        instruction['update-flags'] = True
    else:
        instruction['update-flags'] = False


# ---- Dump instruction operand information ----

def dump_x86_operands(insn) -> dict:
    """ Compute operand fields and characteristics given x86 instruction

        reference code: https://github.com/capstone-engine/capstone/blob/master/bindings/python/test_x86.py#L206
            * remove prints, and convert to dictionary storing
    """
    operands = {}

    if len(insn.operands) > 0:
        c = -1
        for i in insn.operands:
            c += 1
            operands['operand_%d' % c] = {}
            if i.type == capstone.x86.X86_OP_REG:
                operands['operand_%d' % c]['type.reg'] = insn.reg_name(i.reg)
            if i.type == capstone.x86.X86_OP_IMM:
                operands['operand_%d' % c]['type.imm'] = i.imm
            if i.type == capstone.x86.X86_OP_MEM:
                operands['operand_%d' % c]['type.mem'] = {}
                if i.mem.segment != 0:
                    operands['operand_%d' % c]['type.mem']['segment'] = insn.reg_name(i.mem.segment)  # noqa
                if i.mem.base != 0:
                    operands['operand_%d' % c]['type.mem']['base'] = insn.reg_name(i.mem.base)
                if i.mem.index != 0:
                    operands['operand_%d' % c]['type.mem']['index'] = insn.reg_name(i.mem.index)
                if i.mem.scale != 1:
                    operands['operand_%d' % c]['type.mem']['scale'] = i.mem.scale
                if i.mem.disp != 0:
                    operands['operand_%d' % c]['type.mem']['displacement'] = i.mem.disp
            operands['operand_%d' % c]['size'] = i.size

            if i.access == capstone.CS_AC_READ:
                operands['operand_%d' % c]['access'] = 'read'
            elif i.access == capstone.CS_AC_WRITE:
                operands['operand_%d' % c]['access'] = 'write'
            elif i.access == capstone.CS_AC_READ | capstone.CS_AC_WRITE:
                operands['operand_%d' % c]['access'] = 'read|write'
    return operands


def dump_arm_operands(insn) -> dict:
    """ Compute operand fields and characteristics given ARM instruction

        reference code: https://github.com/capstone-engine/capstone/blob/master/bindings/python/test_arm.py#L36
            * remove prints, and convert to dictionary storing
            * omitted some fields to keep main features, but keep relatively aligned with x86 features
    """
    operands = {}
    if len(insn.operands) > 0:
        c = -1
        for i in insn.operands:
            c += 1
            operands['operand_%d' % c] = {}
            if i.type == capstone.arm.ARM_OP_REG:
                operands['operand_%d' % c]['type.reg'] = insn.reg_name(i.reg)
            if i.type == capstone.arm.ARM_OP_IMM:
                operands['operand_%d' % c]['type.imm'] = i.imm
            if i.type == capstone.arm.ARM_OP_PIMM:
                operands['operand_%d' % c]['type.pimm'] = i.imm
            if i.type == capstone.arm.ARM_OP_CIMM:
                operands['operand_%d' % c]['type.cimm'] = i.imm
            if i.type == capstone.arm.ARM_OP_FP:
                operands['operand_%d' % c]['type.fp'] = i.fp
            if i.type == capstone.arm.ARM_OP_SYSREG:
                operands['operand_%d' % c]['type.sysreg'] = i.reg
            if i.type == capstone.arm.ARM_OP_SETEND:
                if i.setend == capstone.arm.ARM_SETEND_BE:
                    operands['operand_%d' % c]['type.setend'] = 'big endian'
                else:
                    operands['operand_%d' % c]['type.setend'] = 'little endian'
            if i.type == capstone.arm.ARM_OP_MEM:
                operands['operand_%d' % c]['type.mem'] = {}
                if i.mem.base != 0:
                    operands['operand_%d' % c]['type.mem']['base'] = insn.reg_name(i.mem.base)
                if i.mem.index != 0:
                    operands['operand_%d' % c]['type.mem']['index'] = insn.reg_name(i.mem.index)
                if i.mem.scale != 1:
                    operands['operand_%d' % c]['type.mem']['scale'] = insn.reg_name(i.mem.scale)
                if i.mem.disp != 0:
                    operands['operand_%d' % c]['type.mem']['displacement'] = insn.reg_name(i.mem.disp)  # noqa
                if i.mem.lshift != 0:
                    operands['operand_%d' % c]['type.mem']['lshift'] = insn.reg_name(i.mem.lshift)

            if i.neon_lane != -1:
                operands['operand_%d' % c]['neon_lane'] = i.neon_lane

            if i.access == capstone.CS_AC_READ:
                operands['operand_%d' % c]['access'] = 'read'
            elif i.access == capstone.CS_AC_WRITE:
                operands['operand_%d' % c]['access'] = 'write'
            elif i.access == capstone.CS_AC_READ | capstone.CS_AC_WRITE:
                operands['operand_%d' % c]['access'] = 'read|write'

            if i.shift.type != capstone.arm.ARM_SFT_INVALID and i.shift.value:
                operands['operand_%d' % c]['shift.type'] = i.shift.type
                operands['operand_%d' % c]['shift.value'] = i.shift.value

            if i.vector_index != -1:
                operands['operand_%d' % c]['vector_index'] = i.vector_index

            operands['operand_%d' % c]['subtracted'] = False
            if i.subtracted:
                operands['operand_%d' % c]['subtracted'] = True
    return operands


def dump_arm64_operands(insn) -> dict:
    """ Compute operand fields given an ARM64 bit instruction

        Reference code: https://github.com/capstone-engine/capstone/blob/master/bindings/python/test_arm64.py#L18
            * remove prints, and convert to dictionary storing
    """
    operands = {}
    if len(insn.operands) > 0:
        c = -1
        for i in insn.operands:
            c += 1
            operands['operand_%d' % c] = {}
            if i.type == capstone.arm64.ARM64_OP_REG:
                operands['operand_%d' % c]['type.reg'] = insn.reg_name(i.reg)
            if i.type == capstone.arm64.ARM64_OP_IMM:
                operands['operand_%d' % c]['type.imm'] = i.imm
            if i.type == capstone.arm64.ARM64_OP_CIMM:
                operands['operand_%d' % c]['type.c_imm'] = i.imm
            if i.type == capstone.arm64.ARM64_OP_FP:
                operands['operand_%d' % c]['type.fp'] = i.fp
            if i.type == capstone.arm64.ARM64_OP_MEM:
                operands['operand_%d' % c]['type.mem'] = {}
                if i.mem.base != 0:
                    operands['operand_%d' % c]['type.mem']['base'] = insn.reg_name(i.mem.base)
                if i.mem.index != 0:
                    operands['operand_%d' % c]['type.mem']['index'] = insn.reg_name(i.mem.index)
                if i.mem.disp != 0:
                    operands['operand_%d' % c]['type.mem']['displacement'] = i.mem.disp
            if i.type == capstone.arm64.ARM64_OP_REG_MRS:
                operands['operand_%d' % c]['reg_mrs'] = i.reg
            if i.type == capstone.arm64.ARM64_OP_REG_MSR:
                operands['operand_%d' % c]['reg_msr'] = i.reg
            if i.type == capstone.arm64.ARM64_OP_PSTATE:
                operands['operand_%d' % c]['pstate'] = i.pstate
            if i.type == capstone.arm64.ARM64_OP_SYS:
                operands['operand_%d' % c]['sys'] = i.sys
            if i.type == capstone.arm64.ARM64_OP_PREFETCH:
                operands['operand_%d' % c]['prefetch'] = i.prefetch
            if i.type == capstone.arm64.ARM64_OP_BARRIER:
                operands['operand_%d' % c]['barrier'] = i.barrier

            if i.shift.type != capstone.arm64.ARM64_SFT_INVALID and i.shift.value:
                operands['operand_%d' % c]['shift.type'] = i.shift.type
                operands['operand_%d' % c]['shift.value'] = i.shift.value

            if i.ext != capstone.arm64.ARM64_EXT_INVALID:
                operands['operand_%d' % c]['ext'] = i.ext

            if i.vas != capstone.arm64.ARM64_VAS_INVALID:
                operands['operand_%d' % c]['vector_arrangement'] = i.vas

            if i.vess != capstone.arm64.ARM64_VESS_INVALID:
                operands['operand_%d' % c]['vector_elem_size'] = i.vess

            if i.vector_index != -1:
                operands['operand_%d' % c]['vector_index'] = i.vector_index

            if i.access == capstone.CS_AC_READ:
                operands['operand_%d' % c]['access'] = 'read'
            elif i.access == capstone.CS_AC_WRITE:
                operands['operand_%d' % c]['access'] = 'write'
            elif i.access == capstone.CS_AC_READ | capstone.CS_AC_WRITE:
                operands['operand_%d' % c]['access'] = 'read|write'
    return operands


def xed_get_reg_name(reg):
    '''
    Return a register's name given its identifier as returned by `get_reg()' of
    class `Instruction'.
    '''

    reg_name = '?'
    for name in dir(pyxed):
        if name.startswith('XED_REG_') and getattr(pyxed, name) == reg:
            reg_name = name
            break
    return reg_name
