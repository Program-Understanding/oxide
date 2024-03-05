DESC = " Evaluate functions TLSH hash from a disassembly (uses ghidra_disasm or angr_disasm)"
NAME = "function_tlsh"
USG = " This module takes a collection of binary files and extracts from \
ghidra_disasm the functions, then calculates their TLSH hash. It returns \
a dictionary with the function name as a key and the TLSH hash as its \
key-value pair.\
set ghidra_disasm to False for emu_angr_disasm."

import logging
from oxide.core import api
import tlsh
logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"disasm": {"type": str, "mangle": False, "default": "ghidra_disasm", "description": "which disassembler module to use"}, "output_fun_name": {"type": bool, "mangle": False, "default": False, "description": "whether to output function names or their offsets"}, "output_vaddr": {"type": bool, "mangle": False, "default": False,"description":"whether to output function vaddr or function offset"}, "by_opcode": {"type": bool, "mangle": False, "default":False,"description":"generate TLSH hash by opcode/mnemonic instead of entire instruction"}}


def documentation():
    return {"description": DESC, "opts_doc": opts_doc,"set": False, "atomic": True, "usage": USG}

def process(oid, opts):
    if opts["output_fun_name"] and opts["output_vaddr"]:
        logger.info("Select to print either vaddress or function name, but not both")
        return False
    fun_dict = {}
    names = api.get_field("file_meta", oid, "names")

    #Get functions, bbs, disasm
    if opts["disasm"] != "ghidra_disasm":
        logger.info(f"Running {opts['disasm']} on {oid}...")
    funs = api.get_field(opts["disasm"], oid, "functions")
    if not funs:
        return False
    bbs = api.get_field(opts["disasm"], oid, "original_blocks")
    insns = api.get_field("disassembly", oid, oid)
    if insns and "instructions" in insns:
        insns = insns["instructions"]
    else:
        return False

    range = sorted(insns.keys())
    logger.info("Instruction range: %d - %d", range[0], range[-1])

    for f in funs:
        if f == 'meta':
            continue
        blocks = funs[f]['blocks']
        fun_string = ""
        fun_info = {}
        fun_len = 0
        fun_instr_count = 0
        for b in blocks:
            if b not in bbs: continue
            fun_instr_count += len(bbs[b]['members'])
            for insn_offset, insn_text in bbs[b]['members']:
                if insn_offset not in insns.keys():
                    logger.error("Basic Block member not found: %s", insn_offset)
                    continue
                fun_len += insns[insn_offset]['size']
                opcode = insn_text.split()
                if opts["by_opcode"] and opcode:
                    opcode = opcode[0]
                    # try to add destination register to opcode for more context and to avoid TNULL
                    if len(insn_text) > 3 and len(insn_text.split(' ')) > 2 and len(insn_text.split(' ')[2]) > 3:
                        target_dest = insn_text.split(' ')[2].split(",")
                        if len(target_dest[0]) == 3 and target_dest[0][-2] == 'a' and target_dest[0][-1] == 'x': #target is *ax
                            opcode += target_dest[0]
                    fun_string += opcode
                else:
                    for sub_str in opcode:
                        fun_string += sub_str

        if fun_instr_count > 5 and tlsh.hash(fun_string.encode()) != "TNULL":  # Eliminate functions that are just jumping to external
            fun_info["tlsh hash"] = tlsh.hash(fun_string.encode())
        else:
            fun_info["tlsh hash"] = None

        fun_info["len"] = fun_len
        if opts['output_fun_name']:
            fun_dict[funs[f]['name']] = fun_info
        elif opts['output_vaddr']:
            fun_dict[funs[f]['vaddr']] = fun_info
        else:
            fun_dict[f] = fun_info

    logger.debug("Storing")
    api.store(NAME, oid,fun_dict,opts)
    return True
