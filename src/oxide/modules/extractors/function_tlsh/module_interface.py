DESC = " Evaluate functions TLSH hash from a disassembly (uses ghidra_disasm)"
NAME = "function_tlsh"
USG = " This module takes a collection of binary files and extracts from \
ghidra_disasm the functions, then calculates their TLSH hash. It returns \
a dictionary with the function name as a key and the TLSH hash as its \
key-value pair."

import logging
from oxide.core import api
import tlsh
logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"ghidra_disasm": {"type": bool, "mangle": False, "default": True}, "output_fun_name": {"type": bool, "mangle": False, "default": False}, "output_vaddr": {"type": bool, "mangle": False, "default": False}}


def documentation():
    return {"description": DESC, "opts_doc": opts_doc,"set": False, "atomic": True, "usage": USG}

def process(oid, opts):
    if opts["output_fun_name"] and opts["output_vaddr"]:
        logger.info("Select to print either vaddress or function name, but not both")
        return False
    fun_dict = {}
    names = api.get_field("file_meta", oid, "names")
    logger.debug(f"process({names})")

    #Get functions, bbs, disasm
    funs = api.get_field("ghidra_disasm", oid, "functions")
    if not funs:
        return False
    bbs = api.get_field("ghidra_disasm", oid, "original_blocks")
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
                opcode = insn_text.split(' ')
                if opcode:
                    opcode = opcode[0]
                    # try to add destination register to opcode for more context and to avoid TNULL
                    if len(insn_text) > 3 and len(insn_text.split(' ')) > 2 and len(insn_text.split(' ')[2]) > 3:
                        target_dest = insn_text.split(' ')[2].split(",")
                        if len(target_dest[0]) == 3 and target_dest[0][-2] == 'a' and target_dest[0][-1] == 'x': #target is *ax
                            opcode += target_dest[0]
                    fun_string += opcode

        if fun_instr_count > 5 and tlsh.hash(fun_string.encode()) != "TNULL":  # Eliminate functions that are just jumping to external
            fun_info["tlsh hash"] = tlsh.hash(fun_string.encode())
        else:
            fun_info["tlsh hash"] = None

        fun_info["len"] = fun_len
        if opts['human_readable']:
            fun_dict[funs[f]['name']] = fun_info
        elif opts['output_vaddr']:
            fun_dict[funs[f]['vaddr']] = fun_info
        else:
            fun_dict[f] = fun_info

    logger.debug("Storing")
    api.store(NAME, oid,fun_dict,opts)
    return True
