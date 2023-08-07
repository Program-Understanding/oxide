DESC = " Extract functions from a disassembly (uses ghidra_disasm)"
NAME = "function_extract"
USG = " This module takes a collection of binary files and extracts information about its functions, basic blocks and instructions from the \
binary using ghidra_disasm. It returns a dictionary with the function name as a key and infomation about the function as its key-value pair"

import logging
import hashlib
import api
logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

def documentation():
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage": USG}

def process(oid, opts):
    f_dict = {}
    names = api.get_field("file_meta", oid, "names")
    logger.debug("process(%s)", names)

    # Get functions, basic blocks, and disassembly
    funs = api.get_field("ghidra_disasm", oid, "functions")
    if not funs: return False
    bbs = api.get_field("ghidra_disasm", oid, "original_blocks")
    insns = api.get_field("disassembly", oid, oid)
    if insns and "instructions" in insns:
        insns = insns["instructions"]
    else:
        return False

    range = sorted(insns.keys())
    logger.info("Instruction range: %d - %d", range[0], range[-1])

    extracts = {}
    for f in funs:
        if f == 'meta': continue
        fname = funs[f]['name']
        extracts[fname] = funs[f]
        blocks = funs[f]['blocks']
        extracts[fname]['instructions'] = {}
        for b in blocks:
            if b not in bbs: continue
            for insn_offset, insn_text in bbs[b]['members']:
                if insn_offset not in insns.keys():
                    logger.error("Basic Block member not found: %s", insn_offset)
                    continue
                extracts[fname]['instructions'][insn_offset] = insn_text
        range = sorted(extracts[fname]['instructions'].keys())
        if range:
            extracts[fname]["start"] = range[0]
        else:
            extracts[fname]["start"] = None

    logger.debug("Storing")
    api.store(NAME, oid, extracts, opts)
    return True
