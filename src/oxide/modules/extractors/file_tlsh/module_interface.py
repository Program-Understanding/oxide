DESC = ""
NAME = "file_tlsh"
USG = ""

import logging
from oxide.core import api
import tlsh
import re
logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

opts = {}

def documentation():
    return {"description": DESC, "opts_doc": opts_doc,"set": False, "atomic": True, "usage": USG}

def process(oid, opts):
    funs = api.get_field("ghidra_disasm", oid, "functions")
    if not funs:
        return False
    bbs = api.get_field("ghidra_disasm", oid, "original_blocks")
    insns = api.get_field("ghidra_disasm", oid, "instructions")
    file_string = ""

    for f in funs:
        if f == 'meta':
            continue
    
        
        blocks = funs[f]['blocks']
        for b in blocks:
            if b not in bbs: continue
            for insn_offset, insn_text in bbs[b]['members']:
                if insn_offset not in insns.keys():
                    continue
                opcode = re.split(r'[,\s]+', insn_text)
                for sub_str in opcode:
                    file_string += sub_str
    file_hash = tlsh.hash(file_string.encode())

    api.store(NAME, oid, file_hash, opts)

    return True