AUTHOR = "KEVAN"
DESC = "Extract details regarding a function that might indicate its complexity"
NAME = "function_dereferences"
USG = "Run this module over an OID to get details about dereferences occurring per function (strided accesses and general dereferences)"

import logging
from typing import Literal
from core import api
import re
logger = logging.getLogger(NAME)

opts_doc : dict[Literal["by-function-name"],dict[str,int|bool|str|type]] = {"by-function-name": {"type": bool,"mangle":True,"default":True,"Description":"Organize the results by name of function instead of by offset"}}

def documentation():
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage": USG}

def process(oid: str, opts : dict[str,bool|int|str]):
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

    #dereference pattern just captures any line that uses []
    dereference_pattern=re.compile(r"\[.*\]")
    #strid pattern captures any line that uses [] and has either a + or * or both
    stride_pattern = re.compile(r"\[.*[+*]+.*\]")
    extracts = {}
    for f in funs:
        if f == 'meta': continue
        blocks = funs[f]['blocks']
        #initialize an empty dict for those who don't have strides
        if "by-function-name" in opts and opts["by-function-name"]:
            f = funs[f]["name"]
        if not f in extracts:
            extracts[f] = {"strides": {}, "dereferences": {}}
        for b in blocks:
            if b not in bbs: continue
            for insn_offset, insn_text in bbs[b]['members']:
                if insn_offset not in insns.keys():
                    logger.error("Basic Block member not found: %s", insn_offset)
                    continue
                #check for different types of accesses per instruction
                mat = stride_pattern.search(insn_text)
                if mat:
                    extracts[f]["strides"][insn_offset] = insn_text
                mat = dereference_pattern.search(insn_text)
                if mat:
                    extracts[f]["dereferences"][insn_offset] = insn_text
    api.store(NAME, oid, extracts, opts)
    return True
