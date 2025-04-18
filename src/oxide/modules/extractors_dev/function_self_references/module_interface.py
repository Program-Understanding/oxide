AUTHOR="Kevan"
DESC = "Check function by function if any function refers to itself through jumps or calls"
NAME = "function_self_references"
USG = "How many unique times a function's blocks refers to some of the functions blocks"
import logging
from typing import TypedDict, Literal
from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc : dict[Literal["by-function-name"],dict[str,int|bool|str|type]] = {"by-function-name": {"type": bool,"mangle":True,"default":True,"Description":"Organize the results by name of function instead of by offset"}}

#ghidra_disasm related hints
class OutputMeta(TypedDict):
    time: float
    load_addr: int
class GhidraDisasmBlocks(TypedDict):
    members: list[tuple[int,str]]
    dests: list[int]
class GhidraDisasmFunctions(TypedDict):
    blocks : list[int]
    name: str
    vaddr: str
    params: list[tuple[int,str]]
    retType: str
    signature: str
    returning: str
class GhidraDisasm(TypedDict):
    meta: OutputMeta
    instructions: dict[int,str]
    original_blocks: dict[int, GhidraDisasmBlocks]
    canon_blocks: None
    functions: dict[int,GhidraDisasmFunctions]

def documentation() -> dict[str, object]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "Usage": USG}

def process(oid: str, opts: dict[Literal["by-function-name"],bool]) -> bool:
    disasm_output : dict[int,GhidraDisasmFunctions] | None = api.get_field("ghidra_disasm", oid, "functions")
    if not disasm_output:
        logger.error("Failed to extract disassembly")
        return False
    original_blocks : dict[int,GhidraDisasmBlocks] | None = api.get_field("ghidra_disasm", oid, "original_blocks")
    if not original_blocks:
        logger.error("Couldn't get original blocks")
        return False
    results : dict[str | int,int] = {}
    for f in disasm_output:
        if f not in original_blocks:
            #logger.info(f"{f} not in {list(original_blocks.keys())}")
            continue
        f_name : str | int
        if "by-function-name" in opts and opts["by-function-name"]:
            f_name = disasm_output[f]["name"]
        else:
            f_name = f
        results[f_name] = 0
        #loop through each destination of the function
        for d in original_blocks[f]["dests"]:
            #check if the destination is one of the function's blocks
            if d in disasm_output[f]["blocks"]:
                results[f_name]+=1
    api.store(NAME,oid,results,opts)
    return True
