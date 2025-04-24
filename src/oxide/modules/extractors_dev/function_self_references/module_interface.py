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

DisassemblyInsns = TypedDict(
    "DisassemblyInsns",
    {
        "id": int,
        "mnemonic": str,
        "address": int,
        "op_str" : str,
        "size" : int,
        "str" : str,
        "groups" : list[Literal["jump"] | Literal["branch_relative"] | str],
        "regs_read" : list[str],
        "regs_write" : list[str],
        "regs_access" : tuple[list[str],list[str]],
        "prefix" : list[int],
        "opcode" : list[int],
        "rex" : int,
        "operand_size" : int,
        "modrm" : int,
        "eflags": list[str],
        "operands" : dict[str,dict[Literal["type.mem"],dict[str,str|int] | dict[Literal["size"],int] | dict[Literal["access"],str]] | dict[Literal["displacement"],int] | dict[Literal["type.imm"],int] | dict[Literal["type.reg"],str]]
    }
)

def documentation() -> dict[str, object]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "Usage": USG}

def process(oid: str, opts: dict[Literal["by-function-name"],bool]) -> bool:
    functions : dict[int,GhidraDisasmFunctions] | None = api.get_field("ghidra_disasm", oid, "functions")
    if not functions:
        logger.error("Failed to extract function information")
        return False
    original_blocks : dict[int,GhidraDisasmBlocks] | None = api.get_field("ghidra_disasm", oid, "original_blocks")
    if not original_blocks:
        logger.error("Couldn't get original blocks")
        return False
    ddisasm : dict[str,dict[int,DisassemblyInsns]] | None = api.get_field("disassembly",oid,oid)
    if ddisasm is None:
        logger.error("Couldn't get disasm from disassembly module")
        return False
    else:
        disasm : dict[int, DisassemblyInsns] = ddisasm["instructions"]
    
    results : dict[str | int,dict[Literal["earlier block"]|Literal["later block"]|Literal["same block"], int]] = {}
    for f in functions:
        if f not in original_blocks:
            #logger.info(f"{f} not in {list(original_blocks.keys())}")
            continue
        f_name : str | int
        if "by-function-name" in opts and opts["by-function-name"]:
            f_name = functions[f]["name"]
        else:
            f_name = f
        results[f_name] = {"earlier block": 0,"later block": 0,"same block":0}
        #loop through each destination of the function
        for b in functions[f]["blocks"]:
            #get all instructions from the function
            fun_insns : list[int] = [i for i,_ in original_blocks[b]["members"]]
            for i in fun_insns:
                if i not in disasm: continue
                insn = disasm[i]
                if "jump" in insn["groups"] or "call" in insn["groups"] or "branch_relative" in insn["groups"]:
                    d : int
                    operands = list(insn["operands"].keys())
                    for key in operands:
                        if  "type.imm" in insn["operands"][key]:
                            d = insn["operands"][key]["type.imm"]
                            break
                    if not "d" in locals(): continue
                    #check if the destination is one of the function's blocks
                    addr : int = insn["address"]
                    if d in functions[f]["blocks"]:
                        timing : Literal["earlier block"]|Literal["later block"]|Literal["same block"]
                        if d == b:
                            timing = "same block"
                        elif d < addr:
                            timing = "earlier block"
                        elif d > addr :
                            timing = "later block"
                        else:
                            timing = "same block"
                        results[f_name][timing]+=1
    api.store(NAME,oid,results,opts)
    return True
