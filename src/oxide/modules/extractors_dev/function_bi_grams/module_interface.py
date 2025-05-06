AUTHOR="Kevan"
DESC = "Check function by function for a bigram of 2 opcodes in sequence by class"
NAME = "function_bi_grams"
USG = "How many unique times a function has a type of bi-gram"
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

class Disassembly(TypedDict):
    instructions: dict[int, DisassemblyInsns]

def documentation() -> dict[str, object]:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "Usage": USG}

def process(oid: str, opts: dict[Literal["by-function-name"],bool]) -> bool:
    functions : dict[int,GhidraDisasmFunctions] | None = api.get_field("ghidra_disasm", oid, "functions")
    if not functions:
        logger.error("Failed to extract disassembly")
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
    results : dict[str | int,dict[Literal["cmp-jump"] | Literal["cmp-jump-stride3"] | Literal["cmp-jump-stride4"] | Literal["returns"],int | bool]] = {}
    for f in functions:
        if f not in original_blocks:
            #logger.info(f"{f} not in {list(original_blocks.keys())}")
            continue
        f_name : str | int
        if "by-function-name" in opts and opts["by-function-name"]:
            f_name = functions[f]["name"]
        else:
            f_name = f
        results[f_name] = {"cmp-jump": 0, "cmp-jump-stride3": 0, "cmp-jump-stride4":0, "returns": False}
        #loop through each block of the function
        for bb in functions[f]["blocks"]:
            #loop through each instruction of the function
            fun_insns : list[int] = [i for i,_ in original_blocks[bb]["members"]]
            for i in range(0,len(fun_insns),2):
                if i+1 >= len(fun_insns): break
                ins1 = disasm[fun_insns[i]] if fun_insns[i] in disasm else None
                ins2 = disasm[fun_insns[i+1]] if fun_insns[i+1] in disasm else None
                if ins1 is None or ins2 is None: continue
                #finally we can check if we have the interesting stuff going on
                if ins1["mnemonic"] == "cmp":
                    if "jump" in ins2["groups"]:
                        #if not "cmp-jump" in results[f_name]: results[f_name]["cmp-jump"] = 0
                        results[f_name]["cmp-jump"] += 1
                if ins1["mnemonic"] == "ret":
                    results[f_name]["returns"] = True
                if "call" in ins2["mnemonic"]:
                    try:
                        target = int(ins2["op_str"],16)
                        if "exit" in functions[target]["name"]:
                            #logger.info(f"call found for instruction {ins2}")
                            results[f_name]["returns"] = True
                    except:
                        pass
            for i in range(0,len(fun_insns),3):
                if i+2 >= len(fun_insns): break
                ins1 = disasm[fun_insns[i]] if fun_insns[i] in disasm else None
                ins2 = disasm[fun_insns[i+1]] if fun_insns[i+1] in disasm else None
                ins3 = disasm[fun_insns[i+2]] if fun_insns[i+2] in disasm else None
                if ins1 is None or ins2 is None or ins3 is None: continue
                #finally we can check if we have the interesting stuff going on
                if ins1["mnemonic"] == "cmp":
                    if "jump" in ins3["groups"]:
                        #if not "cmp-jump-stride3" in results[f_name]: results[f_name]["cmp-jump-stride3"] = 0
                        results[f_name]["cmp-jump-stride3"] += 1
            for i in range(0,len(fun_insns),4):
                if i+3 >= len(fun_insns): break
                ins1 = disasm[fun_insns[i]] if fun_insns[i] in disasm else None
                ins2 = disasm[fun_insns[i+1]] if fun_insns[i+1] in disasm else None
                ins3 = disasm[fun_insns[i+2]] if fun_insns[i+2] in disasm else None
                ins4 = disasm[fun_insns[i+3]] if fun_insns[i+3] in disasm else None
                if ins1 is None or ins2 is None or ins3 is None or ins4 is None: continue
                #finally we can check if we have the interesting stuff going on
                if ins1["mnemonic"] == "cmp":
                    if "jump" in ins4["groups"]:
                        #if not "cmp-jump-stride4" in results[f_name]: results[f_name]["cmp-jump-stride4"] = 0
                        results[f_name]["cmp-jump-stride4"] += 1
    return api.store(NAME,oid,results,opts)
