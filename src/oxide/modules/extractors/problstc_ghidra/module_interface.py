import logging
import time
import re
from typing import Dict, Any, TypedDict
from oxide.core import api

NAME = "problstc_ghidra"
DESC = ("This module runs ghidra_disasm to extract a baseline disassembly, then feeds these "
        "‘truths’ into exhaust_disasm to generate all plausible alternatives, and finally "
        "applies problstc_disasm to whittle down the options based on probability hints.")
CATEGORY = "disassembler"
USG = ("This module performs a combined disassembly pipeline using ghidra_disasm, exhaust_disasm, "
       "and problstc_disasm. It ensures that the ghidra results remain unchanged in the exhaustive stage "
       "and then uses probability-based filtering to select the best options.")

opts_doc = {}

def documentation() -> Dict[str, Any]:
    """
    Returns module documentation.
    """
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
        "category": CATEGORY,
        "usage": USG
    }



class Disassembly(TypedDict):
    id: int
    mnemonic: str
    address: int
    op_str: str
    size: int
    str: str
    groups: list
    regs_read: list
    regs_write: list
    regs_access: tuple
    prefix: list
    opcode: list
    rex: int
    operand_size: int
    modrm: int
    operands: dict

class GhidraDisasmInstructions(TypedDict):
    blocks : list[tuple[int,str]]
    name: str
    vaddr: str
    params : list[tuple[int,str]]
    retType: str
    signature: str
    returning: str

class ExhaustDisasmInstructions(TypedDict):
    id: int
    mnemonic: str
    address: int
    op_str: str
    size: int
    str: str
    groups: list
    regs_read: list
    regs_write: list
    regs_access: tuple[list, list[str]]
    prefix: list[int]
    opcode: list[int]
    rex: int
    operand_size: int
    modrm: int
    eflags: list[str]
    operands: dict[str, dict[str, Any]]

def process(oid: str, opts: dict) -> bool:
    logger = logging.getLogger(NAME)
    logger.info("Starting combined disassembly for oid: %s", oid)

    ghidra_result = api.retrieve("ghidra_disasm", oid)
    if not ghidra_result or "instructions" not in ghidra_result:
        logger.error("ghidra_disasm returned no instructions for oid: %s", oid)
        return False
    ghidra_instructions : dict[int,str] = ghidra_result.get("instructions", {})
    logger.info("Ghidra disassembly retrieved for oid: %s", oid)

    exhaust_result = api.retrieve("exhaust_disasm", oid)
    if not exhaust_result or "instructions" not in exhaust_result:
        logger.error("exhaust_disasm returned no instructions for oid: %s", oid)
        return False
    exhaust_instructions : ExhaustDisasmInstructions = exhaust_result.get("instructions", {})
    logger.info("Exhaustive disassembly retrieved for oid: %s", oid)


    #Filtering: For each offset present in ghidra, compare its opcode to candidates.
    offsets_to_remove = []
    for offset in ghidra_instructions:
        if offset in exhaust_instructions:
            instruction_dict  = exhaust_instructions[offset]
            # logger.debug("Instruction dict: %s", instruction_dict)
            if instruction_dict["mnemonic"] in ghidra_instructions[offset].lower():
                #valid candidate, so we keep track of all the offsets that the valid candidate covers by its size so we can remove it later
                offsets_to_remove.extend(range(offset+1,offset+instruction_dict["size"]-1))

    #remove the invalid candidates
    print("Removing Stuff")
    logger.info("Removing Stuff")
    for offset in offsets_to_remove:
        del exhaust_instructions[offset]
        print("Removed invalid candidate at offset: %s", offset)
        logger.info("Removed invalid candidate at offset: %s", offset)



    api.store("exhaust_disasm", oid, exhaust_result, opts)
    # logger.debug("Filtered and reformatted exhaustive instructions: %s", exhaust_instructions)


    final_result = api.retrieve("problstc_disasm", oid)

    final_instructions = final_result.get("instructions", {})
    result = {'instructions': {int(offset): insn for offset, insn in final_instructions.items()}}
    api.store(NAME, oid, result, opts)
    logger.debug("Combined disassembly completed successfully for oid: %s", oid)
    return True

#Ghidra disasm
#Exhaustive disasm



#Problstc disasm






















# def normalize_instruction(instruction: Any) -> str:
#     """
#     Normalize an instruction by converting it to string, stripping whitespace,
#     converting to lowercase, removing extraneous punctuation, and extracting
#     the first alphanumeric token.
#     """
#     instruction = str(instruction)
#     instr = instruction.strip().lower()
#     instr = re.sub(r'[,\;]', '', instr)
#     match = re.match(r'([\w]+)', instr)
#     return match.group(1) if match else ""

# def transform_candidate(candidate: Dict[str, Any], offset: int) -> Dict[str, Any]:
#     """
#     Transform a candidate option into the expected format for probabilistic disassembly.
#     Uses candidate values if available; otherwise, falls back to generic defaults.
#     Expected keys:
#       - id, mnemonic, address, op_str, size, str, groups, regs_read, regs_write,
#         regs_access, prefix, opcode, rex, operand_size, modrm, operands.
#     """
#     return {
#         "id": candidate.get("id", 0),
#         "mnemonic": candidate.get("mnemonic", normalize_instruction(candidate.get("str", ""))),
#         "address": offset,
#         "op_str": candidate.get("op_str", ""),
#         "size": candidate.get("size", 4),
#         "str": candidate.get("str", ""),
#         "groups": candidate.get("groups", []),
#         "regs_read": candidate.get("regs_read", []),
#         "regs_write": candidate.get("regs_write", []),
#         "regs_access": candidate.get("regs_access", ([], [])),
#         "prefix": candidate.get("prefix", [0, 0, 0, 0]),
#         "opcode": candidate.get("opcode", [0, 0, 0, 0]),
#         "rex": candidate.get("rex", 0),
#         "operand_size": candidate.get("operand_size", 8),
#         "modrm": candidate.get("modrm", 0),
#         "operands": candidate.get("operands", {}),
#     }

# def process(oid: str, opts: dict) -> bool:
#     logger = logging.getLogger(NAME)
#     logger.info("Starting combined disassembly for oid: %s", oid)

#     # --- Step 1: Run ghidra_disasm via the Oxide API ---
#     logger.info("Running ghidra_disasm")
#     if not api.process("ghidra_disasm", oid, opts):
#         logger.error("ghidra_disasm failed for oid: %s", oid)
#         return False
#     ghidra_result = api.retrieve("ghidra_disasm", oid)
#     if not ghidra_result or "instructions" not in ghidra_result:
#         logger.error("ghidra_disasm returned no instructions for oid: %s", oid)
#         return False
#     ghidra_instructions = ghidra_result.get("instructions", {})

#     # --- Step 2: Run exhaust_disasm via the Oxide API ---
#     logger.info("Running exhaust_disasm")
#     if not api.retrieve("exhaust_disasm", oid, opts):
#         logger.error("exhaust_disasm failed for oid: %s", oid)
#         return False
#     exhaust_result = api.retrieve("exhaust_disasm", oid)
#     if not exhaust_result or "instructions" not in exhaust_result:
#         logger.error("exhaust_disasm returned no instructions for oid: %s", oid)
#         return False
#     exhaust_instructions = exhaust_result.get("instructions", {})

#     # --- Filtering: For each offset present in ghidra, compare its opcode to candidates.
#     offsets_to_remove = []
#     for offset, ghidra_insn in ghidra_instructions.items():
#         if offset not in exhaust_instructions:
#             continue
#         ghidra_opcode = normalize_instruction(ghidra_insn)
#         # If ghidra opcode is purely numeric, remove this offset.
#         if ghidra_opcode.strip().isdigit():
#             logger.debug("Removing offset %s because ghidra opcode '%s' is numer



# def normalize_instruction(instruction: Any) -> str:
#     """
#     Normalize an instruction by converting it to string, stripping whitespace,
#     converting to lowercase, removing extraneous punctuation, and extracting
#     the first alphanumeric token.
#     """
#     instruction = str(instruction)
#     instr = instruction.strip().lower()
#     instr = re.sub(r'[,\;]', '', instr)
#     match = re.match(r'([\w]+)', instr)
#     return match.group(1) if match else ""

# def transform_candidate(candidate: Dict[str, Any], offset: int) -> Dict[str, Any]:
#     """
#     Transform a candidate option into the expected format for probabilistic disassembly.
#     Uses candidate values if available; otherwise, falls back to generic defaults.
#     Expected keys:
#       - id, mnemonic, address, op_str, size, str, groups, regs_read, regs_write,
#         regs_access, prefix, opcode, rex, operand_size, modrm, operands.
#     """
#     return {
#         "id": candidate.get("id", 0),
#         "mnemonic": candidate.get("mnemonic", normalize_instruction(candidate.get("str", ""))),
#         "address": offset,
#         "op_str": candidate.get("op_str", ""),
#         "size": candidate.get("size", 4),
#         "str": candidate.get("str", ""),
#         "groups": candidate.get("groups", []),
#         "regs_read": candidate.get("regs_read", []),
#         "regs_write": candidate.get("regs_write", []),
#         "regs_access": candidate.get("regs_access", ([], [])),
#         "prefix": candidate.get("prefix", [0, 0, 0, 0]),
#         "opcode": candidate.get("opcode", [0, 0, 0, 0]),
#         "rex": candidate.get("rex", 0),
#         "operand_size": candidate.get("operand_size", 8),
#         "modrm": candidate.get("modrm", 0),
#         "operands": candidate.get("operands", {}),
#     }

# def process(oid: str, opts: dict) -> bool:
#     logger = logging.getLogger(NAME)
#     logger.info("Starting combined disassembly for oid: %s", oid)

#     # --- Step 1: Run ghidra_disasm via the Oxide API ---
#     logger.info("Running ghidra_disasm")
#     if not api.process("ghidra_disasm", oid, opts):
#         logger.error("ghidra_disasm failed for oid: %s", oid)
#         return False
#     ghidra_result = api.retrieve("ghidra_disasm", oid)
#     if not ghidra_result or "instructions" not in ghidra_result:
#         logger.error("ghidra_disasm returned no instructions for oid: %s", oid)
#         return False
#     ghidra_instructions = ghidra_result.get("instructions", {})

#     # --- Step 2: Run exhaust_disasm via the Oxide API ---
#     logger.info("Running exhaust_disasm")
#     if not api.retrieve("exhaust_disasm", oid, opts):
#         logger.error("exhaust_disasm failed for oid: %s", oid)
#         return False
#     exhaust_result = api.retrieve("exhaust_disasm", oid)
#     if not exhaust_result or "instructions" not in exhaust_result:
#         logger.error("exhaust_disasm returned no instructions for oid: %s", oid)
#         return False
#     exhaust_instructions = exhaust_result.get("instructions", {})

#     # --- Filtering: For each offset present in ghidra, compare its opcode to candidates.
#     offsets_to_remove = []
#     for offset, ghidra_insn in ghidra_instructions.items():
#         if offset not in exhaust_instructions:
#             continue
#         ghidra_opcode = normalize_instruction(ghidra_insn)
#         # If ghidra opcode is purely numeric, remove this offset.
#         if ghidra_opcode.strip().isdigit():
#             logger.debug("Removing offset %s because ghidra opcode '%s' is numeric", offset, ghidra_opcode)
#             offsets_to_remove.append(offset)
#             continue

#         candidates = exhaust_instructions[offset]
#         valid_candidates = {}
#         for key, candidate in candidates.items():
#             # For dictionary candidates, use the "str" field.
#             candidate_str = candidate.get("str", "") if isinstance(candidate, dict) else str(candidate)
#             # Skip candidate if it's purely numeric.
#             if candidate_str.strip().isdigit():
#                 logger.debug("Removing candidate '%s' at offset %s because it is numeric", key, offset)
#                 continue
#             if normalize_instruction(candidate_str) == ghidra_opcode:
#                 valid_candidates[key] = candidate
#             else:
#                 logger.debug("Removing candidate '%s' at offset %s because '%s' does not match ghidra opcode '%s'",
#                              key, offset, normalize_instruction(candidate_str), ghidra_opcode)
#         if valid_candidates:
#             exhaust_instructions[offset] = valid_candidates
#         else:
#             logger.error("No valid disassembly options remain at offset: %s", offset)
#             offsets_to_remove.append(offset)
#     # Remove offsets that failed filtering.
#     for offset in offsets_to_remove:
#         if offset in exhaust_instructions:
#             del exhaust_instructions[offset]

#     # --- Flattening: For each offset, select one candidate and transform it.
#     flattened = {}
#     for offset, candidates in exhaust_instructions.items():
#         if isinstance(candidates, dict) and candidates:
#             default_key = next(iter(candidates))
#             candidate = candidates[default_key]
#             if not isinstance(candidate, dict):
#                 candidate = {"str": str(candidate)}
#             flattened[offset] = transform_candidate(candidate, offset)
#     exhaust_instructions = flattened

#     # Store the filtered and reformatted exhaustive disassembly.
#     exhaust_result["instructions"] = exhaust_instructions
#     api.store("exhaust_disasm", oid, exhaust_result, opts)
#     logger.debug("Filtered and reformatted exhaustive instructions: %s", exhaust_instructions)

#     # --- Step 3: Run problstc_disasm via the Oxide API ---
#     logger.info("Running problstc_disasm")
#     if not api.process("problstc_disasm", oid, opts):
#         logger.error("problstc_disasm failed for oid: %s", oid)
#         return False
#     final_result = api.retrieve("problstc_disasm", oid)
#     if not final_result or "instructions" not in final_result:
#         logger.error("problstc_disasm did not produce a result for oid: %s", oid)
#         return False

#     # Retrieve final instructions and reformat them using integer offsets.
#     final_instructions = final_result.get("instructions", {})
#     result = {'instructions': {int(offset): insn for offset, insn in final_instructions.items()}}
#     api.store(NAME, oid, result, opts)
#     logger.debug("Combined disassembly completed successfully for oid: %s", oid)
#     return True
# ic", offset, ghidra_opcode)
# #             offsets_to_remove.append(offset)
# #             continue

# #         candidates = exhaust_instructions[offset]
# #         valid_candidates = {}
# #         for key, candidate in candidates.items():
# #             # For dictionary candidates, use the "str" field.
# #             candidate_str = candidate.get("str", "") if isinstance(candidate, dict) else str(candidate)
# #             # Skip candidate if it's purely numeric.
# #             if candidate_str.strip().isdigit():
# #                 logger.debug("Removing candidate '%s' at offset %s because it is numeric", key, offset)
# #                 continue
# #             if normalize_instruction(candidate_str) == ghidra_opcode:
# #                 valid_candidates[key] = candidate
# #             else:
# #                 logger.debug("Removing candidate '%s' at offset %s because '%s' does not match ghidra opcode '%s'",
# #                              key, offset, normalize_instruction(candidate_str), ghidra_opcode)
# #         if valid_candidates:
# #             exhaust_instructions[offset] = valid_candidates
# #         else:
# #             logger.error("No valid disassembly options remain at offset: %s", offset)
# #             offsets_to_remove.append(offset)
# #     # Remove offsets that failed filtering.
# #     for offset in offsets_to_remove:
# #         if offset in exhaust_instructions:
# #             del exhaust_instructions[offset]

# #     # --- Flattening: For each offset, select one candidate and transform it.
# #     flattened = {}
# #     for offset, candidates in exhaust_instructions.items():
# #         if isinstance(candidates, dict) and candidates:
# #             default_key = next(iter(candidates))
# #             candidate = candidates[default_key]
# #             if not isinstance(candidate, dict):
# #                 candidate = {"str": str(candidate)}
# #             flattened[offset] = transform_candidate(candidate, offset)
# #     exhaust_instructions = flattened

# #     # Store the filtered and reformatted exhaustive disassembly.
# #     exhaust_result["instructions"] = exhaust_instructions
# #     api.store("exhaust_disasm", oid, exhaust_result, opts)
# #     logger.debug("Filtered and reformatted exhaustive instructions: %s", exhaust_instructions)

# #     # --- Step 3: Run problstc_disasm via the Oxide API ---
# #     logger.info("Running problstc_disasm")
# #     if not api.process("problstc_disasm", oid, opts):
# #         logger.error("problstc_disasm failed for oid: %s", oid)
# #         return False
# #     final_result = api.retrieve("problstc_disasm", oid)
# #     if not final_result or "instructions" not in final_result:
# #         logger.error("problstc_disasm did not produce a result for oid: %s", oid)
# #         return False

# #     # Retrieve final instructions and reformat them using integer offsets.
# #     final_instructions = final_result.get("instructions", {})
# #     result = {'instructions': {int(offset): insn for offset, insn in final_instructions.items()}}
# #     api.store(NAME, oid, result, opts)
# #     logger.debug("Combined disassembly completed successfully for oid: %s", oid)
# #     return True
