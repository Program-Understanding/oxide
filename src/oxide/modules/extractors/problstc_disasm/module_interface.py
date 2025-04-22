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

from typing import Literal


DESC = " This module computes probablistic disassembly based on module:exhaust_disasm."
NAME = "problstc_disasm"
CATEGORY = "disassembler"
USG = "This module takes a collection of binary files and analyzes them using the exhaust_disasm module. It returns "

try:
    import logging
    import time
    from typing import Dict, Any
    logger = logging.getLogger(NAME)
    logger.debug("init")
    # import speculative
    from collections import defaultdict
    from oxide.core import api
except:
    logger.warning("Failed to import oxide bro")


opts_doc = {}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True, "category": CATEGORY, "usage": USG}

# Probabilistic Disassembly
# Compute Occlusion -> checks the overlapping instructions and removes them
# Compute Successors (fall-through, conditional, and unconditional branches, calls)
# Compute Destinations -> computes the successor addresses
# Set initial probablities, offsets not in the valid set are set to data, offsets in valid set start as unknown
# For each instruction offset, gather hints that will seed dependence hypergraph (RH)
# Compute Hint Weights -> collapse each set in RH into weight factors H{offset} based on NEAR,REL,etc.
# Compute Fixed Point -> iteratively update the probabilities of each instruction via forward propagation and back propagation 
#               until convergence or max iteration

BOTTOM = -1
DEBUG = 0

CONTROL_GROUPS = {"CALL", "COND_BR", "UNCOND_BR", "RET"}
BRANCH_GROUPS = {"CALL", "COND_BR", "UNCOND_BR"}

NEAR_JUMP = 0.00001525902  # (2^32 - 1)^-1
REL_JUMP = 0.00392156862  # (2^16 - 1)^-1


def _log_fun_time(fun):
    def wrapper(*args, **kwargs):
        start = time.time()
        results = fun(*args, **kwargs)
        end = time.time()
        if DEBUG:
            logger.info(f"{fun.__name__} took {end - start} seconds to complete.")
        return results
    return wrapper

def extract_from_oid(oid: str, opts: dict) -> bool:
    """ Extracts and processes disassembly from an OID using API calls. """
    logger.debug("Processing OID: %s", oid)
    
    src = api.source(oid)
    data = api.get_field(src, oid, "data", {})
    if not data:
        logger.debug("Not able to process %s", oid)
        return False
    
    header = api.get_field("object_header", oid, oid)
    if not header:
        logger.debug("No header found for %s in %s", oid, NAME)
        return False
    
    disasm = api.retrieve("exhaust_disasm", oid)
    if not disasm or 'instructions' not in disasm:
        logger.debug("No disassembly found for %s", oid)
        return False
    disasm = disasm['instructions']
    
    try:
        result = extract(disasm)
    except ZeroDivisionError:
        logger.error("Division by zero encountered in probability calculations.")
        result = None
    
    if not result:
        return False
    
    api.store(NAME, oid, result, opts)
    return True



@_log_fun_time
def _compute_occlusion(disasm):
    """ Identify overlapping instructions and remove them from the valid set. Will need work for architecture that has
    valid overlapping instructions. """
    occlusion = defaultdict(list)
    valid_instructions = set()
    covered = set()


    # Calculate the length and occlusion of each instruction
    for offset, details in disasm.items():
        # print(offset, details)
        for i in range(offset + 1, offset + details["size"]):
            occlusion[i].append(offset)

    # Check to see if the instruction is occluded by another instruction, then skip it if so
    for offset in sorted(disasm.keys()):
        if offset in covered:
            logger.debug(f"Skipping {offset} due to occlusion")
            continue  # Skip if another instruction already claimed this byte

        valid_instructions.add(offset)
        for i in range(offset, offset + disasm[offset]["size"]):
            covered.add(i)  # Mark all bytes of this instruction as covered

    logger.debug(f"Final valid instructions after occlusion: {sorted(valid_instructions)}")
    return occlusion, valid_instructions


@_log_fun_time
def _compute_destinations(disasm):
    """ Compute successor addresses (CFG) and ensure function epilogues are correctly identified. """
    dests, preds = {}, defaultdict(list)
    function_end = {}
    last_offset = list(disasm.keys())[-1]

    for offset, details in disasm.items():
        instr = details['str']
        next_offset = offset + details['size']

        # no successors
        if instr == 'ret':
            function_end[offset] = True  # Mark function boundary
            dests[offset] = []
            continue
        # fall through to next offset, non-control
        elif not (set(details["groups"]) & CONTROL_GROUPS):
            # Default fallthrough for non-control flow instructions
            if next_offset <= last_offset:
                dests[offset] = [next_offset]
                preds[next_offset].append(offset)
            else:
                dests[offset] = []
        else: 
            # Branches/calls - parse jmp target
            try:
                #uncoditional branches
                if "UNCOND_BR" in details["groups"]:
                    dests[offset] = [int(details['op_str'], 16)]
                # conditional branches or calls
                else:
                    target = int(details['op_str'], 16)
                    dests[offset] = [next_offset, target]
                    preds[target].append(offset)
            except ValueError:
                dests[offset] = []
        # Reverse-edge map for hint propagation
        for target in dests[offset]:
            preds[target].append(offset)
        #function_end is the flag map that can be used later if one wants to build off of it (potentially look at how 
        # to use it to determine likely boundaries that might tell if something is data or code)
    return dests, preds, function_end




@_log_fun_time
def update_H():
    """ MATH determined from https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf
    Collapses all hints in RH[off] into a single weight factor H[off] by multiplying the weights of each hint type.
    """
    global H
    for offset in RH:
        prod = 1.0
        if RH[offset]:
            for hint, addr in RH[offset]:
                if 'near' in hint:
                    prod *= NEAR_JUMP
                elif 'rel' in hint:
                    prod *= REL_JUMP
                elif '3gen' in hint:
                    # Generalized would be a less likely indicator, same with eflags
                    prod *= 1 / 16
                elif '3orig' in hint:
                    prod *= 1 / 16
                elif "epilogue" in hint:
                    prod *= 0.9
                else:
                    print("not handled", hint)
            H[offset] = prod

def _compute_fixed_point(disasm, code_prob, data_prob, cfg, preds, occlusion_space):
    """ Ensure function epilogues (`pop` + `ret`) are retained while preventing infinite loops. """
    global COUNT
    COUNT = 0
    MAX_ITERATIONS = 100  # Prevent infinite looping
    function_start = {}
    function_end = {}   
    for iteration in range(1, MAX_ITERATIONS + 1):
        COUNT += 1
        fp = _forward_propagation(disasm, data_prob, cfg)
        _adjust_occlusion_probs(disasm, code_prob, data_prob, occlusion_space)
        bp = _back_propagation(disasm, code_prob, data_prob, preds)
        #stop early if no change
        if fp and bp:
            break

    logger.info(f"Fixed-point computation finished after {iteration} iterations.")
    return function_start, function_end




@_log_fun_time
def _forward_propagation(exh_disasm, data_prob, cfg):
    """ Iterative analyais to find instructions that lead to bad assembly.
        Outside of control flow, this is guarenteed to be data

        attempting to write ~line 10 algorithm 1 of https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf
    """
    fixed_point = True
    for offset, detail in exh_disasm.items():
        if data_prob[offset] == 1.0:
            # Already know instruction is data
            continue

        # update this instructions probability
        if H[offset] != BOTTOM and offset not in [x[1] for x in RH[offset]]:
            RH[offset].add(('init', offset))
            # print("product for {}".format(offset), [x[1] for x in RH[offset]])
            result = 1
            for hint, addr in RH[offset]:
                result = result * H[addr]
            data_prob[offset] = result

        # Update ongoing data reference from H's
        # Propagate instruction hints to successors
        for n in cfg[offset]:
            # for each successor from current instruction
            for hint in RH[offset]:
                if hint not in RH[n]:
                    RH[n].add(hint)
                    fixed_point = False

    return fixed_point

@_log_fun_time
def _adjust_occlusion_probs(disasm, code_prob, data_prob, occlusion_space):
    """ attempting to write ~line 22 algorithm 1 of https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf

        Struggled with which probabilities should be adjusted and whether that is a global change
        or incremental
    """


    for offset, detail in disasm.items():
        if not data_prob[offset] == BOTTOM:
            continue
        probs = [data_prob[j] for j in occlusion_space[offset] if data_prob[j] != BOTTOM]
        if probs:
            data_prob[offset] = 1 - min(probs) * 0.9


@_log_fun_time
def _back_propagation(disasm, code_prob, data_prob, preds):
    """ Iterative analysis to find instructions that lead to bad assembly.
        Outside of control flow, this is guaranteed to be data.

        Attempting to implement ~line 25 of Algorithm 1 from:
        https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf
    """
    fixed_point = True
    for i in data_prob.keys():
        if data_prob[i] == BOTTOM or i not in preds:
            # Cannot propagate unknown probability or unknown predecessors
            continue

        # if DEBUG & 32:
        #     print("BACK", i, data_prob[i], preds[i])

        for p in preds[i]:
            # if DEBUG & 32:
            #     print(f"Processing predecessor {p}: current={data_prob[p]}, propagating from {i}: {data_prob[i]}")

            # Updated probability propagation logic
            if data_prob[p] == BOTTOM or data_prob[p] < data_prob[i]:
                data_prob[p] = max(data_prob[p], data_prob[i] * 0.8)
                fixed_point = False  # Mark that we've updated a probability

                if p > i:
                    # Ensure continued processing if new updates occur
                    fixed_point = False

        if DEBUG & 32:
            print(f"Updated {i}: {data_prob[i]}, Predecessors: {preds[i]}")

    return fixed_point

@_log_fun_time
def _hint_one(offset, prev_list, disasm):
    """ Implements Control Flow Convergence hint. If multiple branches land at a given offset, tage each predecessor branch with 1rel (short jump) or 1near (long jump)
    Will tell likely hood instructions are real if they converge at a given offset"""
    branches = [prev for prev in prev_list if set(disasm[prev]["groups"]) & BRANCH_GROUPS]
    for branch in branches:
        RH[branch].add(("1rel" if disasm[branch]["size"] == 2 else "1near", offset))

@_log_fun_time
def _hint_two(offset, prev_list, disasm):
    """ Implements Control Flow Crossing hint. Captures unconditional branches that cross over other branch targets indicating unlikely. Tagged 2rel or 2 near"""
    branches = [prev for prev in prev_list if set(disasm[prev]["groups"]) & BRANCH_GROUPS]
    if branches:
        for size, label in [(2, "2rel"), (5, "2near")]:
            prev_offset = offset - size
            if prev_offset in disasm and "UNCOND_BR" in disasm[prev_offset]["groups"]:
                RH[prev_offset].add((label, offset))
                for branch in branches:
                    RH[branch].add((label, offset))

@_log_fun_time
def _hint_three(offset, prev_list, disasm):
    """ Implements Register Define-Use Relation hint. Links any predecessor that writes a register later read by the current instruction. If multiple instructions read it,
    after a value was set, likely code. """
    if offset not in disasm:
        logger.debug(f"Offset {offset} not in disasm")
        return
    for prev in prev_list:
        prev_reg_write = set(disasm[prev]['regs_write'])
        curr_reg_read = set(disasm[offset]['regs_read'])
        if prev_reg_write & curr_reg_read:
            RH[prev].add(("3orig", offset))
            RH[offset].add(("3orig", prev))


@_log_fun_time
def _hint_four(offset, prev_list, disasm):
    """
    Implements a Memory Access Pattern hint.
    Checks if the current instruction accesses a memory address
    that was recently written by any of the previous instructions.
    This helps link instructions in a probable flow.
    """

    if offset not in disasm:
        return

    # Current instruction memory reads
    curr_mem_reads = set(disasm[offset].get('mem_read', []))
    curr_mem_writes = set(disasm[offset].get('mem_write', []))

    # Loop over each predecessor instruction
    for prev in prev_list:
        if prev not in disasm:
            continue

        # Previous instruction memory writes
        prev_mem_writes = set(disasm[prev].get('mem_write', []))
        prev_mem_reads = set(disasm[prev].get('mem_read', []))

        # Check for a "write -> read" pattern:
        # The previous instruction wrote to a memory address
        # that the current instruction reads from.
        if prev_mem_writes & curr_mem_reads:
            RH[prev].add(("4memWR", offset))
            RH[offset].add(("4memWR", prev))

        # Optionally check for "read -> write" pattern:
        # If the previous instruction read from a location
        # that the current instruction writes to.
        if prev_mem_reads & curr_mem_writes:
            RH[prev].add(("4memRW", offset))
            RH[offset].add(("4memRW", prev))

@_log_fun_time
def _hint_epilogue(offset, prev_list, disasm):
    """ Adds an epilogue hint if the instruction is a function epilogue (e.g., 'pop rbp' or 'leave') followed by a 'ret'. Does not force keep, only
    provides a hint. """
    print("Hint epilogue")
    if offset not in disasm:
        return
    instr = disasm[offset]['str']
    next = offset + disasm[offset]['size']
    if instr in {'pop rbp', 'leave'} and next in disasm and disasm[next]["str"]=="ret":
        # If the instruction is a function epilogue (e.g., 'pop rbp' or 'leave') followed by a 'ret'
        # Mark the function end and link the predecessor to the return instruction
        function_end[offset] = True
        RH[offset].add(("epilogue", next))
        RH[next].add(("epilogue", offset))

def _filter_padding(instructions: Dict[int, str],
                    disasm: Dict[int, Dict[str, Any]]) -> Dict[int, str]:
                    
    """
    Remove alignment NOPs immediately following any unconditional transfer:
    - Returns (RET group or any token ending with 'ret')
    - HLT (any token ending with 'hlt')
    - Jumps (JMP or UNCOND_BR)
    Strips all NOP variants (single- and multi-byte).
    """
    filtered = dict(instructions)

    def is_terminator(off: int) -> bool:
        # 1. Check instruction groups if available (unconditional branches and returns)
        groups = disasm[off].get("groups", [])
        if "RET" in groups or "UNCOND_BR" in groups:
            return True
        # 2. Mnemonic‑based fallback: any token with 'ret' or 'hlt'
        tokens = disasm[off]["str"].split()
        if any(tok.lower().endswith("ret") for tok in tokens):
            return True
        if any(tok.lower().endswith("hlt") for tok in tokens):
            return True
        # 3. Jumps by mnemonic prefix
        if tokens and tokens[0].lower().startswith("jmp"):
            return True
        return False

    for off in sorted(instructions):
        if not is_terminator(off):
            continue
        next_off = off + disasm[off]["size"]
        while next_off in filtered:
            first_tok = disasm[next_off]["str"].split()[0].lower()
            # Remove any NOP variants (single-byte or multi-byte) :contentReference[oaicite:4]{index=4}
            if first_tok.startswith("nop"):
                pad_size = disasm[next_off]["size"]
                del filtered[next_off]
                next_off += pad_size
                continue
            break

    return filtered




def extract(disasm: Dict[int, Dict[str, Any]]) -> Dict[str, Any]:
    """ Main function to extract probabilistic disassembly from the given disassembly data. Initializes global hint graph (RH) and 
    weight map (H). Calls compute occlusion to filter overlapping bytes and compute destinations to build CFG and predecessor map (preds).
    Offsets not in valid_insts (overlapping instructions) are set to data, while valid instructions start as unknown (BOTTOM).
    Applies all hint functions to populate RH. 
    update_H collapses the hints into weights for each instruction.
    propogate the hints through the CFG and preds to update the data_prob and code_prob until convergence via compute_fixed_point.
    converts data->code probabilities and emits only offsets >= THRESHOLD. """
    global RH, H, function_start, function_end, COUNT

    function_start = {}
    function_end = {}
    RH = defaultdict(set)
    H = defaultdict(float)
    COUNT = 0

    res, data_prob, code_prob = {}, {}, {}
    occlusion_space, valid_instructions = _compute_occlusion(disasm)
    cfg, preds, function_end = _compute_destinations(disasm)

    min_offset, max_offset = min(disasm), max(disasm)
    for offset in range(min_offset, max_offset + 1):
        if offset not in valid_instructions:
            data_prob[offset], code_prob[offset] = 1.0, 0.0  # Treat as data
        else:
            data_prob[offset], code_prob[offset] = BOTTOM, BOTTOM
        H[offset], RH[offset] = BOTTOM, set()
    
    for offset, prev_list in preds.items():
        _hint_one(offset, prev_list, disasm)
        _hint_two(offset, prev_list, disasm)
        _hint_three(offset, prev_list, disasm)
        # _hint_four(offset, prev_list, disasm)
        # _hint_epilogue(offset, prev_list, disasm)

    update_H()
    _compute_fixed_point(disasm, code_prob, data_prob, cfg, preds, occlusion_space)

    for i in data_prob:
        code_prob[i] = 1 - data_prob[i] if data_prob[i] != BOTTOM else BOTTOM

    # Remove instructions with low confidence
    THRESHOLD = 0.0067
    for i in code_prob:
        if code_prob[i] >= THRESHOLD:
            res[i] = disasm[i]['str']

    logger.debug("Completed after %s passes.", COUNT)
    res = _filter_padding(res, disasm)
    return {'instructions': res}



def process(oid: str, opts: dict) -> bool:
    """ Compute probablistic disassembly from exhaustive disassembly
            https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf
    """
    logger.debug("process()")

    src = api.source(oid)
    data = api.get_field(src, oid, "data", {})
    if not data:
        logger.debug("Not able to process %s", oid)
        return False

    header = api.get_field("object_header", oid, oid)
    if not header:
        logger.debug('No header found for %s in %s', oid, NAME)
        return False

    disasm = api.retrieve("exhaust_disasm", oid)
    if not disasm or 'instructions' not in disasm:
        logger.debug("No disassembly found for %s" % disasm)
        return False
    disasm = disasm['instructions']

    try:
        result = extract(disasm)
    except ZeroDivisionError:
        # In some cases probalistic disassemly hits division by 0 in adjust code probs
        # this needs serious rethinking
        result = None
    api.flush_module("exhaust_disasm")
    if not result: return False
    api.store(NAME, oid, result, opts)
    # api.flush_module("probablstc_disam")
    return True
