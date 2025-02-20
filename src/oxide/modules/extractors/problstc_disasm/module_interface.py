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
        logger.info("No header found for %s in %s", oid, NAME)
        return False
    
    disasm = api.retrieve("exhaust_disasm", oid)
    if not disasm or 'instructions' not in disasm:
        logger.info("No disassembly found for %s", oid)
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
    """ Identify overlapping instructions and remove """
    occlusion = defaultdict(list)
    valid_instructions = set()

    for offset, details in disasm.items():
        for i in range(offset + 1, offset + details["size"]):
            occlusion[i].append(offset)

    covered = set()
    for offset in sorted(disasm.keys()):
        if offset in covered:
            logger.debug(f"Skipping {offset} due to occlusion")
            continue  # Skip if another instruction already claimed this byte

        instr = disasm[offset]['str']

        if instr.startswith('pop ') and offset + disasm[offset]['size'] in disasm:
            next_instr = disasm[offset + disasm[offset]['size']]['str']
            if next_instr == 'ret':
                valid_instructions.add(offset)
                covered.add(offset + disasm[offset]['size'])  # Mark `ret` too
                continue

        valid_instructions.add(offset)
        for i in range(offset, offset + disasm[offset]["size"]):
            covered.add(i)  # Mark all bytes of this instruction as covered

    logger.debug(f"Final valid instructions after occlusion: {sorted(valid_instructions)}")
    return occlusion, valid_instructions


@_log_fun_time
def _compute_destinations(disasm):
    """ Compute successor addresses (CFG) and ensure function epilogues are correctly identified. """
    dests, preds = {}, defaultdict(list)
    last_offset = list(disasm.keys())[-1]

    for offset, details in disasm.items():
        instr = details['str']
        next_offset = offset + details['size']

        if instr.startswith('pop '):
            if next_offset in disasm and (disasm[next_offset]['str'].startswith('pop ') or disasm[next_offset]['str'] == 'ret'):
                dests[offset] = [next_offset]
                preds[next_offset].append(offset)

        if instr == 'ret':
            function_end[offset] = True  # Mark function boundary
            dests[offset] = []
            continue

        if not set(details["groups"]) & CONTROL_GROUPS:
            # Default fallthrough for non-control flow instructions
            if next_offset <= last_offset:
                dests[offset] = [next_offset]
                preds[next_offset].append(offset)
            else:
                dests[offset] = []
            continue  

        try:
            if "UNCOND_BR" in details["groups"]:
                dests[offset] = [int(details['op_str'], 16)]
            elif "COND_BR" in details["groups"] or "CALL" in details["groups"]:
                jump_target = int(details['op_str'], 16)
                dests[offset] = [next_offset, jump_target]
                preds[jump_target].append(offset)
            else:
                dests[offset] = []
        except ValueError:
            dests[offset] = []

        for target in dests[offset]:
            preds[target].append(offset)

    return dests, preds





@_log_fun_time
def update_H():
    """ MATH determined from https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf
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
                else:
                    print("not handled", hint)
            H[offset] = prod

def _compute_fixed_point(disasm, code_prob, data_prob, cfg, preds, occlusion_space):
    """ Ensure function epilogues (`pop` + `ret`) are retained while preventing infinite loops. """
    global COUNT

    MAX_ITERATIONS = 1000  # Prevent infinite looping
    function_start = {}
    function_end = {}

    # Identify function boundaries
    for offset, details in disasm.items():
        instr = details['str']

        if instr in {'push rbp', 'mov rbp, rsp'}:
            function_start[offset] = True
        if instr in {'leave', 'ret'}:
            function_end[offset] = True

    fixed_point = False
    iteration = 0

    while not fixed_point and iteration < MAX_ITERATIONS:
        fixed_point = True
        iteration += 1  # Increment iteration count

        for offset in disasm:
            instr = disasm[offset]['str']
            next_offset = offset + disasm[offset]['size']
            if instr.startswith('pop ') and next_offset in disasm:
                next_instr = disasm[next_offset]['str']
                if next_instr.startswith('pop ') or next_instr == 'ret':
                    code_prob[offset] = max(code_prob.get(offset, 0), 1.0)  # Keep `pop`
                    code_prob[next_offset] = max(code_prob.get(next_offset, 0), 1.0)  # Keep `ret`

        # Adjust occlusion probabilities
        _adjust_occlusion_probs(disasm, code_prob, data_prob, occlusion_space)

        fixed_point = _back_propagation(disasm, code_prob, data_prob, preds) and fixed_point

    logger.info(f"Fixed-point computation finished after {iteration} iterations.")
    return function_start, function_end




@_log_fun_time
def _forward_propagation(exh_disasm, data_prob, cfg):
    """ Iterative analyais to find instructions that lead to bad assembly.
        Outside of control flow, this is guarenteed to be data

        attempting to write ~line 10 algorithm 1 of https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf
    """
    global RH
    fixed_point = True
    for offset, detail in exh_disasm.items():
        if data_prob[offset] == 1.0:
            # Already know instruction is data
            continue

        # update this instructions probability
        if H[offset] != BOTTOM and offset not in [x[1] for x in RH[offset]]:
            RH[offset].add(('init', offset))
            print("product for {}".format(offset), [x[1] for x in RH[offset]])
            result = 1
            for hint, addr in RH[offset]:
                result = result * H[addr]
            data_prob[offset] = result

        # Update ongoing data reference from H's
        # Propagate instruction hints to successors
        for n in cfg[offset]:
            # for each successor from current instruction
            for hint in RH[offset]:
                if n in RH and hint not in RH[n]:
                    if DEBUG & 8:
                        logger.info("adding %s to hints for %s", hint, n)
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
            # Only update if data probability is unknown
            continue

        # Find probability of being data for each overlapping instruction
        occluded_probs = []
        for j in occlusion_space[offset]:
            if data_prob[j] == BOTTOM:
                continue
            occluded_probs.append(data_prob[j])

        if not occluded_probs:
            # If not overlapping instructions, leave probability as is
            continue

        # Set probability to inverse of most likely overlapping instruction
        # In lines 22-24, the algorithm traverses all the addressesand performs local propagation of
        #  probabilities within occlusion space of individual instructions. Particularly, for each address_i,
        #  it finds its occluded peer_j that has the minimal probability (i.e., the most likely instruction).
        #  The likelihoodofibeing data is hence computed as 1−D[j](line 24).
        data_prob[offset] = 1 - min(occluded_probs)*0.9
        print("adjusting {} to {}".format(offset, data_prob[offset]))

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

        if DEBUG & 32:
            print("BACK", i, data_prob[i], preds[i])

        for p in preds[i]:
            if DEBUG & 32:
                print(f"Processing predecessor {p}: current={data_prob[p]}, propagating from {i}: {data_prob[i]}")

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
    """ Implements Control Flow Convergence hint. """
    branches = [prev for prev in prev_list if set(disasm[prev]["groups"]) & BRANCH_GROUPS]
    for branch in branches:
        RH[branch].add(("1rel" if disasm[branch]["size"] == 2 else "1near", offset))

@_log_fun_time
def _hint_two(offset, prev_list, disasm):
    """ Implements Control Flow Crossing hint. """
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
    """ Implements Register Define-Use Relation hint. """
    if offset not in disasm:
        return
    for prev in prev_list:
        prev_reg_write = set(disasm[prev]['regs_write'])
        curr_reg_read = set(disasm[offset]['regs_read'])
        if prev_reg_write & curr_reg_read:
            RH[prev].add(("3orig", offset))
            RH[offset].add(("3orig", prev))

def extract(disasm: Dict[int, Dict[str, Any]]) -> Dict[str, Any]:
    global RH, H, function_start, function_end, COUNT

    function_start = {}
    function_end = {}
    RH = defaultdict(set)
    H = defaultdict(float)
    COUNT = 0

    res, data_prob, code_prob = {}, {}, {}
    occlusion_space, valid_instructions = _compute_occlusion(disasm)
    cfg, preds = _compute_destinations(disasm)

    min_offset, max_offset = min(disasm), max(disasm)
    for offset in range(min_offset, max_offset + 1):
        if offset == 2763:
            pass
        if offset not in valid_instructions:
            data_prob[offset], code_prob[offset] = 1.0, 0.0  # Treat as data
        else:
            data_prob[offset], code_prob[offset] = BOTTOM, BOTTOM
        H[offset], RH[offset] = BOTTOM, set()
    
    for offset, prev_list in preds.items():
        if offset == 2763:
            pass
        _hint_one(offset, prev_list, disasm)
        _hint_two(offset, prev_list, disasm)
        _hint_three(offset, prev_list, disasm)

    update_H()
    _compute_fixed_point(disasm, code_prob, data_prob, cfg, preds, occlusion_space)

    for i in data_prob:
        code_prob[i] = 1 - data_prob[i] if data_prob[i] != BOTTOM else BOTTOM

    # Remove instructions with low confidence
    THRESHOLD = 0.0067
    for i in code_prob:
        if code_prob[i] >= THRESHOLD:
            res[i] = disasm[i]['str']

    logger.info("Completed after %s passes.", COUNT)
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
        logger.info('No header found for %s in %s', oid, NAME)
        return False

    disasm = api.retrieve("exhaust_disasm", oid)
    if not disasm or 'instructions' not in disasm:
        logger.info("No disassembly found for %s" % disasm)
        return False
    disasm = disasm['instructions']

    try:
        result = extract(disasm)
    except ZeroDivisionError:
        # In some cases probalistic disassemly hits division by 0 in adjust code probs
        # this needs serious rethinking
        result = None
    if not result: return False
    api.store(NAME, oid, result, opts)
    return True
