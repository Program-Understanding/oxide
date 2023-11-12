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

import logging
import time
from collections import defaultdict

from termcolor import colored
import colorama
colorama.init()
import pprint

import api

NAME = "speculative"
logger = logging.getLogger(NAME)

"""
    This module is an extremely rough implementation of https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf
        The starting point is Algorithm 1 of paper, where extract function is the top level of algorithm
    Superset Disassembly
        exhaustive minus invalid and sequences that lead to invalid
        not interesting to analysis

    Assumptions
        Instructions come from compiler that does not produce overlapping bodies

    Relevant papers to understand state of the art and approaches
        Speculative
            Khadra, M. Ammar Ben, Dominik Stoffel, and Wolfgang Kunz. "Speculative disassembly of binary code." 2016 International Conference on Compliers, Architectures, and Sythesis of Embedded Systems (CASES). IEEE, 2016.
                *Arm only*

        Superset

        Probablistic
            Miller, Kenneth, et al. "Probabilistic disassembly." 2019 IEEE/ACM 41st International Conference on Software Engineering (ICSE). IEEE, 2019.
"""

BOTTOM = -1
COUNT = 0
# debug:
#   1: invalid
#   2: hint_two
#   4: hint_three
#   8: fwd_prop
#  16: adjust_code_prob
#  32: back_prop
DEBUG = 0

# These strings are used to identify disassembly instructions that represent control flow relevant to algorithm
# Default XED disassembly groups denoting control flow
CONTROL_GROUPS = set(["CALL", "COND_BR", "UNCOND_BR", "RET"])
# capstone set(["call", "branch_relative", "jump", "ret"])
BRANCH_GROUPS = set(["CALL", "COND_BR", "UNCOND_BR"])
# capstone set(["branch_relative", "call", "jump"])

RH = defaultdict(set)
H = defaultdict(float)

# Probabilities (constants converted to floats from fraction from "probability analsyis section of
#   https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf for hint 1")
NEAR_JUMP = 0.00001525902  # (2^32 - 1)^-1
# 1near, 2near
REL_JUMP = 0.00392156862  # # (2^16 - 1)^-1
# 1rel, 2rel

# ---- Utilities


def _create_or_insert(elem, key, dictionary):
    """ Custom implementation of default dict, mainly to avoid DefaultDict in printing
    """
    if key not in dictionary:
        dictionary[key] = [elem]
    else:
        dictionary[key].append(elem)


def _log_fun_time(fun):
    """ Logging utility wrapper to record time spend on individual functions
    """
    def wrapper(*args, **kwargs):
        start = time.time()
        results = fun(*args, **kwargs)
        end = time.time()
        if DEBUG:
            logger.info(f"{fun.__name__} took {end-start} seconds to complete.")
        return results
    return wrapper


# ---- Hint functions


@_log_fun_time
def _hint_one(offset, prev_list, disasm):
    """ Run once - Control Flow Convergence
            each conditional branch has range of destinations, odds of multiple pointing to same byte unlikely
            * relative, near, far jumps for addr size
            * 1/255, 1/2^16 - 1, 1/2^32 -1 respectively

        best attempt at implementing Hint I: Control Flow Convergence of https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf
    """
    global RH
    branches = []
    for prev in prev_list:
        if len(list(set(disasm[prev]["groups"]) & BRANCH_GROUPS)) > 0:
            branches += [prev]

    # Assign probabilities, we only need to assign destination at branch, child will get
    # probability through forward propagation
    for branch in branches:
        if disasm[branch]["size"] == 2:
            RH[branch].add(("1rel", offset))
        else:
            RH[branch].add(("1near", offset))


@_log_fun_time
def _hint_two(offset, prev_list, disasm):
    """ Control Flow Crossing
            Control destination following unconditional jump
        Given offset and list of predecessors, if this was destination, and previous linear instruction was unconditional jump

        best attempt at implementing Hint II: Control Flow Crossing of https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf
    """
    global RH
    branches = []
    # TODO:: does this properly handle fallthroughs, how rule was inferred from paper this is not an issue as only jmp is used for rule
    for prev in prev_list:
        if len(list(set(disasm[prev]["groups"]) & BRANCH_GROUPS)) > 0:
            branches += [prev]

    # assign probabilies
    if len(branches) > 0:
        # previous instruction was a jump
        if ((offset - 2) in disasm) and "UNCOND_BR" in disasm[offset - 2]["groups"] and disasm[offset - 2]['size'] == 2:
            # previous instruction 2 bytes ago was a RELATIVE jump
            if DEBUG & 2:
                print(colored("{} updated".format(offset - 2), "yellow"))
            RH[offset - 2].add(("2rel", offset))
            for branch in branches:
                if DEBUG & 2:
                    print(colored("{} updated".format(branch), "yellow"))
                RH[branch].add(("2rel", offset))

        elif ((offset - 5) in disasm) and "UNCOND_BR" in disasm[offset - 5]["groups"] and disasm[offset - 5]['size'] == 5:
            # previous instruction 5 bytes ago was a NEAR jump
            if DEBUG & 2:
                print(colored("{} updated".format(offset - 5), "yellow"))
            RH[offset - 5].add(("2near", offset))
            for branch in branches:
                if DEBUG & 2:
                    print(colored("{} updated".format(branch), "yellow"))
                RH[branch].add(("2near", offset))


def _hint_two_b():
    """ Jump target occulusion
            if a branch has a sequence of valid decodes that includes its destination, likely good code

        TODO:: Not Implemented.
    """
    pass


def _update_reg_references(reg_refs) -> set:
    """ Replace references to both 8 bit, 16 bit, and 64 bit registers with 32 bit

        This is not reference in paper, but inferred aliasing registers may be useful.
        As this implementation is parsing xed or capstone, there is nuance to how written/read reg
            Attempts to omit instruction pointer as many instructions seemed to increment for next

        INFO:: new to this implementation, deviated from paper
    """
    reg_refs_prime = reg_refs
    general_register_tuples = [
        # General purpose registers
        (["XED_REG_AL", "XED_REG_AH", "XED_REG_AX", "XED_REG_RAX"], "XED_REG_EAX"),
        (["XED_REG_BL", "XED_REG_BH", "XED_REG_BX", "XED_REG_RBX"], "XED_REG_EBX"),
        (["XED_REG_CL", "XED_REG_CH", "XED_REG_CX", "XED_REG_RCX"], "XED_REG_ECX"),
        (["XED_REG_DL", "XED_REG_DH", "XED_REG_DX", "XED_REG_RDX"], "XED_REG_EDX")
    ]
    extended_register_tuples = [
        (["XED_REG_DL", "XED_REG_BP", "XED_REG_RBP"], "XED_REG_EBP"),
        (["XED_REG_DL", "XED_REG_SI", "XED_REG_RSI"], "XED_REG_ESI"),
        (["XED_REG_DL", "XED_REG_DI", "XED_REG_RDI"], "XED_REG_EDI"),
        (["XED_REG_DL", "XED_REG_SP", "XED_REG_RSP"], "XED_REG_ESP"),
        # x86_64
        (["XED_REG_R8B", "XED_REG_R8W", "XED_REG_R8"], "XED_REG_R8D"),
        (["XED_REG_R9B", "XED_REG_R9W", "XED_REG_R9"], "XED_REG_R9D"),
        (["XED_REG_R10B", "XED_REG_R10W", "XED_REG_R10"], "XED_REG_R10D"),
        (["XED_REG_R11B", "XED_REG_R11W", "XED_REG_R11"], "XED_REG_R11D"),
        (["XED_REG_R12B", "XED_REG_R12W", "XED_REG_R12"], "XED_REG_R12D"),
        (["XED_REG_R13B", "XED_REG_R13W", "XED_REG_R13"], "XED_REG_R13D"),
        (["XED_REG_R14B", "XED_REG_R14W", "XED_REG_R14"], "XED_REG_R14D"),
        (["XED_REG_R15B", "XED_REG_R15W", "XED_REG_R15"], "XED_REG_R15D"),
    ]

    for ((_low, _high, _16, _64), _32) in general_register_tuples:
        if any(item in reg_refs_prime for item in [_low, _high, _16, _64]):
            reg_refs_prime.discard(_low)
            reg_refs_prime.discard(_high)
            reg_refs_prime.discard(_16)
            reg_refs_prime.discard(_64)
            reg_refs_prime.add(_32)
    for ((_8, _16, _64), _32) in extended_register_tuples:
        if any(item in reg_refs_prime for item in [_8, _16, _64]):
            reg_refs_prime.discard(_8)
            reg_refs_prime.discard(_16)
            reg_refs_prime.discard(_64)
            reg_refs_prime.add(_32)

    if any(item in reg_refs_prime for item in ["IP", "RIP"]):
        reg_refs_prime.discard("IP")
        reg_refs_prime.discard("RIP")
        reg_refs_prime.add("EIP")
    return reg_refs_prime


def _hint_three(offset, prev_list, disasm):
    """ Register Define-Use Relation
            uniform distribution of bytes is unlikley to define instructions, then use them
            * register spilling
            * memory def-use using different instructions

        best attempt at implementing Hint III: Register Define-use Relation. of https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf
    """
    global RH
    if offset not in disasm:
        return

    if DEBUG & 4:
        print(offset, colored(disasm[offset]["str"], "red"))

    for prev in prev_list:
        # Wild-card smaller registers. Same with larger registers. Everything simplifies to 32 bit as this affects 64 and 16 and 8s.
        prev_reg_write = set(disasm[prev]['regs_write'])
        curr_reg_read = set(disasm[offset]['regs_read'])

        # TODO:: omit false positive causing instructions
        # remove eflags and adc to lower false positives
        #   add -> adc shouldnt flag because of eflags
        #   pop -> ret shouldnt flag on esp
        #   eax + 4 written, eax + 8 read, not applicable
        if DEBUG & 4:
            print(prev, colored(disasm[prev]["str"], "magenta"),
                  "from prev inst (red)", colored(curr_reg_read, "yellow"))

        def_use = prev_reg_write & curr_reg_read
        if len(def_use) > 0:
            if DEBUG & 4:
                logger.info("REGs NAME %s", prev_reg_write & curr_reg_read)
            RH[prev].add(("3orig", offset))
            RH[offset].add(("3orig", prev))
        else:
            # If original registers do not match, generalize to registers also affected by write access
            # in x86, 32 write affects 64 bit, as does 32 on lesser, the reverse is not true for smaller
            prev_reg_write = _update_reg_references(prev_reg_write)
            curr_reg_read = _update_reg_references(curr_reg_read)

            if DEBUG & 4:
                print(prev, colored(disasm[prev]["str"], "magenta"),
                      "from prev inst (red)", colored(curr_reg_read, "yellow"))

            gen_def_use = prev_reg_write & curr_reg_read
            if len(gen_def_use) > 0:
                # data flow from current instruction to next
                if DEBUG & 4:
                    logger.info("NOTE, GENERALIZED REGs NAME %s", prev_reg_write & curr_reg_read)
                RH[prev].add(("3gen", offset))
                RH[offset].add(("3gen", offset))


# --- Phase functions


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
def _back_propagation(disasm, code_prob, data_prob, preds):
    """ Iterative analyais to find instructions that lead to bad assembly.
        Outside of control flow, this is guarenteed to be data

        attempting to write ~line 25 algorithm 1 of https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf
    """
    fixed_point = True
    for i in data_prob.keys():
        if data_prob[i] == BOTTOM or i not in preds:
            # Cannot propogate unknown or unknown predecessors
            continue
        if DEBUG & 32:
            print("BACK", i, data_prob[i], preds[i])
        for p in preds[i]:
            if DEBUG & 32:
                print(p > i, data_prob[p] == BOTTOM, data_prob[p] < data_prob[i])

            if data_prob[p] == BOTTOM or data_prob[p] < data_prob[i]:
                data_prob[p] = data_prob[i]
                fixed_point = False
                if p > i:
                    # updated need to continue processing
                    fixed_point = False
        if DEBUG & 32:
            print(i, data_prob[i], preds[i])
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
        data_prob[offset] = 1 - min(occluded_probs)
        print("adjusting {} to {}".format(offset, data_prob[offset]))


@_log_fun_time
def _adjust_code_probs(disasm, code_prob, data_prob, occlusion_space):
    """ Posterior probability by normalization

        attempting to write ~line 31 algorithm 1 of https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf
    """
    for offset, _ in disasm.items():
        if DEBUG & 16:
            logger.info(colored("{} - {} ".format(offset, code_prob[offset]), "green"))
        if data_prob[offset] == 0:
            continue

        if data_prob[offset] == 1.0:
            code_prob[offset] = 0.0
            continue

        numerator  = 1 / data_prob[offset]
        s = numerator
        for j in occlusion_space[offset]:
            if data_prob[j] == 0:
                continue
            s += (1 / data_prob[j])
        code_prob[offset] = numerator / s

        if DEBUG & 16:
            logger.info(colored("{} - {} ".format(offset, code_prob[offset]), "cyan"))


def _compute_fixed_point(disasm, code_prob, data_prob, cfg, preds, occlusion_space):
    """ Main loop of algorithm 1 of https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf
            ~line 8
    """
    global COUNT

    fixed_point = False
    while not fixed_point:
        # go into iteration thinking this could be last pass
        fixed_point = True

        # Forward propagate hints between instructions
        fixed_point = _forward_propagation(disasm, data_prob, cfg) and fixed_point
        if COUNT == 2: break
        # From overlapping candidate instructions, assign probability of data based on surrounding bytes
        _adjust_occlusion_probs(disasm, code_prob, data_prob, occlusion_space)

        fixed_point = _back_propagation(disasm, code_prob, data_prob, preds) and fixed_point

        COUNT += 1
        # terminate and print
        if COUNT % 4000 == 0:
            print("data_prob", data_prob)
            fixed_point = True


# ---- Global reference structures

@_log_fun_time
def _compute_occlusion(disasm):
    """ Mapping from byte to instruction that contained byte
    """
    occlusion = defaultdict(list)
    for offset, details in disasm.items():
        # find mapping of all instructions that overlap with byte n
        for i in range(offset, offset + details["size"]):
            if i == offset:
                continue
            occlusion[i].append(offset)

    return occlusion


@_log_fun_time
def _compute_destinations(disasm):
    dests = {}
    preds = {}
    last_offset = list(disasm)[-1]

    for offset, details in disasm.items():
        # Non-control flow only has fallthrough
        if len(list(set(details["groups"]) & CONTROL_GROUPS)) == 0:
            # TODO:: does not account for multiple sections worth of disassembly
            # Only include destination if in range of possible decodes
            if offset + disasm[offset]['size'] > last_offset:
                dests[offset] = []
                continue

            dests[offset] = [offset + disasm[offset]['size']]
            _create_or_insert(offset, offset + disasm[offset]['size'], preds)
        else:
            # Indirect control flow requires resolving relative address
            if len(list(set(details["groups"]) & CONTROL_GROUPS)) > 0:
                # TODO:: convention for long jump unclear
                if "UNCOND_BR" in details["groups"]:
                    try:
                        dests[offset] = [int(details['op_str'], 16)]
                        _create_or_insert(offset, int(details['op_str'], 16), preds)
                    except ValueError:
                        # Operand was computed
                        dests[offset] = []
                        continue
                elif "COND_BR" in details["groups"] or "CALL" in details["groups"]:
                    try:
                        dests[offset] = [offset + disasm[offset]['size']]
                        dests[offset].append(int(details['op_str'], 16))
                        _create_or_insert(offset, offset + disasm[offset]['size'], preds)
                        _create_or_insert(offset, int(details['op_str'], 16), preds)
                    except ValueError:
                        # Operand was computed
                        dests[offset] = []
                        continue
                else:
                    # Return case
                    dests[offset] = []
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


def extract(disasm: dict):
    global RH
    global H

    res = {}
    data_prob = {}
    code_prob = {}

    # Compute all overlapping instructions
    occlusion_space = _compute_occlusion(disasm)

    # ckompute all sucessors for every instruction
    cfg, preds = _compute_destinations(disasm)

    # Section IV, pg 6, initialize probablity of data to no knowledge
    # TODO:: assumes one section
    min_offset = min(list(disasm.keys()))
    max_offset = max(list(disasm.keys()))
    for offset in range(min_offset, max_offset + 1):
        if offset not in disasm:
            # Set data to guarenteed as invalid decode
            if DEBUG & 1:
                logger.info(offset, "INVALID - ", preds[offset] if offset in preds else "{}")
            data_prob[offset] = 1.0
            code_prob[offset] = 0.0
        else:
            data_prob[offset] = BOTTOM
            code_prob[offset] = BOTTOM
        H[offset] = BOTTOM  # prior distribution at offset
        RH[offset] = set()  # Hints that reach offset

    # define initial probability with hints, H
    for offset, prev_list in preds.items():
        _hint_one(offset, prev_list, disasm)
        _hint_two(offset, prev_list, disasm)
        _hint_three(offset, prev_list, disasm)

    update_H()

    # with forward and backwards propagation, find P
    _compute_fixed_point(disasm, code_prob, data_prob, cfg, preds, occlusion_space)
    # resolve overlapping instructions and normalize for final answer
    _adjust_code_probs(disasm, code_prob, data_prob, occlusion_space)

    # set code probablities
    for i in data_prob:
        if data_prob[i] != BOTTOM:
            code_prob[i] = 1 - data_prob[i]

    # Output final set using threshold
    THRESHOLD = 0.0067  # as per pg 9 of https://www.cs.purdue.edu/homes/zhan3299/res/ICSE19.pdf
    for i in code_prob:
        if code_prob[i] >= THRESHOLD:
            print(i, ":", colored(disasm[i]['str'], "blue"), colored(code_prob[i], "red"),
                    end=" ")
            if DEBUG & 128:
                print(RH[i] if (i in RH) else "{}",
                        end="")
            print()
            res[i] = disasm[i]['str']

    logger.info("Completed after %s passes.", COUNT)
    return {'instructions': res}
