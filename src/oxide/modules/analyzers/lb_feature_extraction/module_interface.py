""""
Copyright 2023 National Technology & Engineering Solutions",
of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS,",
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

DESC = "Performs feature extraction on binary extracting features relevant to conditional statements."
NAME = "lb_feature_extraction"

# imports
import logging

import angr

from typing import Dict, Any, List
from core.libraries.angr_utils import init_angr_project

from function_lib import (
    sensitive_functions,
    system_input_checks,
    pthread_funcs,
    functions_ignore,
)

import os, psutil

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    """Documentation for this module
    private - Whether module shows up in help
    set - Whether this module accepts collections
    atomic - TBD
    """
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    """Entry point for analyzers, these do not store in database
    these are meant to be very quickly computed things passed along
    into other modules
    """
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    results = {}
    opts = {}

    for oid in oid_list:
        triggerResults = {}
        # Collect information and objects used for backwards slicing
        f_name, header = _configure_bs(oid)
        if f_name == False or header == False:
            continue
        p = init_angr_project(f_name, header)
        base_addr = header.image_base

        # Pull disasm and basic_block module results
        disasm = api.retrieve("ghidra_disasm", oid)
        bbs = api.retrieve("basic_blocks", oid, opts)[oid]
        capa_results = api.retrieve("capa_results", oid)[oid]

        if disasm != None:
            functions = disasm["functions"]
        else:
            continue

        triggers = _findTriggerStmts(bbs)

        # Iterate through each function found in executable.
        for function in functions:
            functionName = functions[function]["name"]
            if (
                functionName.startswith("_")
                or functionName.startswith("__")
                or functionName in functions_ignore
            ):
                pass
            else:
                # Pull information relevant to current function.
                functionTriggers = {}

                functionBlocks = functions[function]["blocks"]
                commonBlocks = _getCommonBlocks(bbs, functionBlocks)
                function_calls = _call_mapping(
                    function, functions[function], functions, bbs
                )

                # Iterate through blocks in function
                for block in functionBlocks:
                    cb = None
                    suspicous_triggers = []
                    if block in triggers:
                        branches = _computeBranch(block, bbs, functionBlocks)

                        if len(branches) == 3:
                            functionTriggers[block] = {}
                            branchA = {}
                            branchB = {}

                            branchA_blocks, branchB_blocks, cb = _compareBranches(
                                branches, commonBlocks
                            )

                            # Branch A
                            branchA["Blocks"] = branchA_blocks

                            # Branch B
                            branchB["Blocks"] = branchB_blocks

                            # Feature Extraction A
                            S_A = numSensFunctCalls(branchA, bbs)
                            P_A = dataFlow(branchA, bbs)
                            M1_A = numExclFunctCalls(branchA, bbs, functionBlocks)
                            S1_A = numExclSensFunctCalls(branchA, bbs, functionBlocks)

                            # Feature Extraction B
                            S_B = numSensFunctCalls(branchB, bbs)
                            P_B = dataFlow(branchB, bbs)
                            M1_B = numExclFunctCalls(branchB, bbs, functionBlocks)
                            S1_B = numExclSensFunctCalls(branchB, bbs, functionBlocks)

                            # Behavior Difference
                            branchDifference = behaviorDifference(branchA, branchB, bbs)

                            functionTriggers[block]["S"] = S_A + S_B
                            functionTriggers[block]["P"] = P_A + P_B
                            functionTriggers[block]["M1"] = M1_A + M1_B
                            functionTriggers[block]["S1"] = S1_A + S1_B
                            functionTriggers[block]["J"] = branchDifference
                            functionTriggers[block]["CAPA_A"] = TBD_A
                            functionTriggers[block]["CAPA_B"] = TBD_B

                            # Determine source of variables used in trigger stmt
                            # if function_calls != {}:
                            #     bs_chosen_statements = backward_slicing(p, block, base_addr)
                            #     for bs_block in bs_chosen_statements:
                            #         if bs_block in function_calls:
                            #             if function_calls[bs_block][1] in system_input_checks:
                            #                 suspicous_triggers += [function_calls[bs_block][1]]
                            if len(suspicous_triggers) != 0:
                                functionTriggers[block]["C"] = 1
                            else:
                                functionTriggers[block]["C"] = 0

                if len(functionTriggers) != 0:
                    triggerResults[functionName] = functionTriggers
        results[oid] = triggerResults
    return results


##########################
### Feature Extraction ###
##########################


def backward_slicing(p, block, base_addr):
    cfg = p.analyses.CFGEmulated(
        keep_state=True,
        state_add_options=angr.sim_options.refs,
        context_sensitivity_level=2,
    )

    location = int(hex(base_addr + block), base=16)

    target_node = cfg.get_any_node(location)

    # bs = p.analyses.BackwardSlice(cfg, cdg=cdg, ddg=ddg, targets=[ (target_node, 0) ], control_flow_slice=True)
    bs = p.analyses.BackwardSlice(
        cfg, targets=[(target_node, 0)], control_flow_slice=True
    )

    return bs.chosen_statements


# Feature S - Number of sensitive functions called in guarded code.
def numSensFunctCalls(branch, bbs):
    calls = _getFunctionCalls(branch, bbs)
    sensitiveCalls = _getSensitiveFunctionCalls(calls, bbs)
    return len(sensitiveCalls)


# Feature P - Are parameters of condition used in guarded code?
def dataFlow(branch, bbs):
    return 0


# Feature M1 - Number of functions exclusively called in guarded code.
def numExclFunctCalls(branch, bbs, functionBlocks):
    calls = _getFunctionCalls(branch, bbs)
    excelusiveCalls = _getExclusiveFunctionCalls(calls, bbs, functionBlocks)
    return len(excelusiveCalls)


# Feature S1 - Number of sensitive function exclusively called only in guarded code
def numExclSensFunctCalls(branch, bbs, functionBlocks):
    calls = _getFunctionCalls(branch, bbs)
    sensitiveCalls = _getSensitiveFunctionCalls(calls, bbs)
    excelusiveCalls = _getExclusiveFunctionCalls(sensitiveCalls, bbs, functionBlocks)
    return len(excelusiveCalls)


# Feature J - Behavior differences between two branches
def behaviorDifference(branchA, branchB, bbs):
    # Branch A
    callsA = _getFunctionCalls(branchA, bbs)
    sensitiveCallsA = _getSensitiveFunctionCalls(callsA, bbs)

    # Branch A
    callsB = _getFunctionCalls(branchB, bbs)
    sensitiveCallsB = _getSensitiveFunctionCalls(callsB, bbs)

    # Calculate jaccard distance for two branches
    branchDifference = _jaccard_distance(sensitiveCallsA, sensitiveCallsB)

    return branchDifference


###############################################
### Functions Supporting Feature Extraction ###
###############################################


def _jaccard_distance(A, B):
    # Find symmetric difference of two sets
    nominator = list(set(A).symmetric_difference(set(B)))

    # Find union of two sets
    denominator = list(set(A) | set(B))
    if len(denominator) == 0:
        distance = 0
    else:
        distance = len(nominator) / len(denominator)

    return distance


def _getFunctionCalls(branch, bbs):
    calls = []
    for block in branch:
        if isinstance(block, str):
            pass
        else:
            last_insn = bbs[block]["last_insn"]
            if "call" in last_insn[1]:
                calls.extend([block])
    return calls


def _getSensitiveFunctionCalls(functionCalls, bbs):
    sensFunctionCalls = []
    for call in functionCalls:
        if call in sensitive_functions:
            sensFunctionCalls[call] = functionCalls[call]
    return sensFunctionCalls


def _getExclusiveFunctionCalls(functionCalls, bbs, functionBlocks):
    calls = []
    for call in functionCalls:
        dests = bbs[call]["dests"]
        for dest in dests:
            if dest not in functionBlocks:
                pass
            else:
                if len(bbs[dest]["dests_prev"]) == 1:
                    calls.extend([call])
    return calls


# This will find all calls_to. It will then add that to a dictionary and iterate back through the calls_to and assign them correctly to the correct calls_to
def _call_mapping(function_addr, function_data, functions, basic_blocks):

    call_mapping = {}
    function_addresses = functions.keys()
<<<<<<< HEAD
    
    #Generating calls_to
    for block_addr in function_data['blocks']:
        if block_addr in basic_blocks:
            for instruction_offset, instruction in basic_blocks[block_addr]['members']:
                if instruction[:4] == 'call':
                    for offset in basic_blocks[block_addr]['dests']:
                        if offset in function_addresses:
                            called_file_offset = offset
                            call_mapping[instruction_offset] = functions[called_file_offset]['name']
=======

    # Generating calls_to
    for block_addr in function_data["blocks"]:
        for instruction_offset, instruction in basic_blocks[block_addr]["members"]:
            if instruction[:4] == "call":
                for offset in basic_blocks[block_addr]["dests"]:
                    if offset in function_addresses:
                        called_file_offset = offset
                        call_mapping[instruction_offset] = functions[
                            called_file_offset
                        ]["name"]
>>>>>>> f185dda (pushing code to try and figure out memory issues)

    return call_mapping


def _findTriggerStmts(bbs):
    triggers = {}
    for b in bbs:
        dests = bbs[b]["dests"]
        trigger = {}
        if len(dests) > 1:
            if _isCall(bbs[b]["last_insn"][1]):
                pass
            else:
                trigger = bbs[b]

                triggers[b] = trigger
    return triggers


def _computeBranch(block, bbs, functionBlocks):
    triggerBranches = [block]
    dests = bbs[block]["dests"]
    for branch in dests:
        dominators = []
        if branch not in functionBlocks or branch not in bbs:
            pass
        else:
            if len(bbs[branch]["dests"]) > 0:
                triggerBranches.extend(
                    [
                        [
                            branch,
                            _computeSubBranches(
                                branch, bbs, functionBlocks, dominators
                            ),
                        ]
                    ]
                )
            elif bbs[branch]["dests"] == []:
                triggerBranches.extend([branch])

    return triggerBranches


def _computeSubBranches(block, bbs, functionBlocks, dominators):
    triggerBranches = []
    dests = bbs[block]["dests"]
    for branch in dests:
        if branch not in functionBlocks or branch not in bbs:
            pass
        elif branch in dominators:
            triggerBranches.extend(["LOOP -> " + str(branch)])
        else:
            dominators.extend([branch])
            if len(bbs[branch]["dests"]) > 0:
                triggerBranches.extend(
                    [
                        branch,
                        _computeSubBranches(branch, bbs, functionBlocks, dominators),
                    ]
                )
            elif bbs[branch]["dests"] == []:
                triggerBranches.extend([branch])
    return triggerBranches


def _compareBranches(triggerBranches, commonBlocks):
    branchMaps = []
    pathA = []
    pathB = []
    index = 1
    cb = None
    while True:
        branchMap = {}
        level = 0
        branchMap = _getBranchMap(branchMap, triggerBranches[index], level)
        branchMaps.extend([branchMap])
        if index == 2:
            break
        else:
            index += 1
    branchA = branchMaps[0]
    branchB = branchMaps[1]
    for cb in commonBlocks:
        if cb in branchA and cb in branchB:
            depthA = branchA[cb]
            depthB = branchB[cb]
            pathA = _getPath(depthA, branchA)
            pathB = _getPath(depthB, branchB)
            break
    return pathA, pathB


def _getBranchMap(branchMap, blocks, level):
    if isinstance(blocks, list):
        for b in blocks:
            if isinstance(b, list):
                branchMap = _getBranchMap(branchMap, b, level + 1)
            else:
                branchMap[b] = level + 1
    else:
        branchMap[blocks] = level
    return branchMap


def getCommonBlocks(bbs, functionBlocks):
    # Get common blocks
    commonBlocks = {}
    for fb in functionBlocks:
        if len(bbs[fb]["dests_prev"]) > 1:
            commonBlocks[fb] = None
    return commonBlocks


def _getPath(depth, branch):
    path = []
    index = 0
    while index <= depth:
        for block in branch:
            if branch[block] < depth:
                if branch[block] == index:
                    path.extend([block])
        index += 1
    return path


def _configure_bs(oid):
    src = api.source(oid)
    data = api.get_field(src, oid, "data", {})
    src_type = api.get_field("src_type", oid, "type")
    header = api.get_field("object_header", oid, oid)
    if not header:
        logger.info("No header found for %s in %s", oid, NAME)
        return False, False
    header.type = src_type
    f_name = api.get_field("file_meta", oid, "names").pop()
    f_name = api.tmp_file(f_name, data)
    return f_name, header


def _getCommonBlocks(bbs, functionBlocks):
    # Get common blocks
    commonBlocks = []
    for fb in functionBlocks:
        if fb in bbs and len(bbs[fb]["dests_prev"]) > 1:
            commonBlocks.extend([fb])
    return commonBlocks

<<<<<<< HEAD
=======

# This will  find all calls_to. It will then add that to a dictionary and iterate back through the calls_to and assign them correctly to the correct calls_to
def _call_mapping(function_addr, function_data, functions, basic_blocks):

    call_mapping = {}
    function_addresses = functions.keys()

    # Generating calls_to
    for block_addr in function_data["blocks"]:
        if block_addr in basic_blocks:
            for instruction_offset, instruction in basic_blocks[block_addr]["members"]:
                if instruction[:4] == "call":
                    for offset in basic_blocks[block_addr]["dests"]:
                        if offset in function_addresses:
                            called_file_offset = offset
                            # call_mapping[instruction_offset] = [offset, functions[called_file_offset]['name']]
                            call_mapping[instruction_offset] = [
                                called_file_offset,
                                functions[called_file_offset]["name"],
                            ]
    return call_mapping

>>>>>>> f185dda (pushing code to try and figure out memory issues)

def _isCall(instruction):
    if instruction.startswith("call"):
        return True
    else:
        return False


# Functions in the C library that check system or user inputs
system_input_checks = [
    "assert",
    "atexit",
    "catgets6",
    "catopen6",
    "clock",
    "fdopen5",
    "fgetc1",
    "fgets1",
    "fgetwc6",
    "fgetws6",
    "fileno5",
    "fopen",
    "fread",
    "freopen",
    "fscanf",
    "ftell1",
    "fwide6",
    "fwscanf6",
    "getc1",
    "getchar1",
    "getenv",
    "gets",
    "getwc6",
    "getwchar6",
    "mbsinit4",
    "nl_langinfo4",
    "putenv",
    "rand",
    "rand_r",
    "regcomp",
    "scanf",
    "setlocale",
    "sscanf",
    "swscanf",
    "time",
    "time64",
    "vfscanf",
    "vfwscanf",
    "vscanf",
    "vsscanf",
    "vswscanf",
    "vwscanf",
    "wscanf6",
]

# Functions found to be vulnerable or perform sensitive operations
sensitive_functions = {
    "abort",
    "assert",
    "atexit",
    "atof",
    "atoi",
    "atol",
    "calloc",
    "catclose6",
    "catgets6",
    "catopen6",
    "clearerr",
    "exit",
    "fclose",
    "fdopen5",
    "fflush1",
    "fgetc1",
    "fgetpos1",
    "fgets1",
    "fileno5",
    "fopen",
    "fprintf",
    "fputc1",
    "fputs1",
    "fputwc6",
    "fputws6",
    "fread",
    "free",
    "freopen",
    "fscanf",
    "fseek1",
    "fsetpos1",
    "ftell1",
    "fwide6",
    "fwprintf6",
    "fwrite",
    "fwscanf6",
    "getc1",
    "getchar1",
    "getenv",
    "gets",
    "getwc6",
    "getwchar6",
    "iswprint4",
    "longjmp",
    "malloc",
    "nl_langinfo4",
    "perror",
    "printf",
    "putc1",
    "putchar1",
    "putenv",
    "puts",
    "putwc6",
    "putwchar6",
    "raise",
    "realloc",
    "regcomp",
    "regfree",
    "remove",
    "rename",
    "rewind1",
    "scanf",
    "setbuf",
    "setjmp",
    "setlocale",
    "setvbuf",
    "signal",
    "sprintf",
    "srand",
    "sscanf",
    "strcat",
    "strcpy",
    "strerror",
    "swprintf",
    "swscanf",
    "system",
    "tmpfile",
    "tmpnam",
    "ungetc1",
    "ungetwc6",
    "va_copy",
    "va_end",
    "va_start",
    "vfprintf",
    "vfscanf",
    "vfwprintf6",
    "vfwscanf",
    "vprintf",
    "vscanf",
    "vsprintf",
    "vsnprintf",
    "vsscanf",
    "vswprintf",
    "vswscanf",
    "vwprintf6",
    "vwscanf",
    "wcscat",
    "wcscpy",
    "wprintf6",
    "wscanf6",
}

# Functions that should be ingnored as they are generated by the compiler
functions_ignore = {
    "__libc_start_main",
    "__do_global_dtors_aux",
    "__cxa_finalize",
    "_init",
    "frame_dummy",
    "__libc_csu_init",
    "register_tm_clones",
    "deregister_tm_clones",
    "_start",
    "__stack_chk_fail",
    "puts",
    "__libc_csu_init",
}
# Functions in the C library that check system or user inputs
system_input_checks = [
    "assert",
    "atexit",
    "catgets6",
    "catopen6",
    "clock",
    "fdopen5",
    "fgetc1",
    "fgets1",
    "fgetwc6",
    "fgetws6",
    "fileno5",
    "fopen",
    "fread",
    "freopen",
    "fscanf",
    "ftell1",
    "fwide6",
    "fwscanf6",
    "getc1",
    "getchar1",
    "getenv",
    "gets",
    "getwc6",
    "getwchar6",
    "mbsinit4",
    "nl_langinfo4",
    "putenv",
    "rand",
    "rand_r",
    "regcomp",
    "scanf",
    "setlocale",
    "sscanf",
    "swscanf",
    "time",
    "time64",
    "vfscanf",
    "vfwscanf",
    "vscanf",
    "vsscanf",
    "vswscanf",
    "vwscanf",
    "wscanf6",
]

# Functions found to be vulnerable or perform sensitive operations
sensitive_functions = {
    "abort",
    "assert",
    "atexit",
    "atof",
    "atoi",
    "atol",
    "calloc",
    "catclose6",
    "catgets6",
    "catopen6",
    "clearerr",
    "exit",
    "fclose",
    "fdopen5",
    "fflush1",
    "fgetc1",
    "fgetpos1",
    "fgets1",
    "fileno5",
    "fopen",
    "fprintf",
    "fputc1",
    "fputs1",
    "fputwc6",
    "fputws6",
    "fread",
    "free",
    "freopen",
    "fscanf",
    "fseek1",
    "fsetpos1",
    "ftell1",
    "fwide6",
    "fwprintf6",
    "fwrite",
    "fwscanf6",
    "getc1",
    "getchar1",
    "getenv",
    "gets",
    "getwc6",
    "getwchar6",
    "iswprint4",
    "longjmp",
    "malloc",
    "nl_langinfo4",
    "perror",
    "printf",
    "putc1",
    "putchar1",
    "putenv",
    "puts",
    "putwc6",
    "putwchar6",
    "raise",
    "realloc",
    "regcomp",
    "regfree",
    "remove",
    "rename",
    "rewind1",
    "scanf",
    "setbuf",
    "setjmp",
    "setlocale",
    "setvbuf",
    "signal",
    "sprintf",
    "srand",
    "sscanf",
    "strcat",
    "strcpy",
    "strerror",
    "swprintf",
    "swscanf",
    "system",
    "tmpfile",
    "tmpnam",
    "ungetc1",
    "ungetwc6",
    "va_copy",
    "va_end",
    "va_start",
    "vfprintf",
    "vfscanf",
    "vfwprintf6",
    "vfwscanf",
    "vprintf",
    "vscanf",
    "vsprintf",
    "vsnprintf",
    "vsscanf",
    "vswprintf",
    "vswscanf",
    "vwprintf6",
    "vwscanf",
    "wcscat",
    "wcscpy",
    "wprintf6",
    "wscanf6",
}

# Functions that should be ingnored as they are generated by the compiler
functions_ignore = {
    "__libc_start_main",
    "__do_global_dtors_aux",
    "__cxa_finalize",
    "_init",
    "frame_dummy",
    "__libc_csu_init",
    "register_tm_clones",
    "deregister_tm_clones",
    "_start",
    "__stack_chk_fail",
    "puts",
    "__libc_csu_init",
}
