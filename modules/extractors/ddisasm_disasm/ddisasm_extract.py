""" Wrapper for using ddisasm to extract basic block and instructions
"""

import os
import subprocess
import json
import logging
import time
import glob
import shutil

from typing import Optional

SRC_VER = 0.1

name = "ddisasm"
logger = logging.getLogger(name)

# --------------------------- Tool N: DDISASM -----------------------------------------


def _cleanup_tempfiles(scratch_dir: str, temp_file: str):
    basename = os.path.basename(temp_file)
    for file_path in glob.glob(os.path.join('scratch', 'ddisasm', basename)):
        logger.debug(f'Trying to delete {file_path}')
        try:
            os.remove(file_path)
        except IsADirectoryError:
            shutil.rmtree(file_path)
        except PermissionError:
            logger.debug(f'Permission error cannot delete {file_path}')


def _get_offset(vaddr, header_interface):
    if header_interface.type == "ELF":
        if header_interface.etype == "Shared object file":
            # If shared object, ddisasm does not rebase
            return vaddr
        else:
            # non-PIE, so use header info
            return header_interface.get_offset(vaddr)
    else:
        return vaddr


def _get_rva(vaddr, header_interface):
    return vaddr


def _scribe_version(output_map):
    output_map['meta'] = {}
    output_map['meta']["tool_ver"] = "???"
    output_map['meta']["src_ver"] = SRC_VER
    output_map['meta']["name"] = "Ddisasm"


def _run_ddisasm(file_test, scratch_dir) -> Optional[str]:
    basename = os.path.basename(file_test)
    os.makedirs("scratch/ddisasm/", exist_ok=True)
    os.makedirs(f"scratch/ddisasm/{basename}/", exist_ok=True)

    # Mount temp file used in test to binary, store results in scratch dir under binary
    exe = f"docker run --rm -v {file_test}:/binary -v {scratch_dir}:/scratch grammatech/ddisasm ddisasm"
    cmd = f"{exe} --json scratch/ddisasm/{basename}/cfg.json /binary --debug-dir scratch/ddisasm/{basename} > {os.devnull}"

    # FIXME:: put back to debug
    logger.info(cmd)
    with open(os.devnull, "w") as null:
        try:
            return subprocess.check_output(cmd, universal_newlines=True, shell=True, stderr=null)
        except subprocess.CalledProcessError as grepexc:
            logger.error("Ddisasm returned with non-zero exit code %s - %s",
                         grepexc.returncode,
                         grepexc.output)
            return None


def _record_data(output_map, data_list) -> None:
    """ Data found in analysis
    """
    # TODO:: parse data from output
    logging.debug(data_list)


def _extract_insn_facts(block_fact_file: str, header_interface, exaustive_facts):
    """ Command to parse fact file for instructions
    """
    instruction_map = {}

    # use block information to pull out instructions found in CFG
    if os.path.exists(block_fact_file) is False:
        logger.error("Could not find block facts file: %s", block_fact_file)
        return instruction_map
    with open(block_fact_file, 'r') as block_info_file:
        lines = block_info_file.read().split('\n')
        for line in lines:
            if line == "":
                # Handle empty line
                continue

            # vaddr, size, end addr or last?
            block_info = line.split('\t')
            block_info = [int(item, 16) for item in block_info]  # convert to list of ints

            i = _get_offset(block_info[0], header_interface)
            while i < _get_offset(block_info[3], header_interface):
                insn = exaustive_facts[i]
                file_offset = i
                instruction_map[file_offset] = insn['mneu']
                i += insn['size']
    return instruction_map


def _parse_exaustive(complete_facts_path, header_interface):
    instruction_map = {}
    # instruction_complete.facts is exaustive disassembly
    # instructions.facts is very stripped down and does not encompass most instructions
    # Utilizing exaustive + basic block information
    if os.path.exists(complete_facts_path) is False:
        logger.error("Could not find exaustive facts file: %s", complete_facts_path)
        return instruction_map
    with open(complete_facts_path) as f:
        lines = f.read().split('\n')
        for l in lines:
            inst_comp_tokens = l.split('\t')
            if inst_comp_tokens[0] == '' or len(inst_comp_tokens) < 3:
                continue
            vaddr = int(inst_comp_tokens[0], 16)
            # print("debugging, where is operands" + str(inst_comp_tokens))
            instruction_map[_get_offset(vaddr, header_interface)] = {'mneu': inst_comp_tokens[2] + ' ' + inst_comp_tokens[3], 'size': int(inst_comp_tokens[1])}

    return instruction_map


def _extract_block_facts(cfg_info_path, header_interface):
    data_map = {}
    block_map = {}
    if os.path.exists(cfg_info_path) is False:
        logger.error("Could not find block facts file: %s", cfg_info_path)
        return data_map, block_map
    with open(cfg_info_path, 'r') as f:
        # print("block_facts", blk_info_path)
        lines = f.read().split('\n')
        for line in lines:
            block_tokens = line.split('\t')
            if block_tokens[0] == '' or len(block_tokens) < 3:
                continue

            vaddr = int(block_tokens[0], 16)
            # print("debugging, where is operands" + str(inst_comp_tokens))
            block_map[_get_offset(vaddr, header_interface)] = {'size': int(block_tokens[1])}
    return data_map, block_map


def _populate_block_map(header_interface, block_map, insn_map, exhaustive_facts):
    for bb in block_map:
        members = []

        insn = bb
        while bb <= insn < bb + block_map[bb]['size']:
            members.append((insn, exhaustive_facts[_get_rva(insn, header_interface)]['mneu']))
            insn += exhaustive_facts[_get_rva(insn, header_interface)]['size']
        block_map[bb]['members'] = members
        del block_map[bb]['size']
        block_map[bb]['dests'] = []


def extract(file_test, header, scratch_dir):
    """ Runs instruction extraction from ghidraHEADLESS using a java language script
        Input -
            file_test - Sample using bap.run() which runs analyses
            header_interface (header) - header object using header utiility lib
    """
    output_map = {}
    output_map["meta"] = {}
    output_map["instructions"] = {}
    output_map["original_blocks"] = {}
    output_map["canon_blocks"] = {}

    _scribe_version(output_map)

    if not header.known_format:
        logger.info("File Sample is of unknown format, Ddisasm returning empty output.")
        return None

    start = time.time()

    # populate fact files
    ddisasm_stdout = _run_ddisasm(file_test, scratch_dir)
    if ddisasm_stdout is None:
        return None

    end = time.time()
    output_map["meta"]["time"] = end - start

    basename = os.path.basename(file_test)

    # earlier versions used instructions_complete
    if os.path.exists(os.path.join(scratch_dir, "ddisasm", basename, "disassembly")) is True:
        insns_facts = "disassembly/instruction.facts"
        block_info = "disassembly/block_information.csv"
    else:
        insns_facts = "instruction.facts"
        block_info = "block_information.csv"

    inst_facts = os.path.join(scratch_dir, "ddisasm", basename, insns_facts)
    exaustive_facts = _parse_exaustive(inst_facts, header)
    block_fact_file = os.path.join(scratch_dir, "ddisasm", basename, block_info)
    output_map["instructions"] = _extract_insn_facts(block_fact_file, header, exaustive_facts)

    block_facts = os.path.join(scratch_dir, "ddisasm", basename, block_info)  # previous versions could use cfg.json
    # likely still can use cfg.json with more research
    res = _extract_block_facts(block_facts, header)

    if res is None:
        return None
    output_map['data'], output_map['original_blocks'] = res

    _populate_block_map(header, output_map['original_blocks'], output_map['instructions'], exaustive_facts)

    # _cleanup_tempfiles(scratch_dir, file_test)
    return output_map
