""" Wrapper for using ddisasm to extract basic block and instructions
"""

import os
import subprocess
import json
import logging
import time
import glob

from typing import Optional

SRC_VER = 0.1

name = "ddisasm"
logger = logging.getLogger(name)

# --------------------------- Tool N: DDISASM -----------------------------------------


def _cleanup_tempfiles():
    pass
    # for file in glob.glob('scratch/ddisasm/binary/*'):
    #     try:
    #         os.remove(file)
    #     except:
    #         pass


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
    os.makedirs("scratch/ddisasm/", exist_ok=True)
    os.makedirs("scratch/ddisasm/binary/", exist_ok=True)
    exe = "docker run --user=$(id -u):$(id -g) --rm -v {}:/binary -v {}:/scratch grammatech/ddisasm ddisasm".format(file_test, scratch_dir)
    cmd = "{} --json scratch/ddisasm/{}/cfg.json {} --debug-dir scratch/ddisasm/{} > /dev/null".format(exe, "binary", "binary", "binary")
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


def _extract_insn_facts(header_interface, exaustive_facts):
    """ Command to parse fact file for instructions
    """
    instruction_map = {}

    
    # use block information to pull out instructions found in CFG
    with open("scratch/ddisasm/binary/block_information.csv") as block_info_file:
        lines = block_info_file.read().split('\n')
        for line in lines:

            # vaddr, size, end addr or last?
            block_info = line.split('\t')
            try:
                block_info = [int(item, 16) for item in block_info]  # convert to list of ints
            except:
                continue
            i = _get_offset(block_info[0], header_interface)

            while i < _get_offset(block_info[3], header_interface):
                insn = exaustive_facts[i]
                file_offset = _get_offset(i, header_interface)
                instruction_map[file_offset] = insn['mneu']
                i += insn['size']
    return instruction_map


def _parse_exaustive(complete_facts_path, header_interface):
    instruction_map = {}
    # instruction_complete.facts is exaustive disassembly
    # instructions.facts is very stripped down and does not encompass most instructions
    # Utilizing exaustive + basic block information
    with open(complete_facts_path) as f:
        lines = f.read().split('\n')
        for l in lines:
            inst_comp_tokens = l.split('\t')
            if inst_comp_tokens[0] == '' or len(inst_comp_tokens) < 3:
                continue
            vaddr = int(inst_comp_tokens[0],16)
            instruction_map[_get_offset(vaddr, header_interface)] = {'mneu': inst_comp_tokens[2] + ' ' + inst_comp_tokens[3], 'size': int(inst_comp_tokens[1])}
    
    return instruction_map


def _extract_block_facts(cfg_info_path, header_interface):
    data_map = {}
    block_map = {}

    with open(cfg_info_path, 'r') as f:
        ddisasm_output = json.load(f)
        modules = ddisasm_output['modules']
        for module in modules:
            
            # DEBUG:: list of elements in knowledge store
            # print(f"module key: {module.keys()}")

            # Save data references while we are here
            if "data" in module:
                _record_data(data_map, module['data'])
            block_uuids = {}
            #if 'blocks' not in module["sections"]:
            #    # If we do not have blocks return None, and pass up accordingly
            #    logger.info('No Basic Blocks found.')
            #    return None
            blocks = []
            for x in module["sections"]:
                bintervals = x['byteIntervals'][0]
                if 'blocks' in bintervals:
                    vaddr = int(bintervals['address'])
                    for blks in bintervals['blocks']:
                        if 'size' in bintervals:
                            if 'code' in blks:
                                code_data = blks['code']
                                block_uuids[code_data['uuid']] = {'vaddr': vaddr, 'size': int(code_data['size'])}
                            else:
                                pass
                    

                # if 'size' in bintervals:
                 #     block_uuids[bintervals['uuid']] = {'vaddr': int(bintervals['address']), 'size' : int(bintervals['size'])}
                
            # for bb in blocks:
            #     # {'uuid': 'Vm+5NJ4oTmOAfKPA3CUxaA==', 'address': '4203014', 'size': '10'}
            #     # maps uuid to addresses with size
            #     # Omit bb that lack size
            #     if bb['size']:
                    
            #         block_uuids[bb['uuid']] = {'vaddr': int(bb['address']), 'size': int(bb['size'])}
            try:
                for edge in ddisasm_output['cfg']['edges']:
                    # 'sourceUuid': 'F8LEDx73RKywaAupHUWBvw==', 'targetUuid': 'lUxHPXA/SFus/NALX22X6g==
                    if edge['sourceUuid'] not in block_uuids:
                        src = None
                    else:
                        src = _get_offset(block_uuids[edge['sourceUuid']]['vaddr'], header_interface)

                    if edge['targetUuid'] not in block_uuids:
                        dst = None
                    else:
                        dst = _get_offset(block_uuids[edge['targetUuid']]['vaddr'], header_interface)

                    if src not in block_map:
                        block_map[src] = {'targets': [],
                                          'size': block_uuids[edge['sourceUuid']]['size']}
                    if dst is not None:
                        block_map[src]['targets'].append(dst)
            except:
                print("ddsiasm_output error")

            # List of basic block identifiers, no use as we can derive from edge list
            # print('v', module['cfg']['vertices'])


    return data_map, block_map


def _populate_block_map(header_interface, block_map, insn_map, exaustive_facts):
    for bb in block_map:
        members = []

        insn = bb
        while insn < bb + block_map[bb]['size']:
            members.append((insn, exaustive_facts[_get_rva(insn, header_interface)]['mneu']))
            insn += exaustive_facts[_get_rva(insn, header_interface)]['size']
        block_map[bb]['members'] = members
        del block_map[bb]['size']


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
    logging.info(_run_ddisasm(file_test, scratch_dir))

    end = time.time()
    output_map["meta"]["time"] = end - start
    
    exaustive_facts = _parse_exaustive("scratch/ddisasm/binary/instruction.facts", header)
    output_map["instructions"] = _extract_insn_facts(header, exaustive_facts)

    res = _extract_block_facts('scratch/ddisasm/binary/cfg.json', header)

    if res is None:
        return None
    output_map['data'], output_map['original_blocks'] = res

    _populate_block_map(header, output_map['original_blocks'], output_map['instructions'], exaustive_facts)

    # FIXME:: replace references to relative scratch with api
    # FIXME:: replace general "binary" files with temp_name
    _cleanup_tempfiles()
    return output_map
