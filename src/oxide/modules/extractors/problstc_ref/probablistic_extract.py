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

""" Probablistic Disasm processing script for instruction offsets
"""

import subprocess
import os
from typing import Optional
import time
import logging

NAME = "probablist_extract"
logger = logging.getLogger(NAME)

# ------------------------------- Tool: Probablistic Disassembly -----------------------------------


def test_docker():
    """ Test if docker is configured and installed
    """
    cmd = "docker"
    with open(os.devnull, "w") as null:
        subprocess.check_output(cmd, universal_newlines=True, shell=True, stderr=null)


def test_module(scratch_dir, probdisasm_image):
    """ Test if probablistic disasm is configured and installed
    """
    invoke = '"./superset_disasm.native"'
    cmd = 'docker run --rm -v {}:dir/ --entrypoint /bin/bash {} -c {}'.format(scratch_dir,
                                                                              probdisasm_image,
                                                                              invoke)
    with open(os.devnull, "w") as null:
        subprocess.check_output(cmd, universal_newlines=True, shell=True, stderr=null)


def _extract_probdisasm_disasm(file_name: str, scratch_dir: str) -> str:
    """ Executes docker image for pharos to dump output
        Parameters -
            file_name (str): program under test
            header_interface (header): header providing access to whether 64 bit
    """
    file_base_name = os.path.basename(file_name)
    invoke = '"./superset_disasm.native --target=dir/{} --save_addrs --tp_threshold=0.50 && cp *.txt dir/"'.format(file_base_name)
    cmd = 'docker run --rm -v {}:/home/bap/workspace/superset_disasm/dir/ --entrypoint /bin/bash {} -c {}'.format(scratch_dir,
                                                                                                                  PROBDISASM_IMAGE,
                                                                                                                  invoke)
    logger.info(cmd)
    with open(os.devnull, "w") as null:
        return subprocess.check_output(cmd, universal_newlines=True, shell=True, stderr=null)


def _process_probdisasm_results(probdisasm_results: str, header_interface) -> (list, list, list):
    """ From serial output from probdisasm docker image, parse into instructions

        Expected Format -
            0x287:64u
            0x288:64u
            0x56B:64u

        Parameters -
            probdisasm_result (str): raw output from tool
            header_interface (header): binary header giving access to 64 bit and object format
            output_map (dict): dictionary to store instructions and basic blocks
    """
    instr = []

    for line in probdisasm_results.split("\n"):
        # remove size of address
        try:
            line = line[:line.index(':')]
        except ValueError:
            continue
        offset = header_interface.get_offset(int(line, 16))
        instr.append(offset)
    return instr


def _record_instr(output_map: dict, instr: list, ex_disasm) -> None:
    # Keep dictionary for consistency
    for offset in instr:
        # TODO:: exclude if not in ex disasm
        output_map["instructions"][offset] = ex_disasm[offset]["str"] if offset in ex_disasm else "foo"


def extract(file_test: str, ex_disasm: dict, header_interface, scratch_dir: str) -> Optional[dict]:
    """ Runs instruction extraction from pharos docker image using python language script
        Input -
            file_test (string) - Sample using bap.run() which runs analyses
            header_interface (header) - header object using header utiility lib
    """
    # Define Header interface
    output_map = {}
    # timing, oxide version, and tool version
    output_map["meta"] = {}
    output_map["instructions"] = {}

    if not header_interface.known_format:
        logger.info("File Sample is of unknown format, Probablistic returning empty output.")
        return None

    if header_interface.type == "MACHO":
        # Does not work on MACHO binaries, as relies on Pharos
        pass

    start = time.time()

    # This analysis implicitly creates file
    _extract_probdisasm_disasm(file_test, scratch_dir)

    end = time.time()

    output_map["meta"]["time"] = end - start

    with open('{}_addrs.txt'.format(file_test), "r") as f:
        instr = _process_probdisasm_results(f.read(), header_interface)
        _record_instr(output_map, instr, ex_disasm)

    return output_map
