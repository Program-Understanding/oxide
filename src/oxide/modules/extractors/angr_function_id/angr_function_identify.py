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

""" angr_function_id.py
        Module to identitfy statically linked functions in binaries using angr.
"""
import logging
import time
import angr

from oxide.core.libraries.angr_utils import init_angr_project

logger = logging.getLogger("angr_function_id")


def extract(file_test, header):
    """ Traverse basic block graph from fst angr, and save basic block offsets as well
            as instruction metrics
        Input -
            file_test - input file to be analyzed by tool
        Output -
            output_map - dictionary of instructions and basic blocks from angr
    """
    output_map = {"meta": {}, "static_link_functions": {}}
    start = time.time()

    project = init_angr_project(file_test, header)
    try:
        idfer = project.analyses.Identifier()
        end = time.time()
        for fun_info in idfer.func_info:
            addr = header.get_offset(fun_info.addr) if not REBASE_OFF else fun_info.addr
            output_map["static_link_functions"][addr] = fun_info.name
        output_map["meta"]["time"] = end - start
    except AttributeError as err:
        logger.info("AttributeError: angr_function_id %s", err)
        output_map = None
    return output_map
