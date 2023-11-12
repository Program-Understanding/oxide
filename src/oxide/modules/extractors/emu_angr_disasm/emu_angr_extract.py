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
import traceback
import cle

from oxide.core.libraries.angr_utils import init_angr_project, process_cfg


def extract(file_test, header):
    """ Traverse basic block graph from angr, and save basic block offsets as well
            as instruction metrics
        Input -
            cfg (angr cfg object) - object containing subprocess* graphs
            p (angr project) - project to initialize analysis
            header_interface (header object) - object that defines object file parameters
            folder (string) - name of sample folder in output directory
        Output -
            inst_to_save (list of tuples) - list containing instructions metrics
                (offset, mnemonics, bb parent, vex?)
    """

    start = time.time()
    try:
        p = init_angr_project(file_test, header)
        cfg = p.analyses.CFGEmulated(normalize=True)
        output_map = process_cfg(cfg, header)
    except StopIteration:
        # TODO:: unclear where this comes from
        try:
            cfg = p.analyses.CFGEmulated()
            output_map = process_cfg(cfg, header)
        except StopIteration:
            logging.error("Emulated angr failed analysis on binary")
            traceback.print_exc()
            return None
    except cle.errors.CLECompatibilityError:
        logging.error("Fst angr cle memory error loading binary")
        return None
    end = time.time()
    output_map["meta"]["time"] = end - start

    return output_map
