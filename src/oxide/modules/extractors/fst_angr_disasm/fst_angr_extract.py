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

import angr

from oxide.core.libraries.angr_utils import init_angr_project, process_cfg


def extract(file_test, header):
    """ Traverse basic block graph from fst angr, and save basic block offsets as well
            as instruction metrics
        Input -
            file_test - input file to be analyzed by tool
        Output -
            output_map - dictionary of instructions and basic blocks from angr
    """
    start = time.time()

    try:
        p = init_angr_project(file_test, header)
        cfg = p.analyses.CFGFast(normalize=True)
        output_map = process_cfg(cfg, header)
    except ValueError:
        # TODO:: which error is the normalize on wrong for
        try:
            cfg = p.analyses.CFGFast()
        except ValueError:
            logging.info("angr (fast cfg) failed to run analysis on binary")
            traceback.print_exc()
            return None
    except cle.errors.CLECompatibilityError:
        logging.info("angr (fast cfg), cle memory error loading binary")
        return None
    except angr.errors.SimProcedureError:
        logging.info("angr (fast cfg), sim procedure error")
        return None
    except angr.errors.AngrExitError:
        logging.info("angr (fast cfg), Likely failure to execute jumpkind while computing CFG")
        return None
    if output_map is None: return None

    end = time.time()
    output_map["meta"]["time"] = end - start

    return output_map
