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

import json
import time
import logging

try:
    import r2pipe
except OSError:
    raise Exception("r2 pipe on shared library")

from typing import Optional

NAME = "radare_linear_extract"
logger = logging.getLogger(NAME)

# ------------------------------- Tool 2: Radare -------------------------------------


def extract(file_test: str, header) -> Optional[dict]:
    """processes an exectuable with radare2/r2pipe, and disassembles code
        input -
                file_test (filename)- exectuable x86,64 parsable with radare2/r2pipe
    """
    start = time.time()

    try:
        r2 = r2pipe.open(file_test, flags=["-2"])
    except Exception:  # Radare does not use custom exception
        return {}

    # cfg is json output of control flow graph
    output_map = {}
    output_map["meta"] = {}
    output_map["instructions"] = {}
    output_map["original_blocks"] = {}
    output_map["canon_blocks"] = {}

    if not header.known_format:
        logging.info("File Sample is of unknown format, IDA returning empty output.")
        return None

    # Special argument giving offset to text section and text section size
    output = r2.cmd("pDj $SS @ $S")
    try:
        output = json.loads(output)
    except json.JSONDecodeError:
        logger.info("Radare linear json decoding fail")
        return None

    if output is None:
        # Radare produced no output
        return None

    for insn in output:
        # No need to bound check as pD prints bytes, and uses start of section with entry point
        if 'disasm' not in insn:
            logger.debug("No assembly found in insn at %s, type: %s", insn['offset'], insn['type'])
            continue
        output_map['instructions'][header.get_offset(insn['offset'])] = insn['disasm']

    end = time.time()
    output_map["meta"]["time"] = end - start

    # Offsets Obtained
    return output_map
