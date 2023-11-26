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

DESC = " Find collocations in the opcodes list"
NAME = "opcode_collocations"
USG = "This module returns a dictionary containing information about the collocations in the opcode listfound in each binary within the \
collection. Each collocation is represented as a pair of opcodes and their corresponding score, which indicates the significance of the \
collocation "

import logging

import api

from collocations import collocations

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"ngrams": {"type": int, "mangle": True, "default": 2},
            "num_ngrams": {"type": int, "mangle": True, "default": 20}}


USAGE = "run opcode_collocations --ngrams N --num_ngrams N"


def documentation():
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False, "atomic": True, "usage": USAGE}


def process(oid, opts):
    logger.debug("process()")

    opcode_histogram = api.retrieve("opcode_histogram", oid, {})
    opcode_ngrams = api.retrieve("opcode_ngrams", oid, {"n": opts["ngrams"]})
    if not opcode_histogram or not opcode_ngrams:
        return False
    colls = collocations(opcode_histogram, opcode_ngrams, "num_ngrams")
    api.store(NAME, oid, colls, opts)
    return True
