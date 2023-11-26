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

DESC = " Compute cyclomatic complexity for functions within executable using Ghidra"
NAME = "cyclo_complexity"
USG = "This module returns a dictionary with cyclomatic complexity for functions within each binary file. It shows the complexity levels \
and complexity scores that both measure the complexity of each function."

import logging
import api
from networkx import DiGraph, strongly_connected_components

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

def documentation():
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage": USG}


def process(oid, opts):
    logger.debug("process()")
    logger.info('TODO:: replace with pure python')
    blocks = api.get_field("ghidra_disasm", [oid], "original_blocks")
    functions = api.get_field("ghidra_disasm", [oid], "functions")
    results = {}

    if not blocks or not functions:
        return False

    for func in functions:
        E = 0  # Edges
        N = 0  # Nodes/Blocks
        P = 0  # Components

        func_graph = DiGraph()
        logger.debug(func)
        N = len(functions[func]['blocks'])
        for block in functions[func]['blocks']:
            func_graph.add_node(block)
            try:
                for edge in blocks[block]['dests']:
                    # Non-interprocedural
                    if edge in functions[func]['blocks']:
                        func_graph.add_edge(block, edge)
                    E += 1
            except KeyError:
                continue
        for component in strongly_connected_components(func_graph):
            P += 1

        cyclo = E - N + 2*P
        logger.debug('[+] Complexity: Edges (%s) - Nodes(%s) + 2*Components(%s): %s', E, N, P, cyclo)
        complexity = None
        if cyclo < 11:
            logger.debug('[-] Simple function')
            complexity = 'simple'
        elif cyclo < 21:
            logger.debug('[-] Moderately complex function')
            complexity = 'moderate'
        elif cyclo < 51:
            logger.debug('[-] Complex function')
            complexity = 'complex'
        else:
            logger.debug('[-] Untestable function')
            complexity = 'needs refactor'

        results[func] = {'name': functions[func]['name'], 'complexity': cyclo, 'desc': complexity}

    api.store(NAME, oid, results, opts)
    return True
