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


from math import log

from typing import List


def collocations(opcode_histo, bigrams: List[str], num_bigrams: int = 20):
    total_opcodes = 0
    colls = set()
    for opcode in opcode_histo:
        total_opcodes += opcode_histo[opcode]

    total_bigrams = 0
    for bigram in bigrams:
        total_bigrams += bigrams[bigram]

    high_bigrams = []
    for bigram in bigrams:
        if bigram not in colls:
            mutual_info = 0
            b = bigram.split(",")
            prob_xy = float(bigrams[bigram]) / total_bigrams
            prob_x = float(opcode_histo[b[0]]) / total_opcodes
            prob_y = float(opcode_histo[b[1]]) / total_opcodes
            if not prob_x or not prob_y: continue
            mutual_info = prob_xy * log(prob_xy / (prob_x * prob_y))
            colls.add(bigram)
            high_bigrams.append((mutual_info, bigram))
    high_bigrams.sort(reverse=True)
    return {"collocations": high_bigrams[:20]}
