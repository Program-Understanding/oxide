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

from oxide.core.libraries import histogram

from typing import Optional


def score_packed(file_meta: dict, execute_sections: int, rwx_sections: int,
                 num_bad_ss: int, num_nonstandard: int) -> int:
    prob_packed = 0
    if not file_meta.imports:
        prob_packed += 1

    elif len(file_meta.imports) < 10:
        prob_packed += 1

    if execute_sections > 1:
        prob_packed += 1

    if execute_sections == 0:
        prob_packed += 1

    if rwx_sections > 0:
        prob_packed += 5

    if num_bad_ss > 0:
        prob_packed += 99

    if num_nonstandard > 0:
        prob_packed += 1

    return prob_packed


def detect_packer(file_meta: dict, data: bytes) -> Optional[dict]:
    """   based on likely behavior of PE including number of sections
        percent of these executable and writable.
    """
    prob_packed = 0

    # Determining number of standard and non-standard section names
    ss_names = set(['.text', '.code', '.data', '.rdata', '.idata', '.edata', '.pdata',
                    '.xdata', '.reloc', '.bss', '.rsrc', '.crt', '.tls', '.orpc', '.INIT',
                    ',data1'])

    bad_ss_names = set(['.UPX0', '.UPX1', '.UPX2', '.aspack', '.asdata', '.packed', '.RLPack',
                        'Themida', '.ndata', '.Upack', '.perplex', '.pelock', '.Wpack',
                        'PEinject', 'PEPACK!!', '.petite', '.pack32'])

    my_sections = set()

    # shouldn't really have any of these
    rwx_sections = 0

    # should only really have one of these
    execute_sections = 0

    # Should be high
    num_imports = 0

    num_bad_ss = 0
    num_sections = 0
    exec_sect_entropy = set()
    sections = getattr(file_meta, 'section_info', None)
    if sections is None:
        return None

    for section in sections:
        flags = sections[section]['flags']

        if 'MEM_READ' in flags and 'MEM_WRITE' in flags and 'MEM_EXECUTE' in flags:
            rwx_sections = rwx_sections + 1

        if 'MEM_EXECUTE' in flags:
            execute_sections = execute_sections + 1
            offset = sections[section]["section_offset"]
            size = sections[section]["section_len"]

            section_data = data[offset: offset + size]
            entrop = histogram.calc_entropy(section_data)
            exec_sect_entropy.add((section, entrop))
            if entrop > .9:
                prob_packed = prob_packed + 1

        my_sections.add(str(section).strip("\x00"))
        num_sections = num_sections + 1

    num_sections = len(my_sections)
    num_nonstandard = len(my_sections.difference(ss_names))
    num_standard = len(my_sections.intersection(ss_names))
    num_bad = len(my_sections.intersection(bad_ss_names))

    # all meta scores to entropy clues
    prob_packed += score_packed(file_meta, execute_sections, rwx_sections, num_bad_ss, num_nonstandard)

    # if more than six hints, likely packed, threshold is arbitrary
    # TODO:: change treshold to be an argument/option
    return {'likely_packed': (prob_packed > 6), 'num_standard_sect_names': num_standard,
            'num_known_bad_sect_names': num_bad_ss,
            'num_nonstandard_sect_names': num_nonstandard, 'num_rwx_sects': rwx_sections,
            'num_exec_sections': execute_sections, 'num_imports': num_imports,
            'num_bad_sections': num_bad, 'executable_sect_entropy': exec_sect_entropy}
