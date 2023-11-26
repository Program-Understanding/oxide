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

""" For all major catagories of findings from oxide modules about a file
    break down where known bytes are.

    e.g. elf header + ghidra disassembly + ghidra data + padding = N% known
"""

import api
import json

class module_organizer:
    elf = None
    pe = None
    ghidra_disasm = None
    ghidra_data = None
    dwarf_info = None
    rtti = None
    bin_size = None
    data = None
    disasm = None
    coverage = None
    padding = None
    oid = None

    def __init__(self, modules):
        if modules["elf"] is not None:
            self.elf = modules["elf"]
        if modules["pe"] is not None:
            self.pe = modules["pe"]
        if modules["ghidra_data"] is not None:
            self.ghidra_data = modules["ghidra_data"]
        if modules["dwarf_info"] is not None:
            self.dwarf_info = modules["dwarf_info"]
        if modules["rtti"] is not None:
            self.rtti = modules["rtti"]
        if modules["bin_size"] is not None:
            self.bin_size = modules["bin_size"]
        if modules["disasm"] is not None:
            self.disasm = modules["disasm"]
        if modules["data"] is not None:
            self.data = modules["data"]
        if modules["padding"] is not None:
            self.padding = modules["padding"]
        if modules["oid"] is not None:
            self.oid = modules["oid"]

    def get_coverage(self):
        '''  This function finds how much the binary is being covered by analysis modules. It stores binary coverage and calculates percentage covered inside a dictionary object coverage.
        '''
        coverage = {}
        total_bytes_covered = 0

        # Offsets covered without overlap is a way to keept track of all of the binary's covered offsets across all used modules excluding offsets that are covered more than once by another module
        offsets_covered_without_overlap = []

        # PE (Header related bytes module:pe)
        if self.pe is not None:
            coverage["pe"] = {}
            coverage["pe"]["coverage"] = {}

            offsets = self.pe["offsets"]

            #Implicit offsets are offsets that are within other offsets meaning the same bytes are being covered as multiple pieces of information, data, instructions, or etc. Implicit offsets are removed from consideration to get more accurate binary coverage.
            implicit_offsets=[]

            for p in offsets:
                coverage["pe"]["coverage"][p] = offsets[p][0]

                if p in implicit_offsets:
                    continue

                x=1

                while len(list(offsets.keys()))-1 > list(offsets.keys()).index(p)+x and p+offsets[p][0]["len"] > list(offsets.keys())[list(offsets.keys()).index(p)+x]:
                    implicit_offsets.append(list(offsets.keys())[list(offsets.keys()).index(p)+1])
                    x=x+1
                total_bytes_covered = total_bytes_covered + int(offsets[p][0]["len"])
                offsets_covered_without_overlap.append((p, int(offsets[p][0]["len"])))

            coverage["pe"]["total_bytes_covered"] = total_bytes_covered
            coverage["pe"]["percent_covered"] = total_bytes_covered / self.bin_size

        total_bytes_covered = 0

        # Disasm (instruction related bytes, module:ghidra_disasm)
        if self.disasm:
            coverage["disasm"] = {}
            coverage["disasm"]["coverage"] = {}

            # don't count me toward the total bytes / overlap list
            implicit_offsets = []

            coverage["disasm"]["coverage"] = self.disasm["instructions"]

            offsets = coverage["disasm"]["coverage"]

            for instr in coverage["disasm"]["coverage"]:

                #------------------
                if instr in implicit_offsets:
                    continue

                x=1
                while len(list(offsets.keys()))-1 > list(offsets.keys()).index(instr)+x and instr+offsets[instr]["size"] > list(offsets.keys())[list(offsets.keys()).index(instr)+x]:
                    implicit_offsets.append(list(offsets.keys())[list(offsets.keys()).index(instr)+1])
                    x += 1
                offsets_covered_without_overlap.append((instr, int(offsets[instr]["size"])))

                #------------------

                total_bytes_covered = total_bytes_covered + offsets[instr]["size"]

                overlap = 0

                for offset in offsets_covered_without_overlap:
                    if (offset[0] < instr and (offset[0] + offset[1]) > instr) or offset[0] == instr: # If it does exist
                        overlap=1
                        break

                if overlap == 0:
                    offsets_covered_without_overlap.append((instr, self.disasm["instructions"][instr]["size"]))

            coverage["disasm"]["total_bytes_covered"] = total_bytes_covered

            coverage["disasm"]["percent_covered"] = total_bytes_covered / self.bin_size

        total_bytes_covered = 0

        # Ghidra Data (global data, module:ghidra_data)
        if self.ghidra_data is not None:
            coverage["ghidra_global_data"] = {}
            coverage["ghidra_global_data"]["coverage"] = {}

            d = self.ghidra_data

            implicit_offsets=[]

            for code in d["global_data"]:

                if code in implicit_offsets:
                     continue

                x=1

                while len(list(d["global_data"].keys()))-1 > list(d["global_data"].keys()).index(code)+x and code+d["global_data"][code]["size"] > list(d["global_data"].keys())[list(d["global_data"].keys()).index(code)+x]:
                    implicit_offsets.append(list(d["global_data"].keys())[list(d["global_data"].keys()).index(code)+1])
                    x=x+1

                total_bytes_covered = total_bytes_covered + int(d["global_data"][code]["size"])
                offsets_covered_without_overlap.append((p, int(d["global_data"][code]["size"])))

                coverage["ghidra_global_data"]["coverage"][code] = d["global_data"][code]["type"]
                overlap = 0

                for offset in offsets_covered_without_overlap:

                    if (offset[0] < code and (offset[0] + offset[1]) > code) or offset[0] == code:
                        overlap=1
                        break

                if overlap == 0:
                    offsets_covered_without_overlap.append((code, d["global_data"][code]["size"]))

            coverage["ghidra_global_data"]["total_bytes_covered"] = total_bytes_covered

            coverage["ghidra_global_data"]["percent_covered"] = total_bytes_covered / self.bin_size

        #Padding (sequences of 0s module:padding)
        coverage["padding"] = {}

        coverage["padding"]["total_padding"] = 0

        padding_no_overlap = 0

        for p in self.padding[self.oid]:
            coverage["padding"]["total_padding"] = coverage["padding"]["total_padding"] + self.padding[self.oid][p]["count"]

            if p in implicit_offsets:
                continue

            x=1

            while len(list(self.padding[self.oid].keys()))-1 > list(self.padding[self.oid].keys()).index(p)+x and p+self.padding[self.oid][p]["count"] > list(self.padding[self.oid].keys())[list(self.padding[self.oid].keys()).index(p)+x]:
                implicit_offsets.append(list(self.padding[self.oid].keys())[list(self.padding[self.oid].keys()).index(p)+1])
                x=x+1
            total_bytes_covered = total_bytes_covered + int(self.padding[self.oid][p]["count"])
            offsets_covered_without_overlap.append((p, int(self.padding[self.oid][p]["count"])))
            overlap = 0

            for offset in offsets_covered_without_overlap:
                if (offset[0] < p and (offset[0] + offset[1]) > p) or offset[0] == p:
                    overlap=1
                    break

            if overlap == 0:
                offsets_covered_without_overlap.append((p, self.padding[self.oid][p]["count"]))
                padding_no_overlap = padding_no_overlap+self.padding[self.oid][p]["count"]

        coverage["padding"]["percent_covered"] = coverage["padding"]["total_padding"] / self.bin_size

        coverage["padding"]["bin_size_no_padding"] = self.bin_size-coverage["padding"]["total_padding"]

        # The remainder is massasaging numbers in ways that may be worth showing a user
        # e.g. detecting if instructions overlap, or data and instructions, or large grouping of bytes which may mislead understanding

        #Module coverage no padding
        total_percent_no_padding = 0
        for c in coverage:
            if "total_bytes_covered" in coverage[c].keys():
                coverage[c]["percent_covered_with_binary_size_not_including_padding"] = str(coverage[c]["total_bytes_covered"] / coverage["padding"]["bin_size_no_padding"])
                total_percent_no_padding = total_percent_no_padding + coverage[c]["total_bytes_covered"] / coverage["padding"]["bin_size_no_padding"]

        #Overall
        overall=0
        for c in coverage:
            overall = overall+coverage[c]["percent_covered"]
        overall = overall - coverage["padding"]["percent_covered"]
        coverage["overall"] = {}
        coverage["overall"]["percent_covered"] = overall
        coverage["overall"]["binary_size"] = self.bin_size
        coverage["overall"]["binary_size_excluding_padding"] = coverage["padding"]["bin_size_no_padding"]

        for c in coverage:
            if "percent_covered_no_padding" in coverage[c].keys():
                coverage["overall"]["percent_covered_sum_no_padding"] = coverage["overall"]["percent_covered_sum_no_padding"] + coverage[c]["percent_covered_no_padding"]

        coverage["overall"]["percent_covered_with_padding"] = str(coverage["padding"]["percent_covered"] + coverage["overall"]["percent_covered"])
        coverage["overall"]["percent_covered_without_padding"] = str(total_percent_no_padding)

        #No Overlap
        coverage["no_overlap"] = {}

        offsets_covered_without_overlap.sort(key=lambda y: y[0])

        coverage["no_overlap"]["offsets"] = offsets_covered_without_overlap
        coverage["no_overlap"]["total_bytes"] = 0
        for o in offsets_covered_without_overlap:
            coverage["no_overlap"]["total_bytes"] = o[1] + coverage["no_overlap"]["total_bytes"]

        coverage["no_overlap"]["total_bytes_no_padding"] = coverage["no_overlap"]["total_bytes"] - coverage["padding"]["total_padding"]

        #Dark Zones
        #Offsets of the binary that aren't covered by any module.
        #This needs to be fixed because currently some dark zone offsets have negative lengths.

        num_dark_bytes = 0
        d_offsets = []
        coverage["dark_zones"] = {}
        coverage["dark_zones"]["percent_covered_with_padding"] =1.0 - float(coverage["overall"]["percent_covered_with_padding"])
        coverage["dark_zones"]["percent_covered_without_padding"] =1.0 - float(coverage["overall"]["percent_covered_without_padding"])

        nooverlap_offsets = offsets_covered_without_overlap

        # subtract this offset from next one to find missing gaps
        for data_offset, data_len in nooverlap_offsets[:-1]:
            # 3 cases:
            #    A + len = B difference: 0
            #    B > A + len difference: +
            #    A < B < A+len difference: -
            next_nooverlap_offset, _  = nooverlap_offsets[nooverlap_offsets.index((data_offset, data_len))+1]
            if data_offset >= 0:
                if (data_offset + data_len) == next_nooverlap_offset:
                    # no dark zone, as next entry starts at our end
                    continue
                # next index start is either inside or beyond our end
                num_dark_bytes = num_dark_bytes + (next_nooverlap_offset - (data_offset + data_len))
                d_offsets.append((data_offset+data_len, (data_offset + data_len) - next_nooverlap_offset))

        coverage["dark_zones"]["offsets"] = d_offsets
        coverage["dark_zones"]["num_dark_bytes"] = num_dark_bytes

        self.coverage = coverage
        return coverage

    def json_output(self, coverage):
        '''
            Creates a .json file out of the coverage object returned by get_coverage above.
        '''
        print("Outputting JSON file coverage.json...")

        if 'disasm' in coverage:
            for c in coverage["disasm"]["coverage"]:
                coverage["disasm"]["coverage"][c]["bytes"] = None

        with open("coverage.json","w") as coverage_file:
            json.dump(coverage, coverage_file, indent=4)


def assemble(modules):
    '''
        Creates a module_organizer object which contains the module objects returned by each modudle analyzing the binary. Get_coverage is called on the module_organizer object to get the coverage of the binary. Then the resulting coverage dictionary is outputted to a json file. The module_organizer object is returned to bin_coverage's module_interface.py
    '''
    data = module_organizer(modules)
    coverage = data.get_coverage()
    data.json_output(coverage)

    return data
