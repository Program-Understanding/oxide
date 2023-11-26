#Get mapping of decompiler statements to lines of assembly
#@author N/A
#@category selection
#@keybinding Alt-d
#@menupath Select.Program Highlight.Decompiler
#@toolbar cache.png
from __future__ import unicode_literals

from ghidra.program.model.address import Address
from ghidra.program.model.listing.CodeUnit import *
from ghidra.program.model.listing.Listing import *
from ghidra.framework.plugintool import PluginTool # access plugin tool
from ghidra.app.plugin.core.colorizer import ColorizingService
from ghidra.app.decompiler import DecompInterface
from ghidra.app.decompiler.component import DecompilerUtils

import sys
import os
import json
import string

printable = string.ascii_letters + string.digits + string.punctuation + ' '
def hex_escape(s):
    return ''.join(c if c in printable else r'\x{0:02x}'.format(ord(c)) for c in s)

#get ghidra root directory
ghidra_default_dir = os.getcwd()

#get ghidra jython directory
jython_dir = os.path.join(ghidra_default_dir, "Ghidra", "Features", "Python", "lib", "Lib", "site-packages")

#insert jython directory into system path
sys.path.insert(0,jython_dir)

OUTFILE = open(getScriptArgs()[0], "w")

decomp = DecompInterface()
decomp.openProgram(currentProgram)
functionManager = currentProgram.getFunctionManager()

output_map = {'meta': {}}

output_map['meta']['load_addr'] = str(currentProgram.getImageBase())

def remove_duplicates(lst):
    return list(dict.fromkeys(lst).keys())

for fun in functionManager.getFunctions(True):
    # iterate in entry point order
    funEntry = fun.getEntryPoint()
    function = functionManager.getFunctionContaining(funEntry)

    results = decomp.decompileFunction(function, 120, monitor)
    markup = results.getCCodeMarkup()
    highfun = markup.getHighFunction()
    clang = markup.getClangFunction()

    # Iterate over lines of source
    for line in DecompilerUtils.toLines(markup):
        unicode_line = hex_escape(line.toString())
        if len(unicode_line) > 30 and "WARNING:" in unicode_line[:30]:
            continue

        tokens = line.allTokens
        for tok_in_line in tokens:
            minAddr = str(tok_in_line.getMinAddress())
            maxAddr = str(tok_in_line.getMaxAddress())

             # Some tokens in C do not correspond to an address such as '('
            if minAddr is None:
                continue
            # Several source lines map to 1 line of assembly
            if minAddr not in output_map:
                output_map[minAddr] = {}

            if 'line' in output_map[minAddr] and unicode_line not in output_map[minAddr]['line']:
                output_map[minAddr]['line'].append(unicode_line)
            else:
                output_map[minAddr]['line'] = [unicode_line]

            if 'tokens' in output_map[minAddr]:
                output_map[minAddr]['tokens'].append(hex_escape(tok_in_line.toString()))
            else:
                output_map[minAddr]['tokens'] = [hex_escape(tok_in_line.toString())]


print(output_map)
# Some instructions do not map to anything, including anything in prologue of function
json.dump(output_map, OUTFILE)