# Get mapping of decompiler statements to lines of assembly
# @author N/A
# @category selection
# @keybinding Alt-d
# @menupath Select.Program Highlight.Decompiler
# @toolbar cache.png
from __future__ import unicode_literals

from ghidra.program.model.address import Address
from ghidra.program.model.listing.CodeUnit import *
from ghidra.program.model.listing.Listing import *
from ghidra.framework.plugintool import PluginTool  # access plugin tool
from ghidra.app.plugin.core.colorizer import ColorizingService
from ghidra.app.decompiler import DecompInterface
from ghidra.app.decompiler.component import DecompilerUtils

import sys
import os
import json
import string
import codecs
import traceback

printable = string.ascii_letters + string.digits + string.punctuation + " "


def hex_escape(s):
    return "".join(c if c in printable else r"\x{0:02x}".format(ord(c)) for c in s)


# get ghidra root directory
ghidra_default_dir = os.getcwd()

# get ghidra jython directory
jython_dir = os.path.join(
    ghidra_default_dir,
    "Ghidra",
    "Features",
    "Python",
    "lib",
    "Lib",
    "site-packages",
)

# insert jython directory into system path
sys.path.insert(0, jython_dir)


def build_mapping():
    decomp = DecompInterface()
    decomp.openProgram(currentProgram)
    functionManager = currentProgram.getFunctionManager()

    output_map = {
        "meta": {
            "load_addr": str(currentProgram.getImageBase()),
            # optional: per-function metadata (not used by extract(), but handy)
            "functions": {},
        }
    }

    for fun in functionManager.getFunctions(True):
        # Iterate in entry-point order
        funEntry = fun.getEntryPoint()
        function = functionManager.getFunctionContaining(funEntry)
        if function is None:
            continue

        # Use fully-qualified name to distinguish Lexer::getObj(int) from Parser::getObj(int)
        func_name = function.getName(True)

        # Set up structure for this function if needed
        if func_name not in output_map:
            output_map[func_name] = {}
            # store metadata under meta, NOT under the function dict
            output_map["meta"]["functions"][func_name] = {"entry": str(funEntry)}

        try:
            results = decomp.decompileFunction(function, 120, monitor)
            if not results or not results.decompileCompleted():
                # skip functions that failed to decompile
                continue
            markup = results.getCCodeMarkup()
            if markup is None:
                continue

            # Not strictly needed, but kept from original script
            highfun = markup.getHighFunction()
            clang = markup.getClangFunction()

            # Iterate over lines of source (add a stable line index for downstream ordering)
            for i, line in enumerate(DecompilerUtils.toLines(markup), start=1):
                unicode_line = hex_escape(line.toString())
                if len(unicode_line) > 30 and "WARNING:" in unicode_line[:30]:
                    continue

                # Prefix with an index so downstream can parse "NNN: <code>"
                tagged_line = "%d: %s" % (i, unicode_line)

                # Track whether we associated this source line with any address
                lineAdded = False

                # Tokens on this source line (may be missing depending on Ghidra/Jython object)
                tokens = getattr(line, "allTokens", None) or []

                for tok_in_line in tokens:
                    min_addr_obj = tok_in_line.getMinAddress()

                    # Some tokens in C do not correspond to an address such as '('
                    if min_addr_obj is None:
                        continue

                    minAddr = str(min_addr_obj)  # e.g., "0010c15a"

                    # Ensure per-address dict exists
                    entry = output_map[func_name].setdefault(minAddr, {})

                    # Add source line (avoid duplicates)
                    lines_list = entry.setdefault("line", [])
                    if tagged_line not in lines_list:
                        lines_list.append(tagged_line)

                    # Add token text (optionally dedupe if you want)
                    tok_str = hex_escape(tok_in_line.toString())
                    entry.setdefault("tokens", []).append(tok_str)

                    lineAdded = True

                # If no token on this line mapped to an address, store under "None"
                if not lineAdded:
                    entry = output_map[func_name].setdefault("None", {})
                    lines_list = entry.setdefault("line", [])
                    if tagged_line not in lines_list:
                        lines_list.append(tagged_line)


        except Exception as e:
            # Log which function blew up, but keep going
            print("decompile_mapping.py: ERROR in function %s: %s" % (func_name, e))
            traceback.print_exc()

            # Track failed functions in meta for debugging
            failed = output_map["meta"].get("failed_functions")
            if failed is None:
                output_map["meta"]["failed_functions"] = [func_name]
            elif func_name not in failed:
                failed.append(func_name)

            continue

    return output_map


def main():
    args = getScriptArgs()
    print("decompile_mapping.py: args = %r" % (args,))

    if not args:
        raise RuntimeError("No output path argument provided")

    out_path = args[0]
    out_dir = os.path.dirname(out_path)
    if out_dir and not os.path.isdir(out_dir):
        os.makedirs(out_dir)

    try:
        mapping = build_mapping()
    except Exception as e:
        # If *something* unexpected happens at the top level, still emit a file
        print("decompile_mapping.py: ERROR while building mapping: %s" % e)
        traceback.print_exc()
        mapping = {
            "meta": {
                "error": str(e),
                "exception_type": e.__class__.__name__,
            }
        }

    print("decompile_mapping.py: writing JSON to %s" % out_path)
    f = open(out_path, "w")
    try:
        # Some instructions do not map to anything, including anything in prologue of function
        json.dump(mapping, f)
    finally:
        f.close()


# Run immediately when invoked by Ghidra/headless
main()
