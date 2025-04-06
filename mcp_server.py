# Oxide MCP Server
#
# Add the "oxide" dictionary in the JSON snippet below to the servers JSON file
# that you configure in your chosen MCP Client.
#   {
#     "mcpServers": {
#       "oxide": {
#         "command": "python",
#         "args": [
#           "<YOUR PATH TO OXIDE>/oxide/mcp_server.py",
#           "--oxidepath=<YOUR PATH TO OXIDE>/"
#         ]
#       }
#     }
#   }
#
# If you are using mcp-cli you can use this command line to test the MCP server
# without involving any LLM calls:
# > mcp-cli cmd --config-file <PATH TO YOUR SERVERS JSON FILE> --server oxide --tool file_stats --tool-args '{"oid" : "6c4c20fb54c83c6283b9085dfd6725ceb6dd8eee"}'
# NOTE: replace the OID with one from a binary file in your own collections
#
# To run mcp-cli in an interactive chat, you can use this command line:
# > mcp-cli chat --config-file <PATH TO YOUR SERVERS JSON FILE> --server oxide --provider openai --model gpt-4o-mini
# NOTE: Depending on the provider and model, ensure your API keys are set in the environment or whatever is needed.

# DGB NOTE: I added complicated code below to import Oxide instead of this simple import statement.
# It parses the command line to learn the desired Oxide path and internally modifies the Python path.
# Too clunky? You'd rather modify the PYTHON_PATH OS environment variable? Or maybe there is
# an even smarter way to do this? Then PLEASE improve this code and document it. But until then
# it won't work (for just me?) without my clunky code.
# from oxide.core import oxide as oxide

import logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("oxide mcp server")
from mcp.server.fastmcp import FastMCP
from typing import Any, Literal
import argparse
import sys

# Parse command line args
parser = argparse.ArgumentParser('oxide MCP server')
parser.add_argument("--oxidepath", type=str, help="Path to active Oxide installation.", required=False, default="./")
parser.add_argument("--caparulespath", type=str, help="Path to Capa rules files.", required=False, default="./datasets/capa-rules/")
args = parser.parse_args()
print(f'oxide path: {args.oxidepath}')
print(f'capa rules path: {args.caparulespath}')

# Import Oxide 
sys.path.append(args.oxidepath+'/src')
sys.path.append(args.oxidepath+'/src/oxide')
from oxide.core import oxide as oxide


mcp = FastMCP("oxide")

@mcp.tool()
async def disasm(oid: str) -> dict[Any,Any] | Literal[False]:
    """
    Retrieve a dictionary of disassembly for an OID.
    Keys in the dictionary which refer to addresses in the binary are typically file offset and not vaddr
    Values in the disassembly may use vaddr that isn't translated to file offset.

    Args:
    oid: the object id of the binary we are interested in
    """
    result = oxide.retrieve("disassembly", [oid])
    if result:
        logger.info("Retrieved disassembly successfully!")
        return result
    else:
        logger.error("Failed to retrieve disassembly")
        return False

@mcp.tool()
async def function_summary(oid: str) -> dict[Any,Any] | Literal[False]:
    """
    Retrieve a dictionary of summaries of functions listed by function
    Keys in the dictionary which refer to addresses in the binary are typically file offset and not vaddr

    Args:
    oid: the object id of the binary we are interested in
    """
    result = oxide.retrieve("function_summary", [oid])
    if result:
        logger.info("Retrieved summary successfully!")
        return result
    else:
        logger.error("Failed to retrieve summary")
        return False

@mcp.tool()
async def file_stats(oid: str) -> dict[Any,Any] | Literal[False]:
    """
    Get general file stats
    
    This module returns a dictionary containing the statistics for each binary file in the collection by their individual oid.
    The dictionary includes the number of basic blocks, the number of functions, the number of sections, whether or not the
    RTTI is present and if present, the section names.

    Args:
    oid: the object id of the binary we are interested in
    """
    result = oxide.retrieve("file_stats", [oid])
    if result:
        logger.info("Retrieved file stats successfully!")
        return result
    else:
        logger.error("Failed to retrieve file stats")
        return False

@mcp.tool()
async def ghidra_decmap(oid:str, org_by_func: bool) -> dict[Any,Any] | Literal[False]:
    """
    Get ghidra decompilation mapping, optionally organized by function.
    Keys in the dictionary which refer to addresses in the binary are typically file offset and not vaddr

    Args:
    oid: the object id of the binary we are interested in
    org_by_func: boolean of whether or not to organize the results by function
    """
    result = oxide.retrieve("ghidra_decmap", [oid], {"org_by_func": org_by_func})
    if result:
        logger.info("Retrieved ghidra decompilation mapping successfully!")
        return result
    else:
        logger.error("Failed to retrieve ghidra decompilation mapping")
        return False

@mcp.tool()
async def get_oids() -> dict[Any,Any] | Literal[False]:
    """
    Given a name, be able to get an OID back which corresponds to the name

    Args:
    No args
    """
    result = oxide.get_oids_with_name("test")
    if result:
        logger.info("Got oids with names")
        return result
    else:
        logger.error(f"Couldn't get oids and names")
        return False
    
if __name__ == "__main__":
    mcp.run(transport="stdio")
