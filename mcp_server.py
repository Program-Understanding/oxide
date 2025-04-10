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
import json
import networkx as nx
from networkx.readwrite import json_graph

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

# Commented out because it didn't look finished yet (e.g., no input args, "test")
# @mcp.tool()
# async def get_oids() -> dict[Any,Any] | Literal[False]:
#     """
#     Given a name, be able to get an OID back which corresponds to the name
#
#     Args:
#     No args
#     """
#     result = oxide.get_oids_with_name("test")
#     if result:
#         logger.info("Got oids with names")
#         return result
#     else:
#         logger.error(f"Couldn't get oids and names")
#         return False

@mcp.tool()
async def get_function_offset(oid: str, function_names: list[str]) -> dict[Any, Any] | Literal[False]:
    """
    Retrieve the offsets for specific functions in a binary.

    **Inputs:**
      - oid (str): The object ID of the binary to be analyzed.
      - function_names (list[str]): A list of function names for which the offsets should be retrieved.

    **Returns:**
      - dict: A JSON-compatible dictionary mapping each function name (from the input list) to its corresponding offset,
              as obtained from the function summary. For example, if "my_function" has an offset of 4096, an entry would be:
              { "my_function": 4096 }.
      - Literal[False]: Returns False if the function summary cannot be retrieved.

    Example:
      Given a binary with a function summary where "my_function" has an offset 4096 and "another_function" has an offset 8192,
      calling:
      
          await get_function_offset("binary_oid", ["my_function", "another_function"])
      
      would return:
      
          {
              "my_function": 4096,
              "another_function": 8192
          }
    """
    result = oxide.retrieve("function_summary", [oid])
    if result:
        logger.info("Retrieved summary successfully!")
        summary = result[oid]
        mapping = {}
        for function_name in function_names:
            if function_name in summary:
                mapping[function_name] = summary[function_name]['offset']
        return mapping
    else:
        logger.error("Failed to retrieve summary")
        return False


@mcp.tool()
async def get_function_name(oid: str, function_offsets: list[int]) -> dict[Any, Any] | Literal[False]:
    """
    Retrieve the function names corresponding to the specified function offsets.

    **Inputs:**
      - oid (str): The object ID of the binary to be analyzed.
      - function_offsets (list[int]): A list of function offsets for which the corresponding function names should be retrieved.

    **Returns:**
      - dict: A JSON-compatible dictionary mapping each function offset (from the input list) to its corresponding function name,
              as found in the function summary. For example, if a function "my_function" has an offset 4096, an entry in the return
              value would be { 4096: "my_function" }.
      - Literal[False]: Returns False if the function summary cannot be retrieved.

    Example:
      Given a binary where the function summary includes:
      
          "my_function" with offset 4096 and "another_function" with offset 8192
      
      Calling:
          await get_function_name("binary_oid", [4096, 8192])
      
      Would return:
          {
              4096: "my_function",
              8192: "another_function"
          }
    """
    result = oxide.retrieve("function_summary", [oid])
    if result:
        logger.info("Retrieved summary successfully!")
        result = result[oid]
        mapping = {}
        for func_name, details in result.items():
            offset_val = details['offset']
            if offset_val in function_offsets:
                mapping[offset_val] = func_name
        return mapping
    else:
        logger.error("Failed to retrieve summary")
        return False


@mcp.tool()
async def function_summary(oid: str) -> dict[Any,Any] | Literal[False]:
    """
    Retrieve summaries of functions for a binary file.
    
    Returns: JSON with summary information about each function in the binary file 
    in a dictionary format. The dictionary key is function name and the value is
    another dictionary containing: offset, signature, number of instructions, complexity,
    operands, and parameters.
    Example:
    {
        \"_init\": {
            \"offset\": 4096, 
            \"signature\": \"int __stdcall _init(EVP_PKEY_CTX * ctx)\", 
            \"num_insns\": 8, 
            \"complexity\": 7, 
            \"complexity_desc\": \"simple\", 
            \"operands\": {
                \"imm\": 3, 
                \"reg\": 6, 
                \"mem\": 1
            }, 
            \"params\": [\"EVP_PKEY_CTX *\"]
        }
    }

    Args:
    oid: the object id of the binary we are interested in
    """
    result = oxide.get_field("function_summary", [oid], oid)
    if result:
        logger.info("Retrieved summary successfully!")
        return result
    else:
        logger.error("Failed to retrieve summary")
        return False
    
@mcp.tool()
async def control_flow_graph(oid: str, function_name: str = None, function_offset:int = None) -> dict[Any, Any] | Literal[False]:
    """
    Retrieve the Control Flow Graph (CFG) for functions in a binary, optionally filtering by function name or function offset.

    **Inputs:**
      - oid (str): The object ID of the binary to be analyzed.
      - function_name (str, optional): The name of the specific function whose CFG should be retrieved.
      - function_offset (int, optional): The offset of the specific function whose CFG should be retrieved.

    If neither function_name nor function_offset is provided, the function returns the CFGs for all functions in the binary.

    **Returns:**
      - dict: A JSON-compatible dictionary representing the CFG(s). For each function, the CFG is formatted as follows:

            {
                "name": FUNCTION_NAME,
                "nodes": {
                    "NODE_OFFSET_1": {
                        "INSTR_OFFSET_1": "INSTRUCTION 1",
                        "INSTR_OFFSET_2": "INSTRUCTION 2",
                        ...
                    },
                    ...
                },
                "edges": {
                    "NODE_OFFSET_SOURCE_1": ["NODE_OFFSET_TARGET_1", "NODE_OFFSET_TARGET_2", ...],
                    ...
                }
            }

            where:
              - **Nodes**: Each key in the "nodes" dictionary represents a basic block (identified by its node offset). The value is a dictionary mapping instruction offsets to their corresponding instructions within that block.
              - **Edges**: Each key in the "edges" dictionary is a source basic block offset. The associated value is a list of target basic block offsets, representing the control flow transitions between these basic blocks.

      - Literal[False]: Returns False if the CFG cannot be retrieved.
    """
    cfgs = oxide.retrieve("mcp_control_flow_graph", [oid])
    if cfgs:
        if function_name:
            for f in cfgs:
                if cfgs[f]["name"] == function_name:
                    result = cfgs[f]
                    break
        elif function_offset:
            result = cfgs[function_offset]
        else:
            result = cfgs
        logger.info("Retrieved control flow graph successfully!")
        return result
    else:
        logger.error("Failed to retrieve control flow graph")
        return False

@mcp.tool()
async def call_graph(oid: str) -> dict[Any,Any] | Literal[False]:
    """
    Retrieve a call graph for a binary file.
    
    Returns: A JSON dictionary with two entries: nodes and links. Nodes is a list of dictionaries
    providing the id for each nodes, which are function offsets and not function names. 
    Links is a list of dictionaries providing the offsets of the source and target functions
    for each call. 
    Example:
    {
        "nodes": [
            {"id": 4096}, 
            {"id": 20520}, 
            {"id": 4288},
            {"id": 20512} 
        ], 
        "links": [
            {"source": 4096, "target": 20520}, 
            {"source": 4288, "target": 20512}
        ]
    }

    Args:
    oid: the object id of the binary we are interested in
    """
    result = oxide.retrieve("call_graph", [oid])
    if result:
        logger.info("Retrieved call graph successfully!")
        result = result[oid]  # Return only information for this oid
        # print(str(result), file=sys.stderr)
        result_dict = nx.node_link_data(result)
        # Simplify the result so that it's just nodes and links
        result_dict = { "nodes" : result_dict["nodes"], "links" : result_dict["links"] }
        return result_dict
    else:
        logger.error("Failed to retrieve call graph")
        return False

@mcp.tool()
async def call_mapping(oid: str, function_offset: int = None) -> dict[Any, Any] | Literal[False]:
    """
    Retrieve a mapping of call relationships for functions in a binary, with an option to filter by a specific function offset.

    **Inputs:**
      - oid (str): The object ID of the binary to be analyzed.
      - function_offset (int, optional): The specific function offset for which to return the call mapping.
          If provided, only the call mapping for that function offset will be returned; otherwise, the mapping for all functions is returned.

    **Returns:**
      - dict: A JSON-compatible dictionary representing the call relationships. Each key is a function offset, and its value is a dictionary containing:
          - "calls_to": A list of dictionaries mapping the offset of a target function (i.e., a function called by the given function) to its virtual address (vaddr).
          - "calls_from": A list of dictionaries mapping the offset of a calling function (i.e., a function that calls the given function) to its virtual address (vaddr).
          
          If a function_offset is provided, the function returns the call mapping for that specific function offset.
      
      - Literal[False]: Returns False if the call mapping cannot be retrieved.

    **Example:**
      Full mapping:
          {
              GIVEN_FUNC_OFFSET: {
                  "calls_to": [ TARGET_FUNC_OFFSET: TARGET_FUNC_VADDR, ... },
                  "calls_from": [ CALLING_FUNCT_OFFSET: CALLING_FUNCT_VADDR, ... } 
              },
              ...
          }

      Specific mapping (e.g., for function offset GIVEN_FUNC_OFFSET):
          {
              "calls_to": [ TARGET_FUNC_OFFSET: TARGET_FUNC_VADDR, ... ],
              "calls_from": [ CALLING_FUNCT_OFFSET: CALLING_FUNCT_VADDR, ... ]
          }
    """
    result = oxide.retrieve("call_mapping", [oid])
    if result:
        logger.info("Retrieved call mapping successfully!")
        if function_offset:
            return result.get(function_offset, {})
        else:
            return result
    else:
        logger.error("Failed to retrieve call mapping")
        return False

@mcp.tool()
async def file_stats(oid: str) -> dict[Any,Any] | Literal[False]:
    """
    Get general file stats for a binary file
    
    Returns: A JSON dictionary containing the statistics for each binary file in the collection by their individual oid.
    The dictionary includes the number of basic blocks, the number of functions, the number of sections, whether or not the
    RTTI is present and if present, the section names.
    Example:
    {
        "Names": "v8", 
        "Number of sections": 30, 
        "Section names": ".interp,.note.gnu.property,.note.gnu.build-id,.note.ABI-tag"
    }

    Args:
    oid: the object id of the binary we are interested in
    """
    result = oxide.retrieve("file_stats", [oid])
    if result:
        logger.info("Retrieved file stats successfully!")
        result = result[oid]  # Return only information for this oid
        return result
    else:
        logger.error("Failed to retrieve file stats")
        return False

@mcp.tool()
async def strings(oid: str) -> dict[Any,Any] | Literal[False]:
    """
    Get ASCII strings contained in a binary file

    Returns: A JSON dictionary where the keys are offsets where the string was found
    and the values are the actual strings.
    Example:
    {
        "792": "/lib64/ld-linux-x86-64.so.2", 
        "1209": "libc.so.6",
        "1219": "__isoc99_scanf"
    }

    Args:
    oid: the object id of the binary we are interested in
    """
    result = oxide.retrieve("strings", [oid])
    if result:
        logger.info("Retrieved strings successfully!")
        result = result[oid]  # Return only information for this oid
        return result
    else:
        logger.error("Failed to retrieve strings")
        return False

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

# @mcp.tool()
# async def disassemble_function(oid:str, function_name:str) -> str | Literal[False]:
#     """
#     Return the disassembly for a specified function as a string. 

#     Args:
#         oid: the ID of the binary file containing the desired function
#         function_name: the name of the desired function
#     """
#     result = oxide.retrieve("disassembly", [oid])
#     if result:
#         logger.info("Retrieved disassembly successfully!")
#         return_str = ''
#         return return_str

#     else:
#         logger.error("Failed to retrieve ghidra decompilation mapping")
#         return False

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
async def decompile_function(oid:str, function_name:str) -> str | Literal[False]:
    """
    Returns the decompilation for a specified function as a string. 

    Args:
        oid: the ID of the binary file containing the desired function
        function_name: the name of the desired function
    """
    result = oxide.retrieve("ghidra_decmap", [oid], {"org_by_func": True})
    if result:
        logger.info("Retrieved ghidra decompilation mapping successfully!")

        # Find object for this function
        functions_dict = result['decompile']
        # for function_name, func_item in functionsDict.items():
        #     print(function_name, file=sys.stderr)
        if (function_name not in functions_dict.keys()):
            return False        
        function_dict = functions_dict[function_name] 

        # Gather the decompilation lines into a map (they will not be returned in order)
        decomp_map = {}
        for offset_key, offset_value in function_dict.items():
            # print(f"OFFSET {offset_key}", file=sys.stderr)
            # For this offset, walk through the lines to add to the decomp line map
            for line_str in offset_value['line']:
                # print(line_str, file=sys.stderr)
                # Extract the line number and code text 
                split = line_str.find(": ")
                line_no_str = line_str[:split]
                line_no = int(line_no_str)
                code = line_str[split + 2:]
                # Find the decomp line for this line number. Create it if not existing.
                decomp_line = decomp_map.get(line_no, None)
                if not decomp_line:
                    decomp_map[line_no] = code

        # Generate a string with all the decompilation line in order
        return_str = ''
        indent_level = 0
        for line_num in sorted(decomp_map.keys()):
            # print(line_num, file=sys.stderr)
            code = str(decomp_map[line_num])
            # print(code, file=sys.stderr)
            if '}' in code:
                indent_level -= 1
            return_str += (('    ' * indent_level) + code + '\n')
            if '{' in code:
                indent_level += 1
        # print(return_str, file=sys.stderr)
        return return_str

    else:
        logger.error("Failed to retrieve ghidra decompilation mapping")
        return False
    
if __name__ == "__main__":
    mcp.run(transport="stdio")
