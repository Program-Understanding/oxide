from oxide.core import oxide as oxide
import logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("oxide mcp server")
from mcp.server.fastmcp import FastMCP
from typing import Any, Literal

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
