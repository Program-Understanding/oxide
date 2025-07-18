from typing import Any, List, Optional, Tuple, Dict, Set, Literal, overload
#from core.ohints.ghidra_hints import GhidraDisasmBlocks, GhidraDisasmFunctions
# pyright: reportAssignmentType=false
# pyright: reportUnusedVariable=false
# These will be wired in oxide.py
# so any lsp errors here are incorrect

# The api import is an Oxide specific interface that gives the module developer access
# to features of Oxide. This interface is the only way that a module should interact
# with the Oxide system. Modules should never attempt to directly import or call other
# components and should not presume to know anything about the directory structure,
# datastore structure, etc. above their module directory. Ignoring this guideline may
# lead to incompatibility and strange errors in configurations of the system that differ
# from the module developer’s.

def apply_tags(oid_list: List[str], new_tags: List[str]) -> None:
    ...
def collection_names() -> List[str]:
    ...
def collection_cids() -> List[str]:
    ...
def create_collection(col_name: str, oid_list: List[str], notes: str = "") -> bool:
    ...
def delete_collection_by_cid(cid):
    ...
def delete_collection_by_name(col_name):
    ...
def documentation(mod_name: str) -> Optional[dict]:
    ...
def exists(mod_name: str, oid: str, opts={}, dir_override: Optional[str] = None) -> bool:
    ...
def expand_oids(oids: str| List[str]) -> List[str]:
        ...
def flush_oid(oid: str) -> None:
    ...
def flush_module(mod_name: str) -> None:
    ...
def flush_oid_for_module(oid: str, mod_name: str) -> None:
    """ Given an oid and module, clears out the data for that oid """
    ...
def get_cid_from_oid_list(oid_list):
    ...
def get_cid_from_name(col_name):
    ...
def get_colname_from_oid(oid: str) -> Set[str]:
    ...

# @overload
# def get_field(mod_name: Literal["ghidra_disasm"], oid: str, field: Literal["original_blocks"],
#               opts: dict = {}, dir_override: Optional[str] = None) -> Optional[Dict[int,GhidraDisasmBlocks]]:
#     ...
# @overload
# def get_field(mod_name: Literal["ghidra_disasm"], oid: str, field: Literal["functions"],
#               opts: dict = {}, dir_override: Optional[str] = None) -> Optional[Dict[int,GhidraDisasmFunctions]]:
#     ...
# @overload
# def get_field(mod_name: Literal["ghidra_disasm"], oid: str, field: Literal["instructions"],
#               opts: dict = {}, dir_override: Optional[str] = None) -> Optional[dict]:
#     ...
#have to overload again... weird Python behavior but this overload tells the type checker
#that we do allow for any str besides matching the literals above, and that its not an error
#on the user's part if they don't match any other overloads
# @overload
# def get_field(mod_name: str, oid: str, field: str,
#               opts: dict = {}, dir_override: Optional[str] = None) -> Optional[Any]:
#     ...
def get_field(mod_name: str, oid: str|list[str], field: str,
              opts: dict[Any,Any] = {}, dir_override: Optional[str] = None) -> Optional[Any]:
    """
    Given a module name, oid and a field return the value of that field

    Args:
    mod_name (str): The name of the module
    oid | oid_list (str | list[str]): OID or list of OIDs to query
    field (str): The field to search for from the module's return dict
    opts (dict): The options to pass the module
    dir_override(Optional[str])

    This is the preferred way to retrieve data if only a single field is needed from another
    module. The field specified should be a key in the dictionary saved out by the given
    module. This function has the advantage of doing validation and will return None if
    the field does not exist. Always test for a None result.
    """
    ...
def get_names_from_oid(oid: str) -> Set[str]:
    ...
def get_oids_with_name(some_name: str) -> Dict[str, str]:
    ...
def get_oid_from_data(data: bytes) -> str:
    ...
def get_available_modules(category: Optional[str] = 'all') -> List[str]:
    ...
def get_orphan_oids() -> List[str]:
    ...
def get_tags(oid: str) -> Optional[List[str]]:
    ...
def import_file(file_location: str, dir_override: Optional[str] = None) -> Tuple[Optional[str], bool]:
    ...
def import_directory(directory: str, dir_override: Optional[str] = None) -> Tuple[List[str], int]:
    ...    
def local_available_data(plugin_name: str) -> List[str]:
    ...
def local_retrieve_all(plugin_name: str) -> Dict[str, bytes]:
    ...
def local_delete_data(plugin_name: str, data_name: str) -> bool:
    """ Given an oid and the name of a module, remove the data for that
        combination if it exists.
    """
    ...
def local_delete_function_data(plugin_name: str) -> bool:
    """ Remove all stored data for a given module.
    """
    ...
def local_exists(plugin_name: str, data_name: str) -> bool:
    """ Determine whether file exists on local file system
    """
    ...
def local_retrieve(plugin_name: str, data_name: str) -> Optional[Any]:
        ...
def retrieve_all(mod_name: str, dir_override: Optional[str] = None) -> dict:
    ...
def local_store(plugin_name: str, data_name: str, data: Any) -> bool:

    """
    Store to the local datastore.

    Args:
    plugin_name (str): Name of the plugin
    data_name (str): Name of the data to store. Used for lookup later. Typically OID.
    data (Any): The data to store assosciated with the plugin_name and data_name.

    The local store function is used by plugins to store results locally. The parameters are
    the function name, the name of the data and the, the data to store which should always
    be a dict. This function returns a boolean to indicate success or failure.
    """
    ...
def load_reference(ref_name: str) -> Optional[bytes]:
    ...
models_dir = "UNUSED"
def modules_list(module_type: str = "all", show_private: bool = False):
    ...

def retrieve(mod_name: str, oid_list: List[str] | str, opts: dict = {},
             lock: bool = False, dir_override: Optional[str] = None) -> Optional[dict]:
    """ Returns the results of calling a module over an oid_list.
    
    Args:
    mod_name (str): The name of the module to call
    oid_list (List[str] | str): The OID or OIDs to call the module on
    opts (dict): Optional, the options to pass to the module
    lock (bool)
    dir_override: Optional[str]

    Retrieve is the way to get the result of any module. If the analysis already exists, then it
    will be retrieved from the datastore directly. Otherwise, the module will be run to gen-
    erate it. Note that this means that a given module may or may not be called depending
    on the state of the datastore. Never directly index into the returned dictionary without
    validating that the desired key exists.
    """
    ...
def retrieve_all_keys(mod_name: str) -> Optional[List[str]]:
    ...
scratch_dir = None
libraries_dir = None
ghidra_path = ""
ghidra_path2 = ""
ghidra_path3 = ""
ghidra_path4 = ""
ghidra_path5 = ""
ghidra_project = ""
pharos_image = ""
local_llm_path = ""
def source(oid: str, dir_override: Optional[str] = None) -> Optional[str]:
    ...
def store(mod_name: str, oid: str, data: dict[object,object], opts: dict[str,object] = {},
          block: bool = True, dir_override: str|None = None)->bool:
    """
    Store the results of a module in the datastore

    Args:
    mod_name (str): The name of the module being stored
    oid (str): The OID corresponding to the data
    data (Dict[str|int,Any]: The results of the module
    opts (dict): The options provided when the module was called
    block (bool)
    dir_override (Optional[str])

    The store function is used by modules that store results. All extractor modules should
    call this if valid features are extracted. The parameters are the module name, the oid
    that you wish to use as a key, the data to store (this should always be a dict), and the
    options dictionary that the module was called with. If your module has no mangle
    options, you can leave off the opts dict as it is used to create a unique key for different
    values of the mangle options. This function returns a boolean to indicate success or
    failure.

    Plugins should NOT use store. For plugins, use local_store.
    """
    ...
def process(mod_name: str, oid_list: List[str], opts: dict = {},
            force: bool = False, dir_override: Optional[str] = None) -> bool:
    """ Calls a module over an oid_list without returning results.
    """
    ...
def tag_filter(oid_list: List[str], tag: str, value: str = "<empty>") -> Optional[List[str]]:
    ...
def valid_oids(l: List[str]) -> Tuple[List[str], List[str]]:
    ...
def tmp_file(name: str, data: bytes, empty: bool = False, override: bool = False) -> Optional[str]:
    """ Given a file name and data uses the Python tempfile package to write the file to
        the scratch directory.
    """
    ...
scripts_dir = ""
