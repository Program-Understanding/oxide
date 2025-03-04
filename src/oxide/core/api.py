from typing import Any, List, Optional, Tuple, Dict, Set
# pyright: reportAssignmentType=false
# pyright: reportUnusedVariable=false
# These will be wired in oxide.py
# so any lsp errors here are incorrect

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
def get_cid_from_oid_list(oid_list):
    ...
def get_cid_from_name(col_name):
    ...
def get_colname_from_oid(oid: str) -> Set[str]:
    ...
def get_field(mod_name: str, oid: str, field: str,
              opts: dict = {}, dir_override: Optional[str] = None) -> Optional[Any]:
    """
    Given a module name, oid and a field return the value of that field

    Args:
    mod_name (str): The name of the module
    oid (str): OID to query
    field (str): The field to search for from the module's return dict
    opts (dict): The options to pass the module
    dir_override(Optional[str])
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
        ...
def load_reference(ref_name: str) -> Optional[bytes]:
    ...
models_dir = "UNUSED"
def modules_list(module_type: str = "all", show_private: bool = False):
    ...
def retrieve(mod_name: str, oid_list: List[str] | str, opts: dict = {},
             lock: bool = False, dir_override: Optional[str] = None) -> Optional[dict]:
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
def source(oid: str, dir_override: Optional[str] = None) -> Optional[str]:
    ...
def store(mod_name: str, oid: str, data: Dict[str|int,Any], opts: dict = {}, block: bool = True,
          dir_override: Optional[str] = None)->bool:
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
