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
from typing import Any, List, Optional, Tuple, Protocol
# pyright: reportAssignmentType=false
# These will be wired in oxide.py
# so any lsp errors here are incorrect

class Retrieve(Protocol):
    def __call__(self, mod_name: str, oid_list: List[str] | str, opts: dict = {},
             lock: bool = False, dir_override: Optional[str] = None) -> Optional[dict]:
        ...

class LocalRetrieve(Protocol):
    def __call__(self,plugin_name: str, data_name: str) -> Optional[Any]:
        ...

class LocalStore(Protocol):
    def __call__(self,plugin_name: str, data_name: str, data: Any) -> bool:
        ...

class GetField(Protocol):
    def __call__(self,mod_name: str, oid: str, field: str, opts: dict = {},
              dir_override: Optional[str] = None) -> Optional[Any]:
                 ...
class ValidOids(Protocol):
    def __call__(self,l: List[str]) -> Tuple[List[str], List[str]]:
        ...

class ExpandOids(Protocol):
    def __call__(self,oids: str| List[str]) -> List[str]:
        ...

apply_tags                 = None
collection_names           = None
collection_cids            = None
create_collection          = None
delete_collection_by_cid   = None
delete_collection_by_name  = None
documentation              = None
exists                     = None
expand_oids                : ExpandOids = None
flush_oid                  = None
flush_module               = None
get_cid_from_oid_list      = None
get_cid_from_name          = None
get_colname_from_oid       = None
get_field                  : GetField = None
get_names_from_oid         = None
get_oids_with_name         = None
get_oid_from_data          = None
get_available_modules      = None
get_orphan_oids            = None
get_tags                   = None
import_file                = None
import_directory           = None
local_available_data       = None
local_count_records        = None
local_delete_data          = None
local_delete_function_data = None
local_exists               = None
local_retrieve             : LocalRetrieve = None
local_retrieve_all         = None
local_store                : LocalStore = None
load_reference             = None
models_dir                 = None
modules_list               = None
retrieve                   : Retrieve = None
retrieve_all_keys          = None
scratch_dir                = None
libraries_dir              = None
ghidra_path                = None
ghidra_path2               = None
ghidra_path3               = None
ghidra_path4               = None
ghidra_path5               = None
ghidra_project             = None
pharos_image               = None
source                     = None
store                      = None
process                    = None
tag_filter                 = None
valid_oids                 : ValidOids= None
tmp_file                   = None
scripts_dir                = None
