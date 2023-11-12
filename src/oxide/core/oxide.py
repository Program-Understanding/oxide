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

import os
import sys
import imp
import hashlib
import logging

from oxide.core import config, sys_utils, ologger, api, progress, options, tags, otypes

# Datstore settings
from oxide.core.local_datastore import (local_store, local_retrieve, local_exists, local_available_data,
                                  local_retrieve_all, local_count_records, local_delete_data,
                                  local_delete_function_data)

if "filesystem" == config.datastore_datastore:
    from oxide.core import datastore_filesystem as datastore
elif "sqlite" == config.datastore_defaults:
    from oxide.core import datastore_sqlite as datastore
else:
    raise ShellRuntimeError(f"Invalid datastore option selected ({config.datastore_defaults})")

from typing import List, Dict, Union, Any, Tuple, Optional, Set, Iterable

# Prepend our dirs in the path
sys.path.insert(0, config.dir_oxide)
sys.path.insert(0, config.dir_libraries)


# Initialize logger
ologger.init()

NAME = "oxide"
logger = logging.getLogger(NAME)
logger.debug("Starting oxide (3.1)")

try:
    import multiproc as mp
except ImportError:
    config.multiproc_on  = False
    config.multiproc_max = 1
    logger.info("Not able to import multiproc, multiprocessing will be disabled")

for d in list(config.get_section("dir").values()):
    sys_utils.ensure_dir_exists(d)

DEBUG = False

initialized_modules = {}  # Used to call modules
module_types = ["source", "extractors", "analyzers", "map_reducers"]
modules_available = {}
for mod_type in module_types:
    modules_available[mod_type] = []


# ------------- CORE FUNCTIONS -------------------------------------------------------------

def get_oid_from_data(data: bytes) -> str:
    """ Given the a blob of data return the <oid>. This is hard coded to sha1sum
        for now.
    """
    return hashlib.sha1(data).hexdigest()


def documentation(mod_name: str) -> Optional[dict]:
    """ Return the documentaton of a module
    """
    if mod_name not in initialized_modules:
        logger.error("Documentation::Module %s not found.", mod_name)
        return None
    # Catch syntax errors
    try:
        mod_doc = initialized_modules[mod_name].documentation()
    except NameError:
        logger.debug("Documentation syntax error in %s", mod_name)
        mod_doc = None

    return mod_doc


def get_mod_type(mod_name: str) -> Optional[str]:
    """ Return the type of a module (extracts, analyzers, etc)
    """
    for module_type in module_types:
        if mod_name in modules_available[module_type]:
            return module_type
    return None


def single_call_module(module_type: str, mod_name: str, oid_list: List[str], opts: dict) -> dict:
    """ Calls any module type with one oid_list
    """
    if module_type in ["extractors", "source"]:
        return initialized_modules[mod_name].process(oid_list, opts)

    if module_type in ["analyzers"]:
        return initialized_modules[mod_name].results(oid_list, opts)

    if module_type in ["map_reducers"]:
        p = progress.Progress(len(oid_list))
        jobid = get_cid_from_oid_list(oid_list)
        results = []
        for oid in oid_list:
            results.append(initialized_modules[mod_name].mapper(oid, opts, jobid))
            p.tick()
        return initialized_modules[mod_name].reducer(results, opts, jobid)

    raise otypes.UnrecognizedModule("Attempt to call module not in module list")


def process(mod_name: str, oid_list: List[str], opts: dict = {},
            force: bool = False, dir_override: Optional[str] = None) -> bool:
    """ Calls a module over an oid_list without returning results.
    """
    if dir_override:
        change_db_dir(dir_override)

    # returns true false, so does not need to check oid_list for None
    if not oid_list:
        return True

    logger.debug("process %s %s", mod_name, oid_list)
    # Clean up and validate inputs
    module_type = get_mod_type(mod_name)
    if not module_type:
        logger.error("Module %s not found", mod_name)
        if dir_override:
            restore_db_dir()
        return False

    oid_list = cleanup_oid_list(mod_name, oid_list)

    if not options.validate_opts(mod_name, opts):
        logger.error("Failed to validate opts for %s : %s", mod_name, opts)
        if dir_override:
            restore_db_dir()
        return False
    try:
        # Prune analysis that already exists
        new_list = []
        for oid in oid_list:
            if not exists(mod_name, oid, opts) or force:
                new_list.append(oid)

        if len(new_list) == 0:  # Everything was already processed
            ret_val = True
        else:
            # Process the oid_list
            # Check module documentation to determine whether it can be parellized
            mod_doc = documentation(mod_name)
            if ((len(new_list) == 1) or (not config.multiproc_on) or
                (module_type in ["analyzers"]) or
                (mod_doc and ('multiproc' in mod_doc) and (not mod_doc['multiproc']))):
                ret_val = True
                if module_type in ["extractors", "source"]:
                    p = progress.Progress(len(new_list))
                    for oid in new_list:
                        if not single_call_module(module_type, mod_name, oid, opts):
                            ret_val = False
                        p.tick()
                else:
                    # Don't keep the return value of analyzers and map_reducers, return False if they return None

                    if not single_call_module(module_type, mod_name, new_list, opts):
                        ret_val = False

            else:  # Multiprocessing is on and not an analysis module
                if module_type in ["extractors", "source"]:
                    func = initialized_modules[mod_name].process
                elif module_type in ["map_reducers"]:
                    func = initialized_modules[mod_name].mapper
                else:
                    raise otypes.UnrecognizedModule("Attempt to call module not of known type.")
                ret_val = mp.multi_map(func, new_list, opts, True)
    except:
        if dir_override:
            restore_db_dir()
        datastore.cleanup()
        raise
    if dir_override:
        restore_db_dir()

    return ret_val


def single_retrieve(mod_name: str, oid: str, opts: dict, lock: bool) -> Optional[dict]:
    """ Retrieve module results for a single <oid>
    """
    if not datastore.exists(mod_name, oid, opts):
        if not options.validate_opts(mod_name, opts):
            logger.warning("Failed to validate opts for %s : %s", mod_name, opts)
            return None
        process(mod_name, oid, opts)
    if lock:
        return datastore.retrieve_lock(mod_name, oid, opts)
    return datastore.retrieve(mod_name, oid, opts)


def multi_retrieve(mod_name: str, oid_list: List[str], opts: dict, lock: bool) -> Dict[str, dict]:
    """ Retrieve module results for a list of <oid>
    """
    results = {}
    for oid in oid_list:
        results[oid] = single_retrieve(mod_name, oid, opts, lock)
    return results


def retrieve(mod_name: str, oid_list: List[str], opts: dict = {},
             lock: bool = False, dir_override: Optional[str] = None) -> Optional[dict]:
    """ Returns the results of calling a module over an oid_list.
    """
    if dir_override:
        change_db_dir(dir_override)

    if not oid_list:
        return None

    logger.debug("retrieve %s %s", mod_name, oid_list)
    # Clean up and validate inputs
    module_type = get_mod_type(mod_name)
    if not module_type:
        logger.error("Module %s not found", mod_name)
        if dir_override:
            restore_db_dir()
        return None

    oid_list = cleanup_oid_list(mod_name, oid_list)

    # Validate only mangle options unless we have to actually call the module
    if not options.validate_opts(mod_name, opts, True):
        logger.warning("Failed to validate opts for %s : %s", mod_name, opts)
        if dir_override:
            restore_db_dir()
        return None

    try:
        if ((not config.multiproc_on) or (module_type in ["analyzers"])):
            if module_type in ["extractors", "source"]:
                if len(oid_list) == 1:
                    ret_val = single_retrieve(mod_name, oid_list[0], opts, lock)
                    if dir_override:
                        restore_db_dir()
                    return ret_val

                ret_val = multi_retrieve(mod_name, oid_list, opts, lock)
                if dir_override:
                    restore_db_dir()
                return ret_val

            else:
                if len(oid_list) == 1:
                    if datastore.exists(mod_name, oid_list[0], opts):
                        ret_val = datastore.retrieve(mod_name, oid_list[0], opts)
                        if dir_override:
                            restore_db_dir()
                        return ret_val
                if not options.validate_opts(mod_name, opts):
                    logger.warning("Failed to validate opts for %s : %s", mod_name, opts)
                    ret_val = False
                    if dir_override:
                        restore_db_dir()
                    return ret_val
                ret_val = single_call_module(module_type, mod_name, oid_list, opts)
                if dir_override:
                    restore_db_dir()
                return ret_val
        else:   # Multiprocessing is on and not an analysis module
            if module_type in ["extractors", "source"]:
                if len(oid_list) == 1:
                    ret_val = single_retrieve(mod_name, oid_list[0], opts, lock)
                    if dir_override:
                        restore_db_dir()
                    return ret_val

                new_list = []
                for oid in oid_list:
                    if not exists(mod_name, oid, opts):
                        new_list.append(oid)
                if new_list and not options.validate_opts(mod_name, opts):
                    logger.warning("Failed to validate opts for %s : %s", mod_name, opts)
                    if dir_override:
                        restore_db_dir()
                    return None
                func = initialized_modules[mod_name].process
                mp.multi_map(func, new_list, opts, True)
                ret_val = multi_retrieve(mod_name, oid_list, opts, lock)
                if dir_override:
                    restore_db_dir()
                return ret_val

            else:  # Map Reducer module
                if len(oid_list) == 1:
                    if datastore.exists(mod_name, oid_list[0], opts):
                        ret_val = datastore.retrieve(mod_name, oid_list[0], opts)
                        if dir_override:
                            restore_db_dir()
                        return ret_val
                if not options.validate_opts(mod_name, opts):
                    logger.warning("Failed to validate opts for %s : %s", mod_name, opts)
                    if dir_override:
                        restore_db_dir()
                    return None
                jobid = get_cid_from_oid_list(oid_list)
                map_func = initialized_modules[mod_name].mapper
                reduce_func = initialized_modules[mod_name].reducer
                ret_val = mp.multi_mapreduce(map_func, reduce_func, oid_list, opts, jobid)
                if dir_override:
                    restore_db_dir()
                return ret_val

    except:  # FIXME:: Raw except
        if dir_override:
            restore_db_dir()
        datastore.cleanup()
        raise
    if dir_override:
        restore_db_dir()


def exists(mod_name: str, oid: str, opts={}, dir_override: Optional[str] = None) -> bool:
    if dir_override:
        change_db_dir(dir_override)
    if not options.validate_opts(mod_name, opts, only_mangle=True):
        if dir_override:
            restore_db_dir()
        return False
    try:
        val = datastore.exists(mod_name, oid, opts)
    except TypeError:
        val = False

    if dir_override:
        restore_db_dir()
    return val


def get_field(mod_name: str, oid: str, field: str, opts: dict = {},
              dir_override: Optional[str] = None) -> Optional[Any]:
    """ Given a module name, oid and a field return the value of that field
    """
    if dir_override:
        change_db_dir(dir_override)
    ds = retrieve(mod_name, oid, opts)
    if not ds:
        if dir_override:
            restore_db_dir()
        return None
    if field not in ds:
        logger.info("Invalid field:%s for module:%s", field, mod_name)
        if dir_override:
            restore_db_dir()
        return None
    if dir_override:
        restore_db_dir()
    return ds[field]


def retrieve_all(mod_name: str, dir_override: Optional[str] = None) -> dict:
    if dir_override:
        change_db_dir(dir_override)
    return_val = datastore.retrieve_all(mod_name)
    if dir_override:
        restore_db_dir()
    return return_val


def store(mod_name: str, oid: str, data: bytes, opts: dict = {}, block: bool = True,
          dir_override: Optional[str] = None):
    if dir_override:
        change_db_dir(dir_override)
    return_val = datastore.store(mod_name, oid, data, opts, block)
    if dir_override:
        restore_db_dir()
    return return_val


def source(oid: str, dir_override: Optional[str] = None) -> Optional[str]:
    if not oid:
        return None
    if dir_override:
        change_db_dir(dir_override)
    for source in modules_available["source"]:
        if exists(source, oid, {}):
            logger.debug("Source of %s is %s", oid, source)
            return source
    if dir_override:
        restore_db_dir()
    return None


def change_db_dir(directory: str) -> None:
    """ Overwrite current datastore directory
    """
    datastore.datastore_dir = directory


def restore_db_dir() -> None:
    """ Update datastore directory using config value
    """
    datastore.datastore_dir = config.dir_datastore


# ------------------------ DELETE FUNCTIONS ----------------------------------------
def flush_oid(oid: str) -> None:
    """ Clears data for a particular OID accross all modules that can currently be loaded
    """
    logger.warning("Flushing data for oid %s", oid)
    for cid in collection_cids():
        if oid in expand_oids(cid):
            prune_collection_by_cid(cid, [oid])
            flush_oid(cid)

    for module_type in modules_available:
        for mod_name in modules_available[module_type]:
            datastore.delete_oid_data(mod_name, oid)


def flush_module(mod_name: str) -> None:
    """ Clears data for module (drop table)
    """
    logger.warning("Flushing data for module %s", mod_name)
    datastore.delete_module_data(mod_name)


# ------------------- MODULES RELATED FUNCTIONS --------------------------------------------------
def module_types_list() -> List[str]:
    return module_types


def modules_list(module_type: str = "all", show_private: bool = False):
    mod_list = []
    for mt in modules_available:
        """For each module type"""
        if module_type == mt or module_type == "all":
            for mod in modules_available[mt]:
                """For each module of that type"""
                d = documentation(mod)
                if ((show_private is False) and (d is not None) and ("private" in d)):
                    if d["private"]:
                        continue
                    mod_list.append(mod)
                else:
                    mod_list.append(mod)
    return mod_list


def modules_stats(modules="all", module_type="all", show_private=True):
    mod_list = []
    if modules == "all":
        mod_list = modules_list(module_type, show_private)
    mod_stats = {}
    for mod in mod_list:
        count = datastore.count_records(mod)
        if count > 0:
            mod_stats[mod] = datastore.count_records(mod)
    return mod_stats


# ---------------------------------- FILE RELATED FUNCTIONS --------------------------------------
def import_file(file_location: str, dir_override: Optional[str] = None) -> Tuple[Optional[str], bool]:
    fd = sys_utils.import_file(file_location, config.file_max)
    if not fd:
        print('no file descriptor')
        return None, False

    oid = get_oid_from_data(fd["data"])
    if not oid:
        print('Not able to get OID')
        logger.error("Not able to get and oid for %s", file_location)
        return None, False

    opts_file = {"file_contents": fd["data"]}
    opts_meta = {"file_location": file_location, "stat": fd["file_stat"]}

    if not exists("files", oid, opts_file, dir_override=dir_override):
        new_file = True
        if not process("files", oid, opts_file, dir_override=dir_override):
            print('not able to process')
            logger.error("Not able to process file data %s", file_location)
            return None, False
    else:
        new_file = False
    if not process("file_meta", oid, opts_meta, force=True, dir_override=dir_override):
        print('Not able to process meta data')
        logger.error("Not able to process file metadata %s", file_location)
        return None, False

    logger.debug("%s file import complete.", file_location)
    return oid, new_file


def import_files(files_list: List[str], dir_override: Optional[str] = None) -> Tuple[List[str], int]:
    if not isinstance(files_list, list):
        logger.error("files must be of type list.")
        return None, 0
    try:
        # Blocking?
        oids = []
        new_file_count = 0
        
        if config.multiproc_on:
            files, _ = mp.multi_map_callable(import_file, files_list, {}, False)
            for oid, new_file in files:
                oids.append(oid)
                new_file_count += 1 if new_file else 0
        else:
            p = progress.Progress(len(files_list))
            for file_location in files_list:
                oid, new_file = import_file(file_location, dir_override=dir_override)
                p.tick()
                if oid:
                    oids.append(oid)
                    if new_file:
                        new_file_count += 1
    except:
        datastore.cleanup()
        raise

    oids = list(set(oids))  # assert uniqueness
    return oids, new_file_count


def import_directory(directory: str, dir_override: Optional[str] = None) -> Tuple[List[str], int]:
    files = sys_utils.get_files_from_directory(directory)
    if files is None:
        return None, 0
    return import_files(files, dir_override=dir_override)


# ------------------------------ GLOBAL SET FUNCTIONS --------------------------------------
def set_verbosity_level(level: int) -> bool:
    config.verbosity_level = level
    return ologger.set_level("verbosity", level)


def set_logging_level(level: str) -> bool:
    config.logging_level = level
    return ologger.set_level("logging", level)


# -------------------------- INTERNAL FUNCTIONS --------------------------------------------------
def initialize_all_modules() -> None:
    logger.debug("initialize_all_modules (%s)", module_types)
    for module_type in module_types:
        mod_dir = os.path.join(config.dir_modules, module_type)
        sys_utils.ensure_dir_exists(mod_dir)
        dev_dir = mod_dir + "_dev"
        sys_utils.ensure_dir_exists(dev_dir)
        mod_list = os.listdir(mod_dir)
        if config.dev_mode_enable:
            mod_list.extend(os.listdir(dev_dir))
        for mod_name in mod_list:
            this_mod_dir = os.path.join(mod_dir, mod_name)
            if not os.path.isdir(this_mod_dir):
                this_mod_dir = os.path.join(dev_dir, mod_name)
            init_file = os.path.join(this_mod_dir, "__init__.py")
            interface_file = os.path.join(this_mod_dir, "module_interface.py")
            if (os.path.isdir(this_mod_dir) and os.path.isfile(init_file) and os.path.isfile(interface_file)):
                if initialize_module(mod_name, os.path.split(this_mod_dir)[0]):
                    modules_available[module_type].append(mod_name)
                else:
                    logger.debug("Not able to initalize module %s", mod_name)
                # Debug warning to alert user loaded module is private
                mod_doc = documentation(mod_name)
                if (mod_doc and 'private' in mod_doc and mod_doc['private']):
                    logger.debug("%s is set to private in option dictionary", mod_name)
            else:
                logger.debug("%s, init file or interface file does not exist.", mod_name)
                logger.debug("\t %s:%s module: %s, init: %s, mod_interface: %s",
                    mod_dir, mod_name,
                    os.path.isdir(this_mod_dir),
                    os.path.isfile(init_file),
                    os.path.isfile(interface_file))

    # ugly hack to make source module lookup faster, places collections and files first in the list
    modules_available['source'].sort()


def initialize_module(mod_name: str, mod_dir: str) -> bool:
    global initialized_modules
    global DEBUG
    # Tweak our sys.modules to import modules from another branch directory
    # TODO:: replace with importlib as imp will be deprecated in future release

    # DELTEME:
    if DEBUG:
        if mod_name in ["emu_angr_disasm", "bap_disasm", "angr_function_id", "fst_angr_disasm"]:
            return False
        f, filename, description = imp.find_module(mod_name, [mod_dir])
        mod = imp.load_module(mod_name, f, filename, description)

        # Register the module in initialized_modules
        f, filename, description = imp.find_module("module_interface", [filename])
        submod = imp.load_module(mod_name, f, filename, description)
        submod.api = api
        initialized_modules[mod_name] = submod
    else:
        pass

    try:
        f, filename, description = imp.find_module(mod_name, [mod_dir])
        mod = imp.load_module(mod_name, f, filename, description)

        # Register the module in initialized_modules
        f, filename, description = imp.find_module("module_interface", [filename])
        submod = imp.load_module(mod_name, f, filename, description)
        submod.api = api
        initialized_modules[mod_name] = submod
    except TypeError as err:
        logger.debug('TypeError: %s in module(%s)', err, mod_name)
        return False
    except ModuleNotFoundError as err:
        logger.debug("ModuleNotFound:%s in module(%s)", err, mod_name)
        return False
    except ImportError as err:
        logger.debug("ImportError:%s in module(%s)", err, mod_name)
        return False
    except AttributeError as err:
        logger.debug("AttributeError:%s in module(%s)", err, mod_name)
        return False
    except SyntaxError as err:
        logger.debug("SyntaxError:%s in module(%s)", err, mod_name)
        return False
    except NameError as err:
        logger.debug("NameError:%s in module(%s)", err, mod_name)
        return False
    except OSError as err:
        logger.debug("NameError:%s in module(%s)", err, mod_name)
        return False
    return True


# -------------------------- COLLECTIONS FUNCTIONS -----------------------------------------------
def create_collection(col_name: str, oid_list: List[str], notes: str = "") -> bool:
    if not oid_list:
        logger.error("Cannot create an empty collection.")
        return False
    if col_name in collection_names():
        logger.error("Collection by that name already exist.")
        return False

    cid = get_cid_from_oid_list(oid_list)
    if cid in get_set_names():
        col_name = get_set_names()[cid]
        logger.error("This collection already exists. name:%s cid:%s", col_name, cid)
        return False

    opts = {"oid_list": oid_list}
    meta_opts = {"name": col_name, "num_oids": len(oid_list), "notes": notes}
    if not process("collections", cid, opts):
        logger.error("Collection creation failed")
        return False
    if not process("collections_meta", cid, meta_opts):
        logger.error("Collection metadata was not saved")
        return False
    return True


def delete_collection_by_name(col_name):
    cid = get_cid_from_name(col_name)
    if not cid:
        logger.error("Cannot delete this collection, name not found:%s", col_name)
        return False
    return delete_collection_by_cid(cid)


def delete_collection_by_cid(cid):
    source_set_dict = get_set_names()
    if cid not in source_set_dict:
        logger.error("Cannot delete this collection, cid not found:%s", cid)
        return False
    if ( not datastore.delete_oid_data("collections_meta", cid)
         or not datastore.delete_oid_data("collections", cid)):
        logger.error("Collection deletion failed")
        return False
    return True


def prune_collection_by_name(col_name, oid_list):
    cid = get_cid_from_name(col_name)
    if not cid:
        logger.error("Cannot prune this collection, name not found:%s", col_name)
        return False
    return prune_collection_by_cid(cid, oid_list)


def prune_collection_by_cid(cid, oid_prune_list):
    source_set_dict = get_set_names()
    if cid not in source_set_dict:
        logger.error("Cannot prune this collection, cid not found:%s", cid)
        return False

    d = datastore.retrieve("collections", cid)
    md = datastore.retrieve("collections_meta", cid)
    oid_list = d["oid_list"]
    for oid in oid_prune_list:
        if oid in oid_list:
            oid_list.remove(oid)
    if delete_collection_by_cid(cid):
        return create_collection(md["name"], oid_list, md["notes"])
    create_collection(md["name"], oid_list, md["notes"])
    return False


def rename_collection_by_name(orig_name, new_name):
    cid = get_cid_from_name(orig_name)
    if not cid:
        logger.error("Cannot rename this collection, name not found:%s", orig_name)
        return False
    return rename_collection_by_cid(cid, new_name)


def rename_collection_by_cid(cid, new_name):
    source_set_dict = get_set_names()
    if cid not in source_set_dict:
        logger.error("Cannot rename this collection, cid not found:%s", cid)
        return False
    d = datastore.retrieve("collections", cid)
    md = datastore.retrieve("collections_meta", cid)
    oid_list = d["oid_list"]
    notes = md["notes"]
    col_names = collection_names()
    if new_name in col_names:
        logger.error("Collection by that name already exist.")
        return False
    if delete_collection_by_cid(cid):
        return create_collection(new_name, oid_list, notes)
    create_collection(md["name"], oid_list, notes)
    return False


def get_cid_from_name(col_name):
    source_set_dict = get_set_names()
    for cid in source_set_dict:
        if source_set_dict[cid] == col_name:
            return cid
    return None


def get_cid_from_oid_list(oid_list):
    oid_list = list(set(oid_list)) # Assert uniqueness
    oid_list.sort() # Assert always in the same order
    oid_string = "".join(oid_list)
    cid = get_oid_from_data(oid_string.encode())
    return cid


def get_orphan_oids() -> List[str]:
    """
    Returns a set of oids not in any collection. If
    no such oids exist, an empty set is returned.
    """
    oids = retrieve_all_keys("file_meta")
    if not oids:
        return set()
    oids = set(oids)
    for cid in collection_cids():
        ids = get_field('collections', cid, 'oid_list')
        if ids:
            ids = set(ids)
            oids = oids - ids
    return oids


def get_set_names() -> dict:
    source_set_dict = {}
    for source_mod in modules_available["source"]:
            doc = documentation(source_mod)
            if doc["set"]: # Currently only source set is collections
                data = retrieve_all(source_mod)
                for oid in data:
                    source_set_dict[oid] = get_colname_from_oid(oid)
    return source_set_dict


def collection_names() -> List[str]:
    return list(get_set_names().values())


def collection_cids() -> List[str]:
    return list(get_set_names().keys())


def get_collection_info(col_name: str, view: str) -> dict:
    col_names = collection_names()
    result = {}
    if len(col_names) == 0:
        return result

    if not col_name in col_names:
        return result

    cid = get_cid_from_name(str(col_name))
    num_files = get_field("collections_meta", cid, "num_oids")
    notes = get_field("collections_meta", cid, "notes")
    result['name'] = col_name
    result['id'] = cid
    result['num_files'] = num_files
    result['notes'] = notes
    oid_list = None

    if view == 'all' or view == 'files':
        flist = []
        oid_list = get_field("collections", cid, "oid_list")
        for oid in oid_list:
            names = get_field("file_meta", oid, "names")
            flist.extend(names)
            flist.sort()
        result['files'] = flist

    if view == 'all' or view == 'oids':
        if not oid_list:
            oid_list = get_field("collections", cid, "oid_list")
        result['oid_list'] = oid_list

    if view == 'all' or view == 'memberships':
        cid = get_cid_from_name(col_name)
        oid_list = expand_oids(cid)
        exclude_cids = [ o for o in oid_list if exists("collections", o) ]
        cids = [ c for c in collection_cids() if c not in exclude_cids]
        results = {}
        for c in cids:
            this_oids = set(expand_oids(c))
            this_intersection = list(set(oid_list).intersection(this_oids))
            if this_intersection:
                results[c] = this_intersection

        result['memberships'] = {}
        for new_cid in results:
            if len(results[new_cid]) == 0:
                continue
            new_col_name = get_colname_from_oid(new_cid)
            result['memberships'][new_col_name] = []
            for oid in results[new_cid]:
                result['memberships'][new_col_name].append( (oid, list(get_names_from_oid(oid))) )

    return result


def get_file_info(file: str) -> None:
    oid_list = list(get_oids_with_name(file).keys())
    result = {}

    for oid in oid_list:
        mr = retrieve("membership", oid_list, {})
        col_names = []
        for cid in mr:
            col_name = get_colname_from_oid(cid)
            col_names.append(col_name)
        meta = retrieve("file_meta", oid, {})
        result[oid] = {'names': list(meta['names']), 'membership': col_names}
    return result


#-------  OID LOOKUP FUNCTIONS -------------------------------------------------------------------
def cleanup_oid_list(mod_name: str, oid_list: List[str]) -> List[str]:
    """ Sanitize oid_list and convert any oids necessary to insure that module's
        requirements are met.
    """
    # Handle single oids and lists both as lists.
    if isinstance(oid_list, str):
        oid_list = [oid_list]

    # If this is a source module, the oids won't have sources yet so other checks are pointless.
    module_type = get_mod_type(mod_name)
    if module_type in ["source"]:
        return oid_list

    # Make sure that we convert the oids into types that the module can handle.
    doc_dict = documentation(mod_name)
    if not doc_dict["set"]:
        oid_list = expand_oids(oid_list)
    if not doc_dict["atomic"]:
        for oid in oid_list:
            try:
                if source(oid) not in ["collections"]:
                    raise otypes.BadOIDList("Atomic OIDs passed to module that only handles sets")
            except otypes.OxideError:
                break
    return oid_list


def flatten_list(l: Iterable[Union[str, List, Tuple, Set, Dict]]) -> List[str]:
    """ Given a list containing lists, sets or tuples
        return a list of strings. Note: dicts are passed over and kept as dict
    """
    new_list = []
    for i in l:
        if isinstance(i, str):
           new_list.append(i)
        elif isinstance(i, (list, set, tuple)):
            new_list.extend(flatten_list(i))
        else:
            new_list.append(i)
    return new_list


def valid_oids(l: List[str]) -> Tuple[List[str], List[str]]:
    """ Given an interable object return the tuple (valid_oids, invalid_items)
    """
    l = flatten_list(l)
    valid = []
    invalid = []
    for i in l:
        try:
            if source(i):
                valid.append(i)
            else:
                invalid.append(i)
        except (otypes.OxideError, KeyError, AttributeError):
            invalid.append(i)
    return valid, invalid


def expand_oids(oids: Union[str, List[str]]) -> List[str]:
    """ Given a list of oids expand each collection id to the ids in that collection
    """
    if isinstance(oids, str):
        oids = [oids]

    new_oids = []
    for oid in oids:
        src = source(oid)
        if not src:
            logger.warning("Invalid OID to expand: %s", oid)
            continue
        if documentation(src)["set"]:
            col_dict = retrieve(src, oid, {})
            new_oids.extend(col_dict["oid_list"])
        else:
            new_oids.append(oid)
    return new_oids


def get_oids_with_name(some_name: str) -> Dict[str, str]:
    """ Given a name search all source modules that have the field 'names' for
        the given name. Return a dict of oid:source
    """
    logger.debug("Getting oids with the name: %s", some_name)
    oids = {}
    for s in modules_available["source"]:
        if "meta" in documentation(s):
            s = documentation(s)["meta"]
            keys = datastore.retrieve_all_keys(s)
            if not keys:
                continue
            for oid in keys:
                names = get_field(s, oid, "names")
                if some_name in names:
                    oids[oid] = s
    return oids


def get_colname_from_oid(oid: str) -> Set[str]:
    """ Given an oid for a collection search the source modules and return
        the name belonging to that oid
    """
    logger.debug("Getting name for collection oid:%s", oid)

    for s in modules_available["source"]:
        if s == "collections":
            s = "collections_meta"
        ds = datastore.retrieve(s,oid)
        if not ds or not isinstance(ds, dict):
            continue
        if "name" in ds:
            return ds["name"]

    return set()


def get_names_from_oid(oid: str) -> Set[str]:
    """ Given an oid search the source modules and return a set of names
        belonging to that oid
    """
    logger.debug("Getting names for oid:%s ", oid)

    s = source(oid)
    if "meta" in documentation(s):
        s = documentation(s)["meta"]
    names = get_field(s, oid, "names")
    if not names:
        names = get_field(s, oid, "name")
    if not names:
        names = set()

    return names


def load_reference(ref_name: str) -> Optional[bytes]:
    filename = os.path.join(config.dir_reference, ref_name)
    ref = sys_utils.read_object_from_file(filename)
    return ref


def get_available_modules(category: Optional[str] = 'all') -> List[str]:
    """ Fetch list of all modules that have `category` matches for.

        Defaults to "all" where all loaded are not fetched.
    """
    mod_list = []
    for mod_name in initialized_modules:
        mod_doc = documentation(mod_name)
        if (mod_doc and (category == 'all' or ('category' in mod_doc and mod_doc['category'] == category))):
            mod_list.append(mod_name)
    return mod_list


def wire_api():
    """ Updates api placeholder references to intended functionality
    """
    global scratch_dir
    global tag_filter
    global retrieve_all_keys
    global apply_tags
    global get_tags
    global tmp_file

    logger.debug("wire api")
    api.store     = store
    api.source    = source
    api.process   = process
    api.exists    = exists
    api.retrieve  = retrieve
    api.get_field = get_field

    api.expand_oids               = expand_oids
    api.get_oids_with_name        = get_oids_with_name
    api.get_colname_from_oid      = get_colname_from_oid
    api.delete_collection_by_cid  = delete_collection_by_cid
    api.delete_collection_by_name = delete_collection_by_name
    api.get_names_from_oid        = get_names_from_oid
    api.get_oid_from_data         = get_oid_from_data
    api.get_available_modules     = get_available_modules
    api.create_collection         = create_collection
    api.scratch_dir               = config.dir_scratch

    scratch_dir           = config.dir_scratch
    api.modules_dir       = config.dir_modules
    api.ida_path          = config.dir_ida_path
    api.ghidra_path       = config.dir_ghidra_path
    api.ghidra_path2       = config.dir_ghidra_path2
    api.ghidra_path3       = config.dir_ghidra_path3
    api.ghidra_path4       = config.dir_ghidra_path4
    api.ghidra_path5       = config.dir_ghidra_path5
    api.ghidra_project    = config.ghidra_project_project_name
    api.pharos_image      = config.pharos_docker_image
    api.probdisasm_image  = config.probdisasm_docker_image
    api.scripts_dir       = config.dir_scripts
    api.documentation     = documentation
    api.get_cid_from_name = get_cid_from_name
    api.modules_list      = modules_list
    api.import_file       = import_file
    api.import_directory  = import_directory

    retrieve_all_keys         = datastore.retrieve_all_keys
    api.retrieve_all_keys     = retrieve_all_keys
    api.apply_tags            = tags.apply_tags
    apply_tags                = tags.apply_tags
    api.get_tags              = tags.get_tags

    get_tags                  = tags.get_tags
    api.tag_filter            = tags.tag_filter
    tag_filter                = tags.tag_filter
    api.collection_names      = collection_names
    api.collection_cids       = collection_cids
    api.get_cid_from_oid_list = get_cid_from_oid_list
    api.get_orphan_oids       = get_orphan_oids
    api.valid_oids            = valid_oids
    api.flush_module          = flush_module
    api.flush_oid             = flush_oid

    api.local_store                = local_store
    api.local_retrieve             = local_retrieve
    api.local_exists               = local_exists
    api.local_available_data       = local_available_data
    api.local_retrieve_all         = local_retrieve_all
    api.local_count_records        = local_count_records
    api.local_delete_function_data = local_delete_function_data
    api.local_delete_data          = local_delete_data

    api.libraries_dir              = config.dir_libraries
    api.load_reference             = load_reference

    tmp_file                       = sys_utils.tmp_file
    api.tmp_file                   = sys_utils.tmp_file

    tags.api = api
    options.api = api


wire_api()
initialize_all_modules()
