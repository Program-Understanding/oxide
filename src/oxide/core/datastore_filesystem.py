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
import shutil
import pickle
import logging
import time
import errno
from glob import glob

from oxide.core import sys_utils, config, api, ologger
from oxide.core.options import build_suffix
from oxide.core.options import parse_suffix

from typing import Dict, List, Any, Optional, Tuple


NAME = "ds_filesystem"
logger = logging.getLogger(NAME)

datastore_dir = config.dir_datastore
sys_utils.ensure_dir_exists(datastore_dir)
scratch_dir = config.dir_scratch
sys_utils.ensure_dir_exists(scratch_dir)

COMPONENT_DELIM = '.'  # separates oid from mangle opts


# ------------------------------- MAIN FUNCTIONS -------------------------------------------------

def store(mod_name: str, oid: str, data: bytes, opts: dict, block: bool = True) -> bool:
    mod_dir = get_mod_dir(mod_name)
    sys_utils.ensure_dir_exists(mod_dir)

    acquire_file_lock(mod_name, oid, opts, write=True)

    tempfile = os.path.join(datastore_dir, "TMP{}{}".format(os.getpid(), mod_name))
    filename = get_fullpath(mod_dir, mod_name, oid, opts)
    logger.debug("Storing data at %s", filename)

    return_val = True

    if not sys_utils.write_object_to_file(tempfile, data):
        logger.error("Not able to store data at %s", filename)
        return_val = False
    try:
        os.replace(tempfile, filename)
    except OSError:
        logger.error("Not able to replace tempfile (%s)", filename)
        return_val = False
    logger.debug("Releasing " + filename)
    release_file_lock(mod_name, oid, opts)

    return return_val


def available_data(mod_name: str) -> List[Tuple[str, Dict[str, Any]]]:
    """
    Returns list of (oid, option) pairs
    """

    mod_dir = get_mod_dir(mod_name)
    files = sys_utils.get_files_from_directory(mod_dir)
    data = list()

    if not files:
        # if no oid data for module, empty list
        return list()

    for f in files:
        base = os.path.basename(f)
        components = base.split(COMPONENT_DELIM, 1)

        if len(components) == 1:
            # no options present
            oid = components[0]
            opts = {}
        else:
            # len must be 2 (assumed)
            oid, suffix = components
            opts = parse_suffix(mod_name, suffix)

        data.append([oid, opts])

    return data


def retrieve_all(mod_name: str) -> Dict[str, Any]:
    mod_dir = get_mod_dir(mod_name)
    files = sys_utils.get_files_from_directory(mod_dir)
    results = {}
    if not files:
        return results

    for f in files:
        data = sys_utils.read_object_from_file(f)
        mangled_name = os.path.basename(f)
        results[mangled_name] = data

    return results


def retrieve_all_keys(mod_name: str) -> Optional[List[str]]:
    mod_dir = get_mod_dir(mod_name)
    files = sys_utils.get_files_from_directory(mod_dir)
    if not files:
        return None

    return [os.path.basename(f) for f in files]


def retrieve_lock(mod_name: str, oid: str, opts: dict):
    return retrieve(mod_name, oid, opts, lock=True)


def retrieve(mod_name: str, oid: str, opts: dict = {}, lock: bool = False) -> Optional[Any]:
    mod_dir = get_mod_dir(mod_name)
    if not exists(mod_name, oid, opts):
        return None

    filename = get_fullpath(mod_dir, mod_name, oid, opts)
    acquire_file_lock(mod_name, oid, opts, write=lock)

    data = sys_utils.read_object_from_file(filename)

    if not lock:
        release_file_lock(mod_name, oid, opts)

    if data is None:
        logger.error("Not able to retrieve data at %s", filename)
        return None

    return data


def count_records(mod_name: str) -> int:
    mod_dir = get_mod_dir(mod_name)
    if not os.path.isdir(mod_dir):
        return 0

    logger.debug("Determining number of items in %s", mod_dir)
    return len(os.listdir(mod_dir))


def exists(mod_name: str, oid: str, opts: dict = {}) -> bool:
    if not isinstance(oid, str):
        logger.warning("Passed a non-string OID to exists.")
        return False
    os.listdir(datastore_dir) # NFS weirdness
    mod_dir = get_mod_dir(mod_name)
    if not os.path.isdir(mod_dir):
        return False
    filename = get_fullpath(mod_dir, mod_name, oid, opts)
    logger.debug("Determining if data exists at %s", filename)
    return os.path.isfile(filename)


def delete_module_data(mod_name: str) -> bool:
    """ Remove all stored data for a given module
    """
    files = retrieve_all_keys(mod_name)
    if not files:
        return True
    for fname in files:
        fullpath = os.path.join(datastore_dir, mod_name, fname)
        sys_utils.delete_file(fullpath)
    return True


def delete_oid_data(mod_name: str, oid: str) -> bool:
    """ Given an oid and the name of a module, remove the data for that
        combination if it exists.
    """
    files = retrieve_all_keys(mod_name)
    if not files:
        return True
    for fname in files:
        if fname.startswith(oid):
            fullpath = os.path.join(datastore_dir, mod_name, fname)
            sys_utils.delete_file(fullpath)
    return True


def get_fullpath(mod_dir: str, mod_name: str, oid: str, opts: dict = {}) -> str:
    suffix = build_suffix(mod_name, opts)
    if suffix:
        store_name = COMPONENT_DELIM.join([oid, suffix])
    else:
        store_name = oid
    filename_fp = os.path.join(mod_dir, store_name)
    return filename_fp


def get_mod_dir(mod_name: str) -> str:
    return os.path.join(datastore_dir, mod_name)


def get_lockfilename(modname: str, oid: str, opts) -> Tuple[str, str]:
    lockid = "{}_{}_{}".format(oid, build_suffix(modname, opts), modname)
    return lockid, os.path.join(datastore_dir,  lockid + ".lock")


# ---------------LOCK FILE FUNCTIONS -------------------------------------------------------------
""" These could go in sys_utils, but then there's a circular reference problem
    has lock file ids as keys, with these subkeys:
    fp => file pointer/descriptor
    mod => module needing lock
    oid => oid needing lock
    opts => options of  analysis needing lock
    suffix => suffix of analysis needing lock (derived from mod,opts)
    name => filename of the lockfile
"""
locked_files = dict()


def acquire_file_lock(modname: str, oid: str, opts: dict, write: bool = False,
                      delay: int = 1, timeout: int = 10) -> None:
    lockid, lockfile = get_lockfilename(modname, oid, opts)
    logger.debug("Locking %s", lockfile)
    suffix = build_suffix(modname, opts)

    start_time = time.time()
    while True:

        # Since during processing the lockfile name might change and yet fail
        # to open, get the lockfile fresh every iteration of the loop.
        lockid, lockfile = get_lockfilename(modname, oid, opts)
        try:

            # If we have the lock already.  Just return.
            if lockid in locked_files:
                break

            # If someone else is writing, we need to wait.
            if not os.path.isfile(lockfile+".write"):

                other_read_locks = glob(lockfile+"*")
                # If someone else is reading...
                if other_read_locks:

                    # If we want to write, we need to wait
                    if write:
                        break

                    # For reading, get the next read lock
                    lockfile = lockfile + "." + \
                        str(max([int(s.rsplit('.',1)[-1]) for s in other_read_locks])+1)

                # No one else is reading or writing
                else:
                    if write:
                        lockfile = lockfile + ".write"
                    else:
                        lockfile = lockfile + ".0"

                fp = os.open(lockfile, os.O_CREAT|os.O_EXCL|os.O_RDWR)
                # if we get here, we've got the lock
                locked_files[lockid] = dict(fp=fp, mod=modname, oid=oid, suffix=suffix, name=lockfile)
                break

        except OSError as e:
            if e.errno != errno.EEXIST:
                logger.error("Unexpected os error trying to get lockfile %s.", lockfile)
                print("failed:", e)
                raise
            elif (time.time() - start_time) >= timeout:
                logger.error("File locking timeout on lockfile %s.", lockfile)
                print("failed:", e)
                raise
        time.sleep(delay)


def release_file_lock(modname: str, oid: str, opts: dict) -> None:
    lockid, lockfile = get_lockfilename(modname, oid, opts)
    logger.debug("Releasing lock file %s", lockid)

    if lockid in locked_files:
        try:
            os.close(locked_files[lockid]['fp'])
            os.unlink(locked_files[lockid]['name'])
            del locked_files[lockid]
        except OSError as e:
            logger.error("Unexpected os error trying to get lockfile %s.", lockfile)
            print("failed:", e)


def cleanup_state() -> None:
    """ TODO::Not implemented.
    """
    return True


def cleanup() -> None:
    """
    Purge lingering lockfiles. This function can be used as part of a signal
    handler.
    TODO:: replace body of loop with release_file_lock?
    """
    for lockid in list(locked_files.keys()):
        try:
            logger.info("Releasing lock file %s PID %d", lockid, os.getpid())
            os.close(locked_files[lockid]['fp'])
            os.unlink(locked_files[lockid]['name'])
            del locked_files[lockid]
        except OSError as e:
            logger.error("Unexpected os error trying to get lockfile %s.", lockfile)
            print("failed:", e)


def register_process() -> None:
    """
    Called through Pool()'s initializer kw.
    """
    pass
