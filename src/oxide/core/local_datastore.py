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
import logging

from oxide.core import config, sys_utils

from typing import Dict, Optional, List

NAME = "localstore"
logger = logging.getLogger(NAME)

LOCALSTORE_DIR = config.dir_localstore
sys_utils.ensure_dir_exists(LOCALSTORE_DIR)


def local_store(plugin_name: str, data_name: str, data: bytes) -> bool:
    """ Write data for data_name to local file system
    """
    plugin_dir = os.path.join(LOCALSTORE_DIR, plugin_name)
    sys_utils.ensure_dir_exists(plugin_dir)
    filename = os.path.join(plugin_dir, data_name)
    logger.debug("Storing data at %s", filename)
    if not sys_utils.write_object_to_file(filename, data):
        logger.error("Not able to store data at %s", filename)
        return False
    return True


def local_exists(plugin_name: str, data_name: str) -> bool:
    """ Determine whether file exists on local file system
    """
    plugin_dir = os.path.join(LOCALSTORE_DIR, plugin_name)
    if not os.path.isdir(plugin_dir):
        return False
    filename = os.path.join(plugin_dir, data_name)
    logger.debug("Determining if data exists at %s", filename)
    if os.path.isdir(filename):
        logger.warning("File exists as a directory!!! %s", filename)
        return False
    return os.path.isfile(filename)


def local_retrieve(plugin_name: str, data_name: str) -> Optional[bytes]:
    plugin_dir = os.path.join(LOCALSTORE_DIR, plugin_name)
    if not local_exists(plugin_name, data_name):
        return None

    filename = os.path.join(plugin_dir, data_name)
    data = sys_utils.read_object_from_file(filename)
    if data is None:
        logger.error("Not able to retrieve data at %s", filename)
        return None
    return data


def local_retrieve_recent(plugin_name: str) -> Optional[bytes]:
    plugin_dir = os.path.join(LOCALSTORE_DIR, plugin_name)
    files = sys_utils.get_files_from_directory(plugin_dir)

    best = (None, 0)
    for f in files:
        if os.path.getmtime(f) > best[1]:
            best = (f, os.path.getmtime(f))

    data = sys_utils.read_object_from_file(best[0])
    if data is None:
        logger.error("Not able to retrieve data at %s", best[0])
        return None
    return data


def local_available_data(plugin_name: str) -> List[str]:
    plugin_dir = os.path.join(LOCALSTORE_DIR, plugin_name)
    files = sys_utils.get_files_from_directory(plugin_dir)
    data_names = []
    if not files:
        return data_names
    for f in files:
        data_names.append(f)
    return data_names


def local_retrieve_all(plugin_name: str) -> Dict[str, bytes]:
    plugin_dir = os.path.join(LOCALSTORE_DIR, plugin_name)
    files = sys_utils.get_files_from_directory(plugin_dir)

    results = {}
    if not files:
        return results

    for f in files:
        data_name = os.path.basename(f)
        data = sys_utils.read_object_from_file(f)
        results[data_name] = data

    return results


def local_count_records(plugin_name: str) -> int:
    """ Count number of records in plugin dir.
    """
    plugin_dir = os.path.join(LOCALSTORE_DIR, plugin_name)
    if not os.path.isdir(plugin_dir):
        return 0
    logger.debug("Determining number of items in %s", plugin_dir)
    return len(os.listdir(plugin_dir))


# TODO:: Revist these
def local_delete_function_data(plugin_name: str) -> bool:
    """ Remove all stored data for a given module.
    """
    # FIXME:: does not exist
    files = local_retrieve_all(plugin_name).keys()
    if not files:
        return True
    for fname in files:
        fullpath = os.path.join(LOCALSTORE_DIR, plugin_name, fname)
        sys_utils.delete_file(fullpath)
    return True


def local_delete_data(plugin_name: str, data_name: str) -> bool:
    """ Given an oid and the name of a module, remove the data for that
        combination if it exists.
    """
    # FIXME:: Does not exist
    files = local_retrieve_all(plugin_name).keys()
    if not files:
        return True
    for fname in files:
        if fname != data_name:
            continue
        fullpath = os.path.join(LOCALSTORE_DIR, plugin_name, fname)
        sys_utils.delete_file(fullpath)
    return True
