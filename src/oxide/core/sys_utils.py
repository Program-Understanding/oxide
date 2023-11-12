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

""" sys_utils.py
"""

import os
import sys
import pickle
import marshal
import zlib
import logging
import xmlrpc.client
import subprocess
import time
import tempfile

from oxide.core import api

from typing import Optional, Dict, Any, List


NAME      = "sys_utils"
logger    = logging.getLogger(NAME)

PWD       = os.path.split(__file__)[0]
OXIDE_DIR = os.path.abspath(PWD)
ROOT_DIR  = os.path.split(PWD)[0]
FILES_NOT_IMPORTED = [".DS_Store", ".gitignore"]  # Files to ignore on import
os.umask(0000)  # Needed for file/directory creation


# ------------------------------ File related functions ------------------------------------
def import_file(file_location: str, max_file_size: int) -> Optional[Dict[str, Any]]:
    logger.debug("Importing file %s", file_location)

    if os.path.basename(file_location) in FILES_NOT_IMPORTED:
        logger.debug("Skipping the import of file: %s", file_location)
        return None

    if not os.path.isfile(file_location):
        logger.error("%s file does not exist.", file_location)
        return None

    if not os.access(file_location, os.R_OK):
        logger.error("%s file is not accessable.", file_location)
        return None

    file_stat = get_file_stat(file_location)
    if not file_stat:
        logger.error("Cannot stat file %s.", file_location)
        return None

    filesize = os.path.getsize(file_location) / 1048576.
    if filesize > max_file_size or filesize == 0:
        logger.error("File size %dM exceeds max filesize %dM or is 0, (%s)", filesize, max_file_size, file_location)
        return None

    logger.debug("File import size %dM", filesize)
    data = get_contents_of_file(file_location)
    file_data = {"file_stat": file_stat, "size": filesize, "data": data}
    return file_data


def delete_file(file_location: str) -> bool:
    if not os.path.isfile(file_location):
        logger.error("File does not exist:%s", file_location)
        return False

    try:
        os.remove(file_location)
        return True
    except OSError:
        logger.error("Cannot remove file:%s", file_location)
        return False


def get_file_stat(file_location: str) -> Optional[Dict[str, Any]]:
    if not os.path.isfile(file_location):
        if os.path.islink(file_location):
            logger.warning("Skipping import of link:%s", file_location)
        else:
            logger.warning("File does not exist:%s", file_location)
        return None

    try:
        file_stat = os.stat(file_location)
    except OSError:
        logger.error("Cannot stat file:%s", file_location)
        return None

    fs_dict = {"atime": file_stat.st_atime,
               "mtime": file_stat.st_mtime,
               "ctime": file_stat.st_ctime,
               "size": file_stat.st_size,
               }
    return fs_dict


def get_contents_of_file(file_location: str) -> Optional[bytes]:
    """ Given the location of a file return the contents or None if an error
        occurs.
    """
    try:
        with open(file_location, 'rb') as fd:
            data = fd.read()
    except IOError as err:
        logger.error("IOError: %s", str(err))
        return None
    return data


def read_object_from_file(filename: str) -> Optional[bytes]:
    """ Reads Python object from file by first uncompressing, unpickling, then returning results.
    """
    if not os.path.isfile(filename):
        logger.error("%s does not exist.", filename)
        return None

    # Open and read file
    try:
        with open(filename, 'rb') as fd:
            data = fd.read()
    except IOError as err:
        logger.error("IOError:%s", err)
        return None

    # Attempt decompression
    try:
        udata = zlib.decompress(data)
    except zlib.error:
        # file was not compressed
        udata = data

    # Unpickle file
    try:
        data = pickle.loads(udata)
    except pickle.UnpicklingError as err:
        logger.error("UnpicklingError:%s", err)
        return None
    except AttributeError as err:
        logger.error("AttributeError:%s, Try clearning database of offending pickle", err)
        return None
    return data


def write_object_to_file(filename: str, data: bytes) -> bool:
    """ Writes Python object to file by first pickling, compressing, then writing results.
    """
    # Open output file for writing
    try:
        fd = open(filename, 'wb')
    except OSError:
        logger.error('Error opening file for writing %s', filename)
        return False

    # Pickle data for serialization
    try:
        data = pickle.dumps(data, pickle.HIGHEST_PROTOCOL)
    except pickle.PicklingError as err:
        # Error pickling large file
        logger.error("PicklingError:%s", err)
        return False

    # Compress data to speed up writing
    try:
        data = zlib.compress(data, zlib.Z_BEST_SPEED)
    except OverflowError:
        # happens because zlib uses 32-bit ints, when data more than 2gb, revert to pickle data
        pass

    try:
        fd.write(data)
        fd.close()
        logger.debug("Data stored to %s", filename)
        return True
    except IOError as err:
        logger.error("IOError:%s", err)
        return False


def get_files_from_directory(directory: str) -> Optional[List[str]]:
    """ Given the name of a directory return a list of the fullpath files in the
        given directory and subdirectories
    """
    if not os.path.isdir(directory):
        return None
    if not os.access(directory, os.R_OK | os.X_OK):
        logger.error("%s directory is not accessable.", directory)
        return None

    fullpath_files = []
    for (path, _, files) in os.walk(directory):
        for fd in files:
            fullpath = os.path.join(path, fd)
            fullpath_files.append(fullpath)

    return fullpath_files


def ensure_dir_exists(directory: str) -> str:
    """ If directory does not exist create it.
    """
    if not directory:
        logger.debug("No path provided (%s)", directory)
        return False

    if not os.path.isdir(directory) and not os.path.islink(directory):
        logger.debug("Creating directory %s", directory)
        try:
            os.makedirs(directory, mode=0o777)
        except OSError:
            logger.debug("Directory already exists %s", directory)
    return True


# --------------------------------- Networking related functions ---------------------------
def pack(data: bytes) -> Optional[bytes]:
    try:
        data = pickle.dumps(data)
        data = zlib.compress(data, zlib.Z_BEST_SPEED)
        return xmlrpc.client.Binary(data)
    except MemoryError:
        logger.error("Not able to pack data")
        return None


# FIXME:: zlib exception handling for these 3 functions
def unpack(data: bytes) -> Optional[bytes]:
    if not data:
        return None

    try:
        data = data.data
        data = zlib.decompress(data)
        return pickle.loads(data)
    except MemoryError:
        logger.error("Not able to unpack data using cPickle.")
        return None
    except AttributeError:
        logger.error("AttributeError, try deleting offending pickle data.")
        return None


def pack_file(data):
    try:
        data = marshal.dumps(data)
        data = zlib.compress(data, zlib.Z_BEST_SPEED)
        return xmlrpc.client.Binary(data)
    except MemoryError:
        logger.error("Not able to pack file data")
        return None


def unpack_file(data) -> Optional[Any]:
    try:
        if not data:
            return None
        data = data.data
        data = zlib.decompress(data)
        return marshal.loads(data)
    except MemoryError:
        logger.error("Not able to unpack file data using cPickle.")
        return None


# ------------------------------------Print/Log/Setup support functions --------------------
def which(program: str) -> Optional[str]:
    def is_exe(fpath) -> bool:
        return os.path.exists(fpath) and os.access(fpath, os.X_OK)

    fpath, _ = os.path.split(program)
    if fpath:
        if is_exe(program):
            return program
    else:
        for path in os.environ["PATH"].split(os.pathsep):
            exe_file = os.path.join(path, program)
            if is_exe(exe_file):
                return exe_file

    return None


def msg(s) -> None:
    print(s, file=sys.stderr)
    return


def error(s) -> None:
    print(s, file=sys.stderr)
    sys.exit(1)


def log(h: str, subproc: str, output: bool, log_name: str = "output.log", cwd: str = None) -> bool:
    """ Given process to run, run and print whether subprocess completed successfully or not,
        and possibly log runtime to file
    """
    with open(log_name, "a") as log_fd:
        print(h, end="")

        if output:
            proc = subprocess.Popen(subproc, shell=True)
        else:
            if cwd:
                proc = subprocess.Popen(subproc, shell=True, stdout=log_fd, stderr=log_fd, cwd=cwd)
            else:
                proc = subprocess.Popen(subproc, shell=True, stdout=log_fd, stderr=log_fd)

        while proc.poll() is None:
            print('.', end='')
            time.sleep(1)

        if proc.returncode == 0:
            msg("success!")
            res = True
        else:
            msg("fail!")
            res = False
    return res


def query(question: str, default: str = "yes") -> bool:
    """Ask a yes/no question via raw_input() and return their answer.
    """

    valid = {"yes": True, "ye": True, "y": True, "no": False, "n": False}

    # Configure prompt with proper default option
    if default is None:
        prompt = " [y/n] "
    elif default == "yes":
        prompt = " [Y/n] "
    elif default == "no":
        prompt = " [y/N] "
    else:
        raise ValueError("invalid default answer: '{}'".format(default))

    # Continue to ask until receieved answer is valid
    while True:
        print(question + prompt, end="")
        choice = input().lower()
        if default and not choice:
            return valid[default]

        if choice in valid:
            return valid[choice]

        print("Please respond with 'yes' or 'no' (or 'y' or 'n').")


# ------------------------------- Tempfile support functions -------------------------------
def tmp_file(name: str, data: bytes, empty: bool = False, override: bool = False) -> Optional[str]:
    """ Given a file name and data uses the Python tempfile package to write the file to
        the scratch directory.
    """
    if not data and not empty:
        return None

    fname = os.path.basename(name)
    tmp = os.path.join(api.scratch_dir, fname)

    # Overwrite or create new file with new prefix
    if os.path.exists(tmp):
        if override:
            os.remove(tmp)
        else:
            tmp = tempfile.mktemp(prefix=fname, dir=api.scratch_dir)

    try:
        if not empty:
            fd = open(tmp, 'wb')
            fd.write(data)
            fd.close()
    except OSError:
        return None

    return tmp


def tmp_dir(name: str, create: bool = True) -> str:
    """ Given a dir name uses the Python tempfile package to write the dir to
        the scratch directory.
    """
    dirname = os.path.basename(name)
    tmp = os.path.join(api.scratch_dir, dirname)

    if os.path.exists(tmp):
        tmp = tempfile.mktemp(prefix=dirname, dir=api.scratch_dir)

    return tmp
