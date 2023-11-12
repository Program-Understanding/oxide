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

""" ologger.py
"""
import os
import sys
import logging
import logging.handlers

try:
    from oxide.core import config
except ImportError as err:
    print("Import config failed!\n" + str(err))
    sys.exit(1)

LOG_FILE        = ".log.txt"

# Set the following in init()
log_file_fp     = None
logs_dir        = None
logging_level   = 0
verbosity_level = 0
console_handle  = None
file_handle     = None
max_log_size    = None
num_log_files   = None


def set_level_str(ltype: str, level: str) -> bool:
    """ For verbosity or logging level, get correct integer level and set logger
    """
    ltype = ltype.strip().lower()
    if ltype not in ["verbosity", "logging"]:
        logging.warning("Attempt to set logging with invalid type %s.", ltype)
        return False

    # If a string is passed in try to convert it
    if isinstance(level, str):
        if not (level.isdigit() or level.isalpha()):
            logging.warning("Attempt to set %s with invalid level %s ", ltype, level)
            return False

        if level.isdigit():
            level = int(level)
        if level.isalpha():
            level = level.upper()
            level = logging._nameToLevel.get(level)
            if level is None:
                logging.warning("Attempt to set %s with invalid level %s ", ltype, level)
                return False

    if not isinstance(level, int) or level < 0 or level > 100:
        logging.warning("Attempt to set %s with invalid level %s", ltype, level)
        return False

    return set_level(ltype, level)


def set_level(ltype: str, level: int) -> bool:
    """ Given an integer level, set logger between console and file loggers
    """
    global verbosity_level
    global logging_level

    if ltype in ["verbosity", "logging"]:
        if ltype == "verbosity":
            verbosity_level = level
            console_handle.setLevel(verbosity_level)

        if ltype == "logging":
            logging_level = level
            file_handle.setLevel(logging_level)

        logging.debug("Setting %s level to %s:%s", ltype, logging._levelToName.get(level), level)
        set_root_to_lowest_level()
        return True

    logging.debug("Failed to set %s level to %s:%s", ltype, logging._levelToName.get(level), level)
    return False


def set_root_to_lowest_level() -> None:
    """ Set the root logging to the lower level between logging and verbosity.
    """
    if logging_level and verbosity_level:
        logging.root.setLevel(min(logging_level, verbosity_level))
    elif logging_level:
        logging.root.setLevel(logging_level)
    elif verbosity_level:
        logging.root.setLevel(verbosity_level)
    else:
        logging.root.setLevel(logging.DEBUG)


def init() -> None:
    """ Initialize general and verbosity logging utilities
    """
    global LOG_FILE
    global logs_dir
    global file_handle
    global max_log_size
    global num_log_files
    global log_file_fp
    global verbosity_level
    global logging_level
    global console_handle

    logs_dir = config.dir_logs
    try:
        os.makedirs(logs_dir, exist_ok=True)
    except OSError:
        # Directory could not be created
        pass

    log_file_fp = os.path.join(logs_dir, LOG_FILE)

    # Remove default handler
    if len(logging.root.handlers) > 0:
        logging.root.removeHandler(logging.root.handlers[0])

    # Set up conole handler
    console_handle = logging.StreamHandler()
    verbosity_level = config.verbosity_level
    level_set = set_level_str("verbosity", verbosity_level)
    if not level_set:
        logging.error("Error in verbosity level: %s", verbosity_level)
        sys.exit(1)

    cformatter = logging.Formatter('  * %(name)s.%(levelname)s.%(lineno)s: %(message)s')
    console_handle.setFormatter(cformatter)
    # Prevent duplicate logging
    if logging.root.hasHandlers():
        logging.root.handlers.clear()
    logging.root.addHandler(console_handle)

    # Set up file handlers
    max_log_size = int(config.logging_max_log_size) * (1024 * 1024)
    num_log_files = int(config.logging_num_log_files)
    if config.logging_rotate:
        file_handle = logging.handlers.RotatingFileHandler(log_file_fp, maxBytes=5242880, backupCount=num_log_files)
    else:
        file_handle = logging.FileHandler(log_file_fp)

    logging_level = config.logging_level
    level_set = set_level_str("logging", logging_level)
    if not level_set:
        logging.error("Error in logging level: {}".format(logging_level))
        sys.exit(1)

    fformatter = logging.Formatter('%(asctime)s %(levelname)-5s %(name)s:%(lineno)-4s %(message)s')
    file_handle.setFormatter(fformatter)
    logging.root.addHandler(file_handle)
