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

""" config.py
"""
import os
import sys
import logging
import configparser

from core import sys_utils
from core.otypes import cast_string, convert_logging_level

from typing import Dict, Optional

NAME = "config"
logger = logging.getLogger(NAME)

dir_root = sys_utils.ROOT_DIR
dir_oxide = sys_utils.OXIDE_DIR

config_file = ".config.txt"
config_file_fp = os.path.join(dir_root, config_file)

# Global config defaults will be used when a new config is created or if a section is missing
# Global vars are section_option
dir_defaults = {"root"          : dir_root,
                "oxide"         : dir_oxide,
                "libraries"     : os.path.join(dir_oxide, "libraries"),
                "modules"       : os.path.join(dir_root, "modules"),
                "datasets"      : os.path.join(dir_root, "datasets"),
                "datastore"     : os.path.join(dir_root, "db"),
                "localstore"    : os.path.join(dir_root, "localstore"),
                "logs"          : dir_root,
                "reference"     : os.path.join(dir_root, "reference"),
                "scratch"       : os.path.join(dir_root, "scratch"),
                "sample_dataset": os.path.join(dir_root, "datasets", "sample_dataset"),
                "ghidra_path"   : "",
                "ghidra_path2"   : "",
                "ghidra_path3"   : "",
                "ghidra_path4"   : "",
                "ghidra_path5"   : "",
                "ida_path"      : "",
                "ghidra_project": os.path.join(dir_root, "scratch"),
                "scripts"       : os.path.join(dir_root, "scripts")
                }

logging_defaults = {"level": "INFO",
                    "rotate": "False",
                    "max_log_size": "10",
                    "num_log_files": "5"}

verbosity_defaults = {"level": "INFO"}

multiproc_defaults = {"on": "False",
                      "max": "3"}

file_defaults = {"max": "1048576",
                 "process_unrecognized_formats": "false"}

distributed_defaults = {"port": "8000",
                        "compute_nodes": "localhost"}

dev_mode = {"enable": "True"}

django = {"ip": "0.0.0.0",
          "port": "8888"}

ghidra_project = {"project_name": "ghidraBenchmarking"}

pharos = {"docker_image": ""}
probdisasm = {"docker_image": ""}

plugins = {"default": "True"}

history = {"file": ".history.txt",
           "max": "200"}

ALL_DEFAULTS = {"dir"            : dir_defaults,
                "logging"        : logging_defaults,
                "verbosity"      : verbosity_defaults,
                "multiproc"      : multiproc_defaults,
                "file"           : file_defaults,
                "distributed"    : distributed_defaults,
                "dev_mode"       : dev_mode,
                "django"         : django,
                "plugins"        : plugins,
                "history"        : history,
                "ghidra_project" : ghidra_project,
                "pharos"         : pharos,
                "probdisasm"     : probdisasm
                }

rcp = configparser.ConfigParser()
config_changed = False
setup_run = False


def config_menu(section: str = "all") -> bool:
    """
    globals:
        rcp: ConfigParser
    """

    if section == "all":
        sections = rcp.sections()
    elif section not in rcp.sections():
        print(" - Section {} not found".format(section))
        return False
    else:
        sections = [section]

    r = input(" - Set all to defaults (Y/n): ").strip().lower()
    if r != 'n':
        set_config_all_to_defaults()
        return True

    print(" - <Enter> to leave value unchanged ")
    print(" - d to use default value")
    print(" - q to abort all changes")
    print(" - c to leave the rest unchanged")
    print()
    print(" [section]")
    print(" <option> = <cur_val>    <default>")
    print()

    for config_section in sections:
        print(" [{}]".format(config_section))
        for option in ALL_DEFAULTS[config_section]:
            cval = rcp.get(config_section, option)
            dval = ALL_DEFAULTS[config_section][option]
            if str(cval).lower() != str(dval).lower():
                print("   {} = {}    <{}>".format(option, cval, dval))
            else:
                print("   {} = {}".format(option, cval))
            nval = input("   > ").strip().lower()
            if nval == "":
                continue

            if nval == 'c':
                return True

            if nval == 'd':
                set_value(config_section, option, dval)
            elif nval == 'q':
                return False
            else:
                set_value(config_section, option, nval)
    return True


def setup(section: str = "all", initial_setup: bool = False) -> None:
    """ Set up or change config
    """
    global setup_run
    if setup_run:
        return

    if not initial_setup:
        r = input(" - Change config (Y/n): ").strip().lower()
        if r == 'n':
            return
    else:
        print(" - Initial setup")
        set_config_all_to_defaults()

    if not config_menu(section):
        print(" - Aborting all changes to config")
        sys.exit(1)
    r = input(" - Write changes to config file (Y/n): ").strip().lower()
    if r != 'n':
        print(" - Writing changes to config file", config_file)
        write_config_file()
    else:
        print(" - Aborting all changes to config")
        sys.exit(1)

    setup_run = True


def init() -> None:
    global config_changed
    global config_file_fp

    # Check if the config file exists. If not create it using defaults
    if not os.path.isfile(config_file_fp):
        setup(section="all", initial_setup=True)

    read_config_file()
    set_globals()
    sanity_check()

    if config_changed:
        set_globals()
        write_config_file()


def sanity_check() -> None:
    """ Validate root and oxide directories valid in configuration
    """
    validate_dir_root()
    validate_dir_oxide()


def validate_dir_root() -> None:
    """ Asserting that root dir in the config is valid for this environment.
    """
    global dir_root
    global config_changed

    logger.debug("Asserting that root dir in the config is valid for this environment.")
    if os.path.realpath(dir_root) != os.path.realpath(sys_utils.ROOT_DIR):
        logger.warning("root dir in config invalid for this environment, resetting")
        dir_root = sys_utils.ROOT_DIR
        set_value("dir", "root", dir_root)
        config_changed = True


def validate_dir_oxide() -> None:
    """ Asserting that oxide dir in the config is valid for this environment.
    """
    logger.debug("Asserting that root dir in the config is valid for this environment.")
    global dir_oxide
    global config_changed
    if os.path.realpath(dir_oxide) != os.path.realpath(sys_utils.OXIDE_DIR):
        logger.warning("oxide dir in config invalid for this environment, resetting")
        dir_oxide = sys_utils.OXIDE_DIR
        set_value("dir", "oxide", dir_oxide)
        config_changed = True


def read_config(fd) -> None:
    """ Reads the configuration in the file referenced by fd.
        the global config_file string variable is only used in error handling
    globals:
        RCP: ConfigParser
    """
    global rcp
    global config_file_fp
    try:
        rcp.read_file(fd, config_file_fp)
    except IOError as e:
        logger.error("ConfigParse exception:%s", e)


def read_config_file() -> bool:
    """ This function opens a file based on the global config_file string and calls
        read_config to actually read the configuration in.
    """
    global config_file_fp
    global logger
    logger.debug("Reading config file %s", config_file_fp)
    try:
        fd = open(config_file_fp, "r")
        read_config(fd)
        fd.close()
        return True
    except IOError:
        logger.error("Unable to read config file %s", config_file_fp)
        return False


def set_config_all_to_defaults() -> None:
    """ Iterate over the defaults and set the according values
    """
    global config_changed
    global logger
    logger.debug("Creating default config")
    for section in ALL_DEFAULTS:
        set_config_section_to_defaults(section)
    config_changed = True


def set_config_section_to_defaults(section: str) -> None:
    global rcp
    global config_changed
    if not rcp.has_section(section):
        rcp.add_section(section)
    for option in ALL_DEFAULTS[section]:
        set_config_option_to_default(section, option)
    config_changed = True


def set_config_option_to_default(section: str, option: str) -> None:
    global config_changed
    rcp.set(section, option, ALL_DEFAULTS[section][option])
    config_changed = True


def set_global_option(section: str, option: str, value: str) -> None:
    var = section + "_" + option
    value = cast_string(value)
    globals()[var] = value


def get_value_or_set_to_default(section: str, option: str) -> str:
    try:
        value = rcp.get(section, option)
        if value == "":
            # if default is also "", ignore
            if ALL_DEFAULTS[section][option] == "":
                return value

            logger.warning(" Empty config option %s in section %s - setting to default", option, section)
            set_config_option_to_default(section, option)
    except configparser.NoOptionError:
        logger.warning(" Missing or new config option %s in section %s - setting to default", option, section)
        set_config_option_to_default(section, option)
        value = rcp.get(section, option)  # TODO:: does this need try/catch
    return value


def set_globals() -> bool:
    """ If possible, use values from config file otherwise use defaults
        global variables are section_option
    """
    global rcp
    global logger
    global config_changed
    logger.debug("Setting globals in config")
    for section in ALL_DEFAULTS:
        if not rcp.has_section(section):
            set_config_section_to_defaults(section)
            config_changed = True
        for option in ALL_DEFAULTS[section]:
            value = get_value_or_set_to_default(section, option)
            set_global_option(section, option, value)
    return True


def set_value(section: str, option: str, value: str) -> None:
    """ This function sets an option in the config
        file but leaves the other values the same.
    """
    global rcp
    global config_changed
    if not rcp.has_section(section):
        rcp.add_section(section)
    rcp.set(section, option, value)
    config_changed = True


def write_config_file(new_config_file: str = None) -> None:
    """ This function opens a file based on the global config_file string and writes the
        current configuration out to it.
    """
    global config_file
    global config_file_fp
    global rcp

    if new_config_file:
        config_file = new_config_file
        config_file_fp = os.path.join(dir_root, config_file)

    logger.debug("Writing config to %s", config_file_fp)
    try:
        fd = open(config_file_fp, "w")
        rcp.write(fd)
        fd.close()
    except IOError as err:
        logger.error("Unable to write config file %s", config_file_fp)
        logger.error(str(err))


def get_logging_level() -> Optional[int]:
    """ Return the logging level from the config
    """
    try:
        level = rcp.get("logging", "level").upper()
        res = convert_logging_level(level)
    except configparser.NoOptionError:
        logger.warning("[logging] section of the config malformed.")
        res = None
    return res


def get_verbosity_level():
    """ Return the verbosity level from the config
    """
    try:
        level = rcp.get("verbosity", "level").upper()
        return convert_logging_level(level)
    except configparser.NoOptionError:
        logger.warning("[verbosity] section of the config malformed.")
        return None


def get_section(section: str) -> Dict[str, str]:
    sdict = {}
    for option in rcp.options(section):
        sdict[option] = rcp.get(section, option)
    return sdict


def get_all() -> Dict[str, str]:
    """ Return a dictionary of dictionaries with the sections, options and values
    """
    global rcp
    cdict = {}
    for section in rcp.sections():
        cdict[section] = get_section(section)
    return cdict


def get_value(section: str, option: str) -> Optional[str]:
    """ Given a section and an option return the value
    """
    global rcp
    try:
        value = rcp.get(section, option)
        res = value
    except configparser.NoOptionError:
        logger.error("Tried to retrieve nonexistant value from config (%s:%s).", section, option)
        res = None
    return res


init()
