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
from pathlib import Path
import shutil

from oxide.core import sys_utils
from oxide.core import user_directories
from oxide.core.otypes import cast_string, convert_logging_level
from oxide.core.user_directories import get_win_path_environ, get_win_path_registry, get_win_path_jna, get_win_path_ctypes

from typing import Dict, Optional


NAME = "config"
logger = logging.getLogger(NAME)

AUTHOR = "ProgramUnderstandingLab"
APPLICATION = "oxide"

dir_root = Path(sys_utils.ROOT_DIR).absolute()
dir_oxide = Path(sys_utils.OXIDE_DIR).absolute()

# Filename and path for configuration
CONFIG_FILE = ".config.txt"
CONFIG_FILE_PATH = None  # Update in set_application_directories

# Directory for data files
DATA_DIRECTORY = None  # Update in set_application_directories

# Global config defaults will be used when a new config is created or if a section is missing
# Global vars are section_option
# This is updated in the init function, when system preferred directories are identified
DIR_DEFAULTS = None

interface_defaults = {"page_size": "0",  # Pagination, None disables all pagination of output, 48 is a good default value
                      }

logging_defaults = {"level": "INFO",
                    "rotate": "false",
                    "max_log_size": "10",
                    "num_log_files": "5"}

datastore_defaults = { "datastore": "filesystem",
                       "serialization": "pickle"
}

verbosity_defaults = {"level": "INFO"}

multiproc_defaults = {"on": "false",
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

ALL_DEFAULTS = {"dir"            : DIR_DEFAULTS,
                "interface"      : interface_defaults,
                "datastore"      : datastore_defaults,
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

if sys.platform == "win32":
    # Derived from appdirs portion written by ofek
    try:
        from ctypes import windll
    except ImportError:
        try:
            import com.sun.jna
        except ImportError:
            try:
                import winreg as _winreg
            except ImportError:
                _get_win_path = get_win_path_environ
            else:
                _get_win_path = get_win_path_registry
        else:
            _get_win_path = get_win_path_jna
    else:
        _get_win_path = get_win_path_ctypes

def user_data_directory():
    global CONFIG_FILE_PATH
    global DATA_DIRECTORY
    global AUTHOR
    global APPLICATION

    system = sys.platform
    if system == "win32":
        if AUTHOR is None:
            AUTHOR = APPLICATION
        const = "CSIDL_LOCAL_APPDATA"
        path = Path(_get_win_path(const))
        if APPLICATION:
            if AUTHOR:
                path = path / AUTHOR / APPLICATION
            else:
                path = path / APPLICATION
    elif system == 'darwin':
        path = Path('~/Library/Application Support/').expanduser()
        if APPLICATION:
            path = path / APPLICATION
    else:
        path = os.getenv('XDG_DATA_HOME', Path("~/.local/share").expanduser())
        if APPLICATION:
            path = path / APPLICATION
    return path

def set_application_directories() -> None:
    """ Inspired by appdirs project: https://github.com/ActiveState/appdirs
    Use good default locations so users have predictable location to find scratch and config
    """
    global CONFIG_FILE_PATH
    global DATA_DIRECTORY
    global AUTHOR
    global APPLICATION

    system = sys.platform
    
    """ Usual configuration directories
        Mac OS X:               ~/Library/Preferences/<AppName>
        Unix:                   ~/.config/<AppName>     # or in $XDG_CONFIG_HOME, if defined
        Win *:                  same as user_data_dir
    """
    if system == "win32":
        path = user_data_directory()
    elif system == 'darwin':
        path = Path('~/Library/Preferences/').expanduser()
        if APPLICATION:
            path = path / APPLICATION
    else:
        path = os.getenv('XDG_CONFIG_HOME', os.path.expanduser("~/.config"))
        if APPLICATION:
            path = Path(path) / APPLICATION

    ''' Usual Data directories
        Windows:                C:\\Users\\<username>\\AppData\\Local\\<Organization>\\<App>
        Mac OS X:               ~/Library/Application Support/<App>
        Linux:                   ~/.local/share/<App>    # Alternative: $XDG_DATA_HOME, if in env
    '''
    CONFIG_FILE_PATH = path / CONFIG_FILE
    DATA_DIRECTORY = user_data_directory()
    print(f" - Location of configuration file   : {CONFIG_FILE_PATH}")
    if path and not path.exists():
        path.mkdir(parents=True, exist_ok=True)
        path.chmod(0o755)
        print(f" - created config directory: {path.absolute()}")
    print(f" - Default location to store data and caching: {DATA_DIRECTORY}")
    if DATA_DIRECTORY and not DATA_DIRECTORY.exists():
        DATA_DIRECTORY.mkdir(parents=True, exist_ok=True)
        DATA_DIRECTORY.chmod(0o755)
        print(f" - created data directory: {DATA_DIRECTORY.absolute()}")


def set_oxide_config_defaults() -> None:
    global DIR_DEFAULTS
    DIR_DEFAULTS = {"config"         : str(CONFIG_FILE_PATH),
                    "root"           : str(dir_root),
                    "oxide"          : str(dir_oxide),
                    "libraries"      : str(dir_oxide / "libraries"),
                    "modules"        : str(dir_root / "modules"),
                    "plugins"        : str(DATA_DIRECTORY / "plugins"),
                    "plugins_dev"    : str(DATA_DIRECTORY / "plugins_dev"),
                    "data_dir"       : str(DATA_DIRECTORY),
                    "datasets"       : str(DATA_DIRECTORY / "datasets"),
                    "datastore"      : str(DATA_DIRECTORY / "db"),
                    "localstore"     : str(DATA_DIRECTORY / "localstore"),
                    "logs"           : str(DATA_DIRECTORY),
                    "reference"      : str(DATA_DIRECTORY / "reference"),
                    "scratch"        : str(DATA_DIRECTORY / "scratch"),
                    "sample_dataset" : str(DATA_DIRECTORY / "datasets" / "sample_dataset"),
                    "ghidra_path"    : "",
                    "ghidra_path2"   : "",
                    "ghidra_path3"   : "",
                    "ghidra_path4"   : "",
                    "ghidra_path5"   : "",
                    "ida_path"       : "",
                    "ghidra_project" : str(DATA_DIRECTORY / "scratch"),
                    "scripts"        : str(dir_root / "scripts")
                    }
    ALL_DEFAULTS['dir'] = DIR_DEFAULTS
    ALL_DEFAULTS['history']['file'] = str(DATA_DIRECTORY / '.history.txt')


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
        print(" - Writing changes to config file", CONFIG_FILE)
        write_config_file()
    else:
        print(" - Aborting all changes to config")
        sys.exit(1)

    setup_run = True


def init() -> None:
    global config_changed
    global CONFIG_FILE_PATH

    # Find system preferred location for config file so Oxide uses predictable directoriess
    # This will update CONFIG_FILE_PATH
    set_application_directories()

    # Using udpated CONFIG_FILE_PATH, update default locations
    set_oxide_config_defaults()

    # Check if the config file exists. If not create it using defaults
    if not CONFIG_FILE_PATH.exists():
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
    global CONFIG_FILE_PATH
    try:
        rcp.read_file(fd, CONFIG_FILE_PATH)
    except IOError as e:
        logger.error("ConfigParse exception:%s", e)


def read_config_file() -> bool:
    """ This function opens a file based on the global config_file string and calls
        read_config to actually read the configuration in.
    """
    global CONFIG_FILE_PATH
    global logger
    logger.debug("Reading config file %s", CONFIG_FILE_PATH)
    try:
        with open(CONFIG_FILE_PATH, "r") as fd:
            read_config(fd)
        return True
    except IOError:
        logger.error("Unable to read config file %s", CONFIG_FILE_PATH)
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
    global CONFIG_FILE
    global CONFIG_FILE_PATH
    global rcp

    if new_config_file:
        CONFIG_FILE = new_config_file
        CONFIG_FILE_PATH = os.path.join(dir_root, CONFIG_FILE)

    logger.debug("Writing config to %s", CONFIG_FILE_PATH)
    try:
        fd = open(CONFIG_FILE_PATH, "w")
        rcp.write(fd)
        fd.close()
    except IOError as err:
        logger.error("Unable to write config file %s", CONFIG_FILE_PATH)
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
