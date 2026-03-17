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
from collections.abc import Iterable

from oxide.core import sys_utils
from oxide.core import user_directories
from oxide.core.otypes import cast_string, convert_logging_level
from oxide.core.user_directories import get_win_path_environ, get_win_path_registry, get_win_path_jna, get_win_path_ctypes

NAME = "config"
logger = logging.getLogger(NAME)
logging.basicConfig(level=logging.INFO) # set this to DEBUG for debugging since config is used before logging is setup

AUTHOR = "ProgramUnderstandingLab"
APPLICATION = "oxide"

dir_root = Path(sys_utils.ROOT_DIR).absolute()
dir_oxide = Path(sys_utils.OXIDE_DIR).absolute()

# Filename and path for configuration
config_file = ".config.txt"
# config_file_path : Path = Path()  # Update in set_application_directories

# Directory for data files
# data_directory : Path = Path()  # Update in set_application_directories

# Global config defaults will be used when a new config is created or if a section is missing
# Global vars are section_option
# This is updated in the init function, when system preferred directories are identified

from typing import Literal, Protocol, cast
from dataclasses import dataclass, field, fields

class ConfigSectionMixin(Protocol):
    __dataclass_fields__ : dict[str, str|bool|int]
    def __getitem__(self, key: str):
        if key not in self.__dataclass_fields__:
            raise KeyError(key)
        return cast(str|bool|int,getattr(self, key))
    def __setitem__(self, key: str, value: str|int|bool) -> None:
        if key not in self.__dataclass_fields__:
            raise KeyError(key)
        setattr(self, key, value)
    def keys(self):
        return self.__dataclass_fields__.keys()
    def items(self):
        for k in self.__dataclass_fields__:
            yield k, getattr(self,k)
    def __contains__(self, key:str) -> bool:
        return key in self.__dataclass_fields__
    def __iter__(self):
        for k in self.__dataclass_fields__:
            yield k
@dataclass
class InterfaceConfig(ConfigSectionMixin):
    # Pagination, None disables all pagination of output, 48 is a good default value
    page_size: int = 0

@dataclass
class LoggingConfig(ConfigSectionMixin):
    level: Literal["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"] = "INFO"
    rotate: bool = False
    max_log_size: int = 10
    num_log_files: int = 5

@dataclass
class DatastoreConfig(ConfigSectionMixin):
    datastore: str = "filesystem"
    serialization: str = "pickle"

@dataclass
class VerbosityConfig(ConfigSectionMixin):
    level: Literal["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"] = "INFO"

@dataclass
class MultiprocConfig(ConfigSectionMixin):
    on: bool = False
    max: int = 3

@dataclass
class FileConfig(ConfigSectionMixin):
    max: int = 1048576
    process_unrecognized_formats: bool = False

@dataclass
class DistributedConfig(ConfigSectionMixin):
    port: int = 8000
    compute_nodes: str = "localhost"

@dataclass
class DevModeConfig(ConfigSectionMixin):
    enable: bool = True

@dataclass
class DjangoConfig(ConfigSectionMixin):
    ip: str = "0.0.0.0"
    port: int = 8888

@dataclass
class GhidraProjectConfig(ConfigSectionMixin):
    project_name: str = "ghidraBenchmarking"

@dataclass
class PharosConfig(ConfigSectionMixin):
    docker_image: str = ""

@dataclass
class ProbdisasmConfig(ConfigSectionMixin):
    docker_image: str = ""

@dataclass
class PluginsConfig(ConfigSectionMixin):
    default: bool = True

@dataclass
class HistoryConfig(ConfigSectionMixin):
    file: str = ".history.txt"
    max: int= 200

# need to set up default locations for user directories depending on system platform
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
    #user_data_directory() code
    const = "CSIDL_LOCAL_APPDATA"
    user_data_directory = Path(_get_win_path(const))
    if APPLICATION:
        if AUTHOR:
            user_data_directory = user_data_directory / AUTHOR / APPLICATION
        else:
            user_data_directory = user_data_directory / APPLICATION
    _path = user_data_directory
elif sys.platform == "darwin":
    user_data_directory = Path('~/Library/Application Support/').expanduser()
    if APPLICATION:
        user_data_directory = user_data_directory / APPLICATION
    _path = Path('~/Library/Preferences/').expanduser()
    if APPLICATION:
        _path = _path / APPLICATION
else:
    user_data_directory = Path(os.getenv('XDG_DATA_HOME', Path("~/.local/share").expanduser()))
    if APPLICATION:
        user_data_directory = user_data_directory = Path(user_data_directory) / APPLICATION
    _path = Path(os.getenv('XDG_CONFIG_HOME', os.path.expanduser("~/.config")))
if APPLICATION:
    _path = Path(_path) / APPLICATION
config_file_path = _path / config_file
data_directory = user_data_directory
print(f" - Location of configuration file   : {config_file_path}")
if _path and not _path.exists():
    _path.mkdir(parents=True,exist_ok=True)
    _path.chmod(0o755)
    print(f" - created config directory: {_path.absolute()}")
    print(f" - Default location to store data and caching: {data_directory}")
if data_directory and not data_directory.exists():
    data_directory.mkdir(parents=True, exist_ok=True)
    data_directory.chmod(0o755)
    print(f" - created data directory: {data_directory.absolute()}")
#now we can define dir dataclass
@dataclass
class DirConfig(ConfigSectionMixin):
    config: str = str(config_file_path)
    root: str = str(dir_root)
    oxide: str = str(dir_oxide)
    libraries: str = str(dir_oxide / "libraries")
    modules: str = str(dir_root / "modules")
    plugins: str = str(data_directory / "plugins")
    plugins_dev: str = str(data_directory / "plugins_dev")
    data_dir: str = str(data_directory)
    datasets: str = str(data_directory / "datasets")
    datastore: str = str(data_directory / "db")
    localstore: str = str(data_directory / "localstore")
    logs: str = str(data_directory)
    reference: str = str(data_directory / "reference")
    scratch: str = str(data_directory / "scratch")
    sample_dataset: str = str(data_directory / "datasets" / "sample_dataset")
    ghidra_path: str = ""
    ghidra_path2: str = ""
    ghidra_path3: str = ""
    ghidra_path4: str = ""
    ghidra_path5: str = ""
    ida_path: str = ""
    ghidra_project: str = str(data_directory / "scratch")
    scripts: str = str(dir_root.parent.parent / "scripts") #actual oxide_root
    local_llm_path: str = ""

# ---- Top-level config ----
ConfigSection = DirConfig | InterfaceConfig | DatastoreConfig | LoggingConfig | VerbosityConfig | MultiprocConfig | FileConfig | DistributedConfig | DevModeConfig | DjangoConfig | PluginsConfig | HistoryConfig | GhidraProjectConfig | PharosConfig | ProbdisasmConfig
SectionName = Literal[
    "dir",
    "interface",
    "datastore",
    "logging",
    "verbosity",
    "multiproc",
    "file",
    "distributed",
    "dev_mode",
    "django",
    "plugins",
    "history",
    "ghidra_project",
    "pharos",
    "probdisasm",
]

@dataclass
class Config:
    dir : DirConfig = field(default_factory=DirConfig)
    interface: InterfaceConfig = field(default_factory=InterfaceConfig)
    datastore: DatastoreConfig = field(default_factory=DatastoreConfig)
    logging: LoggingConfig = field(default_factory=LoggingConfig)
    verbosity: VerbosityConfig = field(default_factory=VerbosityConfig)
    multiproc: MultiprocConfig = field(default_factory=MultiprocConfig)
    file: FileConfig = field(default_factory=FileConfig)
    distributed: DistributedConfig = field(default_factory=DistributedConfig)
    dev_mode: DevModeConfig = field(default_factory=DevModeConfig)
    django: DjangoConfig = field(default_factory=DjangoConfig)
    plugins: PluginsConfig = field(default_factory=PluginsConfig)
    history: HistoryConfig = field(default_factory=HistoryConfig)
    ghidra_project: GhidraProjectConfig = field(default_factory=GhidraProjectConfig)
    pharos: PharosConfig = field(default_factory=PharosConfig)
    probdisasm: ProbdisasmConfig = field(default_factory=ProbdisasmConfig)
    def __getitem__(self,item:SectionName) -> ConfigSection:
        return cast(ConfigSection,getattr(self, item))
    def __setitem__(self,item:SectionName,value:ConfigSection):
        setattr(self, item, value)
    def __iter__(self):
        for k in list(self.__dataclass_fields__.keys()):
            yield cast(SectionName,k)
    def __contains__(self, k:str):
        if k in self.__dataclass_fields__:
            return True
        return False
    
# logging_defaults : LoggingDefaults = {"level": "INFO",
#                     "rotate": "false",
#                     "max_log_size": "10",
#                     "num_log_files": "5"}

# datastore_defaults : DatastoreDefaults = { "datastore": "filesystem",
#                        "serialization": "pickle"
# }

# verbosity_defaults : VerbosityDefaults = {"level": "INFO"}

# multiproc_defaults : MultiprocDefaults = {"on": "false",
#                       "max": "3"}

# file_defaults : FileDefaults = {"max": "1048576",
#                  "process_unrecognized_formats": "false"}

# distributed_defaults : DistributedDefaults = {"port": "8000",
#                         "compute_nodes": "localhost"}

# dev_mode : DevModeDefaults = {"enable": "True"}

# django : DjangoDefaults = {"ip": "0.0.0.0",
#           "port": "8888"}

# ghidra_project : GhidraProjectDefaults = {"project_name": "ghidraBenchmarking"}

# pharos : PharosDefaults = {"docker_image": ""}
# probdisasm : ProbdisasmDefaults = {"docker_image": ""}

# plugins : PluginsDefaults = {"default": "True"}

# history : HistoryDefaults = {"file": ".history.txt",
#            "max": "200"}

# ALL_DEFAULTS : AllDefaults = {"dir"            : dir_defaults,
#                 "interface"      : interface_defaults,
#                 "datastore"      : datastore_defaults,
#                 "logging"        : logging_defaults,
#                 "verbosity"      : verbosity_defaults,
#                 "multiproc"      : multiproc_defaults,
#                 "file"           : file_defaults,
#                 "distributed"    : distributed_defaults,
#                 "dev_mode"       : dev_mode,
#                 "django"         : django,
#                 "plugins"        : plugins,
#                 "history"        : history,
#                 "ghidra_project" : ghidra_project,
#                 "pharos"         : pharos,
#                 "probdisasm"     : probdisasm
#                 }
# our top-level config
# defined into a dataclass because existing names of options such as "logging"
# would conflict at the 'global' level for the module, "logging" attribute conflicts w/ logging module
conf = Config()
rcp = configparser.ConfigParser()
config_changed = False
setup_run = False

# def set_oxide_config_defaults() -> None:
#     global dir_defaults
#     dir_defaults = {"config"         : str(config_file_path),
#                     "root"           : str(dir_root),
#                     "oxide"          : str(dir_oxide),
#                     "libraries"      : str(dir_oxide / "libraries"),
#                     "modules"        : str(dir_root / "modules"),
#                     "plugins"        : str(data_directory / "plugins"),
#                     "plugins_dev"    : str(data_directory / "plugins_dev"),
#                     "data_dir"       : str(data_directory),
#                     "datasets"       : str(data_directory / "datasets"),
#                     "datastore"      : str(data_directory / "db"),
#                     "localstore"     : str(data_directory / "localstore"),
#                     "logs"           : str(data_directory),
#                     "reference"      : str(data_directory / "reference"),
#                     "scratch"        : str(data_directory / "scratch"),
#                     "sample_dataset" : str(data_directory / "datasets" / "sample_dataset"),
#                     "ghidra_path"    : "",
#                     "ghidra_path2"   : "",
#                     "ghidra_path3"   : "",
#                     "ghidra_path4"   : "",
#                     "ghidra_path5"   : "",
#                     "ida_path"       : "",
#                     "ghidra_project" : str(data_directory / "scratch"),
#                     "scripts"        : str(dir_root.parent.parent / "scripts"),  # actual oxide_root
#                     "local_llm_path": "",
#                     }
#     ALL_DEFAULTS['dir'] = dir_defaults
#     ALL_DEFAULTS['history']['file'] = str(data_directory / '.history.txt')


def config_menu(section: str = "all") -> bool:
    """
    globals:
        rcp: ConfigParser
    """

    if section == "all":
        sections = cast(list[SectionName], rcp.sections())
    elif section not in rcp.sections():
        print(" - Section {} not found".format(section))
        return False
    else:
        sections = cast(list[SectionName],[section])

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
        section_dc = conf[config_section]
        for f in fields(section_dc):
            option = f.name
            cval = rcp.get(config_section, option)
            dval = section_dc[option]
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
    global config_file_path

    # Check if the config file exists. If not create it using defaults
    if not config_file_path.exists():
        setup(section="all", initial_setup=True)

    if not read_config_file():
        logger.warning("Issue reading config file!")
    if not set_globals():
        logger.warning("Issue setting globals in config")
    sanity_check()

    if config_changed:
        if not set_globals():
            logger.warning("Issue setting globals in config after detecting a change in config!")
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
        dir_root = Path(sys_utils.ROOT_DIR)
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
        dir_oxide = Path(sys_utils.OXIDE_DIR)
        set_value("dir", "oxide", dir_oxide)
        config_changed = True


# old definition of read_config, overshadowed by following def        
# def read_config(fd: Iterable[str]) -> None:
#     """ Reads the configuration in the file referenced by fd.
#         the global config_file string variable is only used in error handling
#     globals:
#         RCP: ConfigParser
#     """
#     global rcp
#     global config_file_path
#     try:
#         rcp.read_file(fd, config_file_path)
#     except IOError as e:
#         logger.error("ConfigParse exception:%s", e)

def read_config(fd : Iterable[str]) -> None:
    """ Reads the configuration in the file referenced by fd.
        the global config_file string variable is only used in error handling
    globals:
        RCP: ConfigParser
    """
    global rcp
    global config_file_path
    try:
        rcp.read_file(fd, str(config_file_path))
        # Ensure all keys are included even if not predefined in ALL_DEFAULTS
        for section in rcp.sections():
            section = cast(SectionName, section)
            if section not in conf:
                logger.error("Section %s not in CONF", section)
                continue
                # ALL_DEFAULTS[section] = {} # we should probably not add new sections, but leaving this just in case
            for key in rcp.options(section):
                if key not in conf[section]:
                    logger.info("Detected new key %s in section %s", key, section)
                    conf[section][key] = rcp.get(section, key)
    except IOError as e:
        logger.error("ConfigParse exception:%s", e)

def read_config_file() -> bool:
    """ This function opens a file based on the global config_file string and calls
        read_config to actually read the configuration in.
    """
    global config_file_path
    global logger
    logger.debug("Reading config file %s", config_file_path)
    try:
        with open(config_file_path, "r") as fd:
            read_config(fd)
        return True
    except IOError:
        logger.error("Unable to read config file %s", config_file_path)
        return False

def set_config_all_to_defaults() -> None:
    """ Iterate over the defaults and set the according values
    """
    global config_changed
    global logger
    logger.debug("Creating default config")
    for section in conf:
        set_config_section_to_defaults(section)
    config_changed = True

def set_config_section_to_defaults(section: SectionName) -> None:
    global rcp
    global config_changed
    if not rcp.has_section(section):
        rcp.add_section(section)
    assert section in conf
    for option in conf[section]:
        set_config_option_to_default(section, option)
    config_changed = True

def set_config_option_to_default(section: SectionName, option: str) -> None:
    global config_changed
    # make a new config and get its default value
    value = Config()[section][option]
    rcp.set(section, option, str(value).lower())
    config_changed = True

#global dict of options
def set_global_option(section: SectionName, option: str, value: str) -> None:
    var = section + "_" + option
    value = cast_string(value)
    globals()[var] = value

def get_value_or_set_to_default(section: SectionName, option: str) -> str:
    try:
        value = rcp.get(section, option)
        if value == "":
            # if default is also "", ignore
            if Config()[section][option] == "":
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
    for section in conf.__dataclass_fields__:
        section = cast(SectionName,section)
        if not rcp.has_section(section):
            set_config_section_to_defaults(section)
            config_changed = True
        for option in cast(ConfigSection,getattr(conf,section)).__dataclass_fields__:
            value = get_value_or_set_to_default(section, option)
            set_global_option(section, option, value)
    return True


def set_value(section: SectionName, option: str, value: str | Path | int | bool) -> None:
    """ This function sets an option in the config
        file but leaves the other values the same.
    """
    global rcp
    global config_changed
    conf[section][option] = value if not isinstance(value,Path) else str(value)
    if not rcp.has_section(section):
        rcp.add_section(section)
    rcp.set(section, option, str(value))
    config_changed = True


def write_config_file(new_config_file: str | None = None) -> None:
    """ This function opens a file based on the global config_file string and writes the
        current configuration out to it.
    """
    global config_file
    global config_file_path
    global rcp

    if new_config_file:
        config_file = new_config_file
        config_file_path = Path(os.path.join(dir_root, config_file))

    logger.debug("Writing config to %s", config_file_path)
    try:
        fd = open(config_file_path, "w")
        rcp.write(fd)
        fd.close()
    except IOError as err:
        logger.error("Unable to write config file %s", config_file_path)
        logger.error(str(err))


def get_logging_level() -> int | None:
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


def get_section(section: SectionName) -> dict[str, str|int|bool]:
    sdict : dict[str,str|int|bool] = {}
    # identify type of each option via dataclass
    for f in fields(conf[section]):
        ty = f.type
        option = f.name
        match ty:
            case "int":
                sdict[option] = rcp.getboolean(section, option)
            case "bool":
                sdict[option] = rcp.getint(section, option)
            case _:
                sdict[option] = rcp.get(section, option)
    # for option in rcp.options(section):
        
    #     sdict[option] = rcp.get(section, option)
    return sdict


def get_all() -> dict[str, dict[str, int|bool|str]]:
    """ Return a dictionary of dictionaries with the sections, options and values
    """
    global rcp
    cdict : dict[str,dict[str,int|bool|str]] = {}
    for section in conf:
    # for section in rcp.sections():
        cdict[section] = get_section(section)
    return cdict


def get_value(section: SectionName, option: str) -> str | int | bool | None:
    """ Given a section and an option return the value
    """
    global rcp
    try:
        ty = type(conf[section][option])
        match ty:
            case ty if ty is int:
                value = rcp.getint(section, option)
            case ty if ty is bool:
                value = rcp.getboolean(section, option)
            case _:
                value = rcp.get(section,option)
        res = value
    except configparser.NoOptionError:
        logger.error("Tried to retrieve nonexistant value from config (%s:%s).", section, option)
        res = None
    return res


init()
def __getattr__(attr:str)->str|int|bool:
    section, option = attr.split("_",1)
    if section in conf:
        section = cast(SectionName,section)
        if option in conf[section]:
            return conf[section][option]
        else:
            raise AttributeError(f"{option} is not a valid config option for {section}. Valid options are {conf[section].keys()}")
    else:
        raise AttributeError(f"{section} is not a part of config")
