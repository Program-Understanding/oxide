""" Sqlite3 backend for oxide datastore

Resources:
- https://stackoverflow.com/questions/12952546/sqlite3-interfaceerror-error-binding-parameter-1-probably-unsupported-type
"""
import os
import shutil
import logging
import time
import errno
import pickle
from glob import glob
import sqlite3
from pathlib import Path

from oxide.core import sys_utils, config, api, ologger
from oxide.core.serialization import serialize, deserialize, SERIAL_METHOD
from oxide.core.options import build_suffix
from oxide.core.options import parse_suffix

from typing import Dict, List, Any, Optional, Tuple


NAME = "ds_sqlite"
logger = logging.getLogger(NAME)

datastore_dir = config.dir_datastore
sys_utils.ensure_dir_exists(datastore_dir)
scratch_dir = config.dir_scratch
sys_utils.ensure_dir_exists(scratch_dir)

# Create or connect to the SQLite database
CONN = None
CURSOR = None

TABLE_NAME = "data"

# Database Initialization
def initialize_database():
    """ Initialize database, and create table if it does not exist
    """
    global TABLE_NAME
    global CONN
    global CURSOR
    global VALID_SERIAL

    db_path = Path(datastore_dir) / 'datastore.db'

    with sqlite3.connect(db_path.absolute()) as conn:
        CONN = conn
        CURSOR = CONN.cursor()
        # Create the table if it doesn't exist
        # OID is BLOB to be consistent with Options
        CURSOR.execute(f'''
            CREATE TABLE IF NOT EXISTS {TABLE_NAME} (
                module_name TEXT NOT NULL,
                oid BLOB NOT NULL,
                options BLOB,
                data BLOB,
                serial TEXT,
                PRIMARY KEY (module_name, oid, options, serial)
            );
        ''')
        CONN.commit()

# ------------------------------- MAIN FUNCTIONS -------------------------------------------------

def store(mod_name: str, oid: str, data: bytes, opts: dict, block: bool = True) -> bool:
    global CURSOR
    global SERIAL_METHOD
    opts_str = serialize(opts)  # Serialize opts for storage
    data_str = serialize(data)  # Serialize data for storage

    CURSOR.execute("INSERT OR REPLACE INTO data (module_name, oid, options, data, serial) VALUES (?, ?, ?, ?, ?)", 
                   (mod_name, oid.encode('utf-8'), opts_str, data_str, SERIAL_METHOD))
    CONN.commit()
    return True


def available_data(mod_name: str) -> List[Tuple[str, Dict[str, Any]]]:
    global SERIAL_METHOD
    CURSOR.execute("SELECT oid, options FROM data WHERE module_name=? AND serial=?", (mod_name, SERIAL_METHOD))
    records = CURSOR.fetchall()
    data = [(oid, deserialize(opts)) for oid, opts in records]
    return data


def retrieve_all(mod_name: str) -> Dict[str, Any]:
    # print('1', mod_name, '2', SERIAL_METHOD)
    CURSOR.execute("SELECT oid || options, data FROM data WHERE module_name=? and serial=?", (mod_name, SERIAL_METHOD))

    records = CURSOR.fetchall()
    return {mangled_name: data for mangled_name, data in records}


def retrieve_all_keys(mod_name: str) -> Optional[List[str]]:
    CURSOR.execute("SELECT oid || options FROM data WHERE module_name=? and serial=?", (mod_name, SERIAL_METHOD))
    records = CURSOR.fetchall()
    return [deserialize(res[0]) for res in records] if records else None


def retrieve(mod_name: str, oid: str, opts: dict = None, lock: bool = False) -> Optional[Any]:
    if opts is None:
        opts = {}
    opts_str = serialize(opts)

    CURSOR.execute("SELECT data FROM data WHERE module_name=? AND oid=? and serial=?", (mod_name, oid.encode('utf-8'), SERIAL_METHOD))
    record = CURSOR.fetchone()

    res = deserialize(record[0]) if record else None
    return res


def retrieve_lock(mod_name: str, oid: str, opts: dict = None) -> Optional[bytes]:
    if opts is None:
        opts = {}
    return retrieve(mod_name, oid, opts, True)


def count_records(mod_name: str) -> int:
    CURSOR.execute("SELECT COUNT(*) FROM data WHERE module_name=? and serial=?", (mod_name, SERIAL_METHOD))
    return CURSOR.fetchone()[0]


def exists(mod_name: str, oid: str, opts: dict = None) -> bool:
    if opts is None:
        opts = {}
    opts_str = serialize(opts)
    # AND options=?
    CURSOR.execute("SELECT 1 FROM data WHERE module_name=? AND oid=? and serial=?", (mod_name, oid.encode('utf-8'), SERIAL_METHOD))
    return bool(CURSOR.fetchone())


def delete_module_data(mod_name: str) -> bool:
    CURSOR.execute("DELETE FROM data WHERE module_name=? and serial=?", (mod_name, SERIAL_METHOD))
    CONN.commit()
    return True


def delete_oid_data(mod_name: str, oid: str) -> bool:
    CURSOR.execute("DELETE FROM data WHERE module_name=? AND oid=?", (mod_name, oid))
    CONN.commit()
    return True

def cleanup() -> None:
    """ NotImplemented
    """
    pass


# ... [rest of the code]