import os
import shutil
import pickle
import logging
import time
import errno
from glob import glob
import sqlite3
from pathlib import Path

from oxide.core import sys_utils, config, api, ologger
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
    db_path = Path(datastore_dir) / 'datastore.db'
    print(db_path.absolute)
    with sqlite3.connect(db_path.absolute) as conn:
        CONN = conn
        CURSOR = CONN.cursor()
        # Create the table if it doesn't exist
        CURSOR.execute(f'''
            CREATE TABLE IF NOT EXISTS {TABLE_NAME} (
                module_name TEXT NOT NULL,
                oid TEXT NOT NULL,
                options TEXT,
                data BLOB,
                PRIMARY KEY (module_name, oid, options)
            );
        ''')
        CONN.commit()

# ------------------------------- MAIN FUNCTIONS -------------------------------------------------

def store(mod_name: str, oid: str, data: bytes, opts: dict, block: bool = True) -> bool:
    global CURSOR
    opts_str = pickle.dumps(opts)  # Serialize opts for storage
    CURSOR.execute("INSERT OR REPLACE INTO data (mod_name, oid, opts, data) VALUES (?, ?, ?, ?)", 
                   (mod_name, oid, opts_str, data))
    CONN.commit()
    return True


def available_data(mod_name: str) -> List[Tuple[str, Dict[str, Any]]]:
    CURSOR.execute("SELECT oid, opts FROM data WHERE mod_name=?", (mod_name,))
    records = cursor.fetchall()
    data = [(oid, pickle.loads(opts)) for oid, opts in records]
    return data


def retrieve_all(mod_name: str) -> Dict[str, Any]:
    cursor.execute("SELECT oid || opts, data FROM data WHERE mod_name=?", (mod_name,))
    records = cursor.fetchall()
    return {mangled_name: data for mangled_name, data in records}


def retrieve_all_keys(mod_name: str) -> Optional[List[str]]:
    cursor.execute("SELECT oid || opts FROM data WHERE mod_name=?", (mod_name,))
    records = cursor.fetchall()
    return [res[0] for res in records] if records else None


def retrieve(mod_name: str, oid: str, opts: dict = {}, lock: bool = False) -> Optional[Any]:
    opts_str = pickle.dumps(opts)
    cursor.execute("SELECT data FROM data WHERE mod_name=? AND oid=? AND opts=?", (mod_name, oid, opts_str))
    record = cursor.fetchone()
    return record[0] if record else None


def count_records(mod_name: str) -> int:
    cursor.execute("SELECT COUNT(*) FROM data WHERE mod_name=?", (mod_name,))
    return cursor.fetchone()[0]


def exists(mod_name: str, oid: str, opts: dict = {}) -> bool:
    opts_str = pickle.dumps(opts)
    cursor.execute("SELECT 1 FROM data WHERE mod_name=? AND oid=? AND opts=?", (mod_name, oid, opts_str))
    return bool(cursor.fetchone())


def delete_module_data(mod_name: str) -> bool:
    cursor.execute("DELETE FROM data WHERE mod_name=?", (mod_name,))
    conn.commit()
    return True


def delete_oid_data(mod_name: str, oid: str) -> bool:
    cursor.execute("DELETE FROM data WHERE mod_name=? AND oid=?", (mod_name, oid))
    conn.commit()
    return True

# ... [rest of the code]
