AUTHOR="KEVAN"
DESC="Pass options to try and analyze effect on angr and Z3"
NAME="angr_parameter_optimization"

import logging
import subprocess
import json
import os

logger = logging.getLogger(NAME)

from core import api

opts_doc={"timeout": {"type": int, "mangle": True, "default": 120, "description": "Time in seconds for angr before it times out, default is 5 minutes"},
          "exploration": {"type": str, "mangle": True, "description": "Choose a different exploration technique. Should be from angr.exploration_techniques, such as 'angr.exploration_techniques.dfs'","default":""},
          "tactics": {"type": str, "mangle": True, "description": "Comma separated list of tactics to use for angr's Z3 solver in a z3.Then() order. Takes precedence over tactic", "default": ""},
          "tactic": {"type": str, "mangle": True, "description": "Singular tactic to use for angr's Z3 solver. Tactics takes precedence","default":""},
          "runs": {"type": int, "mangle": True, "description": "How many runs to do of the OID","default": 5}
          }

def documentation():
    return {"description":DESC,
            "opts_doc": opts_doc,
            "private": False,
            "set": False,
            "atomic":True
            }

timeout = float()
def process(oid, opts):
    """
    This module takes in various parameters as options to
    pass to angr or Z3 in order to try and optimize them for
    faster execution speed in angr
    """
    timeout = opts['timeout']
    tactic = opts['tactic']
    num_runs = int(opts['runs'])
    data = api.get_field(api.source(oid), oid, "data", {}) #get file data
    f_name = api.get_field("file_meta", oid, "names").pop()
    f_name = api.tmp_file(f_name, data) #make temp file for angr project
    for run in range(num_runs):
        tactic_cmd = f"python separate_extraction_script.py {f_name} {timeout} {tactic}"
        angr_cmd = f"python separate_extraction_script.py {f_name} {timeout}"
        with open(os.devnull, "w") as null:
            tactic_output = subprocess.check_output(tactic_cmd, universal_newlines=True,stderr=null)
            angr_output = subprocess.check_output(angr_cmd, universal_newlines=True,stderr=null)
    try:
        if "error" in output.lower():
            return False
        else:
            output = json.loads(output)
    except Exception as e:
        logger.error(f"Error occured when handling output using tactics: {e}")
        return False
    return True
