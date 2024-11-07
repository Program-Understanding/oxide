AUTHORS="KEVAN,DYLAN"
DESC="Pass options to try and analyze effect on angr and Z3"
NAME="angr_parameter_optimization"

import logging
import subprocess
import json
import os
import z3
import statistics
import scipy

logger = logging.getLogger(NAME)

from core import api

opts_doc={"timeout": {"type": int, "mangle": True, "default": 600, "description": "Time in seconds for angr before it times out, default is 5 minutes"},
          "z3_timeout": {"type": int, "mangle": True, "default": 120,"description": "Time in seconds (later converted to ms) before Z3 returns unsat for a query"},
          "exploration": {"type": str, "mangle": True, "description": "Choose a different exploration technique. Should be from angr.exploration_techniques, such as 'angr.exploration_techniques.dfs'","default":""},
          "tactics": {"type": str, "mangle": True, "description": "Comma separated list of tactics to use as a z3.Solver() in claripy", "default": ""},
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
    #capture options
    try:
        timeout = opts['timeout']
        tactics = opts['tactics'].split(',')
        z3_timeout = opts['z3_timeout']
    except Exception as e:
        logger.error(f"Unable to wrangle options, error: {e}")
        return False
    #check validity of tactics
    for tactic in tactics:
        try:
            z3.Tactic(tactic)
        except z3.Z3Exception as e:
            logger.error(f"Unknown tactic: {tactic}, {e}")
            return False
    num_runs = int(opts['runs'])
    #create temporary file to run through angr script
    data = api.get_field(api.source(oid), oid, "data", {}) #get file data
    f_name = api.get_field("file_meta", oid, "names").pop()
    f_name = api.tmp_file(f_name, data) #make temp file for angr project
    file_full_path = os.path.join(api.scratch_dir, f_name)
    if not os.path.isfile(file_full_path):
        logger.error(f"Scratch file not found: {file_full_path}")
        return False
    #getting the script name to append to the path
    script_name = "angr_param_optimization.py"
    script_full_path = os.path.join(api.scripts_dir, script_name)
    if not os.path.isfile(script_full_path):
        logger.error(f"Script not found: {script_full_path}")
        return False
    #this has to be run separate times since angr will not let go of RAM
    #so we'll make as many commands as we have tactics
    tactic_cmds = []
    #initialize results dictionary as well
    results = {}
    for tactic in tactics:
        #appending a tuple: command, tactic
        tactic_cmds.append((f"python3 {script_full_path} {file_full_path} {timeout} {z3_timeout} {tactic}",tactic))
        results[tactic] = {'seconds': []}
    results['with no tactic'] = {'seconds':[]}
    angr_cmd = f"python3 {script_full_path} {file_full_path} {timeout} {z3_timeout}"
    #log out how many runs, timeout
    logger.debug(f"Timeout: {timeout}, runs: {num_runs}")
    #run multiple times to get some valid output and ensure angr isn't doing well as a one-off try
    for run in range(num_runs):
        with open(os.devnull, "w") as null:
            try:
                #get the output from angr and with tactics, and translate it to a json dictionary
                tactic_output = []
                for tactic_cmd in tactic_cmds:
                    #using tuple: output, tactic
                    logger.debug(f'Run {run+1}: command: {tactic_cmd[0]}')
                    tactic_output.append((json.loads(subprocess.check_output(tactic_cmd[0], universal_newlines=True, shell=True, stderr=null)),tactic_cmd[1]))
                logger.debug(f'Run {run+1}: command: {angr_cmd}')
                angr_output = json.loads(subprocess.check_output(angr_cmd, universal_newlines=True, shell=True, stderr=null))
                for t_o in tactic_output:
                    #using tuple: json, tactic
                    tactic_output = t_o[0]
                    results[t_o[1]][f'run {run+1}'] = tactic_output
                    results[t_o[1]]['seconds'].append(tactic_output['seconds'])
                angr_output = angr_output
                results['with no tactic'][f'run {run+1}'] = angr_output
                results['with no tactic']['seconds'].append(angr_output['seconds'])
            except subprocess.CalledProcessError as e:
                logger.error(f"Error occured in subprocess: {e}")
                return False
            except json.decoder.JSONDecodeError as e:
                logger.error(f"JSON decoding error {e}")
                return False
            except Exception as e:
                logger.error(f"Exception raised: {e}")
                return False
    #get mean, standard deviation, t-test
    results['with no tactic']['mean seconds'] = statistics.mean(results['with no tactic']['seconds'])
    results['with no tactic']['std. deviation'] = statistics.stdev(results['with no tactic']['seconds'])
    for tactic in tactics:
        results[tactic]['mean seconds'] = statistics.mean(results[tactic]['seconds'])
        results[tactic]['std. deviation'] = statistics.stdev(results['with no tactic']['seconds'])
        t_test_p_value = scipy.stats.ttest_ind(results['with no tactic']['seconds'], results[tactic]['seconds'], equal_var=False).pvalue
        results[tactic][f'p-value of the t-test putting tactic against angr'] = t_test_p_value
        results[tactic][f'p-value < 0.05'] = float(t_test_p_value) < 0.05
    #ranking the tactics by mapping each tactic to its average seconds,
    #but returning only the tactics that are statistically significantly better than
    #the default solver used by angr
    mapped_tactics = []
    for tactic in tactics:
        if results[tactic][f'p-value < 0.05']:
            mapped_tactics.append((tactic,results[tactic]['mean seconds']))
    if mapped_tactics:
        sorted_tactics = sorted(mapped_tactics,key=lambda mapt: mapt[1])
        results['statistically significant tactics ranked'] = [(tactic[0],round(tactic[1],4)) for tactic in sorted_tactics]
    else:
        results['statistically significant tactics ranked'] = "No statistically significant improvement with any tactic"
    api.store(NAME,oid,results,opts)
    return True
