AUTHORS="KEVAN,DYLAN"
DESC="Pass options to try and analyze effect on angr and Z3"
NAME="angr_parameter_optimization"
SUBPROC="angr_constraint_grabber"
SUBPROC_B="angr_optimization_test"
import logging
import subprocess
import os, sys
import statistics
import scipy
#used for debugging multithreading segfault i was having
import faulthandler
faulthandler.enable()
import traceback
logger = logging.getLogger(NAME)

from core import api, config

#debugging in oxide run: random_sample --n=2 &core_utils | run angr_parameter_optimization --timeout=1500 --z3_timeout=120 --tactics=qfufbv_ackr,qfnra,qfidl,qflra,qfauflia,qfbv
#random_sample --n=1 &small_bins | run angr_parameter_optimization --timeout=1500 --z3_timeout=120 --tactics=qfufbv_ackr,qfnra,qfidl,qflra,qfauflia,qfbv

opts_doc={"timeout": {"type": int, "mangle": True, "default": 600, "description": "Time in seconds for angr before it times out, default is 5 minutes"},
          "z3_timeout": {"type": int, "mangle": True, "default": 120,"description": "Time in seconds (later converted to ms) before Z3 returns unsat for a query"},
          "exploration": {"type": str, "mangle": True, "description": "Choose a different exploration technique. Should be from angr.exploration_techniques, such as 'angr.exploration_techniques.dfs'","default":""},
          "tactics": {"type": str, "mangle": True, "description": "Comma separated list of tactics to use as a z3.Solver() in claripy", "default": ""},
          "runs": {"type": int, "mangle": True, "description": "How many runs to do of the OID","default": 1}
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
    #sorry but this is the best way to test if the tactics are valid.... otherwise i get issues w/ multithreading
    #if i call z3 here and don't set a thread context and stuff
    z3_tactics = "ackermannize_bv subpaving horn horn-simplify nlsat qfnra-nlsat qe-light nlqsat qe qsat qe2 qe_rec psat sat sat-preprocess ctx-solver-simplify psmt unit-subsume-simplify aig add-bounds card2bv degree-shift diff-neq eq2bv factor fix-dl-var fm lia2card lia2pb nla2bv normalize-bounds pb2bv propagate-ineqs purify-arith recover-01 bit-blast bv1-blast bv_bound_chk propagate-bv-bounds propagate-bv-bounds2 reduce-bv-size bv-slice bvarray2uf dt2bv elim-small-bv max-bv-sharing blast-term-ite cofactor-term-ite collect-statistics ctx-simplify demodulator der distribute-forall dom-simplify elim-term-ite elim-uncnstr2 elim-uncnstr elim-predicates euf-completion injectivity snf nnf occf pb-preprocess propagate-values2 propagate-values reduce-args reduce-args2 simplify elim-and solve-eqs special-relations split-clause symmetry-reduce tseitin-cnf tseitin-cnf-core qffd pqffd smtfd fpa2bv qffp qffpbv qffplra default solver-subsumption qfbv-sls qfbv-new-sls qfbv-new-sls-core nra qfaufbv qfauflia qfbv qfidl qflia qflra qfnia qfnra qfuf qfufbv qfufbv_ackr ufnia uflra auflia auflira aufnira lra lia lira smt skip fail fail-if-undecided macro-finder quasi-macros ufbv-rewriter bv ufbv"
    #check validity of tactics
    for tactic in tactics:
        if tactic not in z3_tactics:
            logger.error(f"invalid tactic {tactic}")
    num_runs = int(opts['runs'])
    #create temporary file to run through angr script
    data = api.get_field(api.source(oid), oid, "data", {}) #get file data
    f_name = api.get_field("file_meta", oid, "names").pop()
    f_name = api.tmp_file(f_name, data) #make temp file for angr project
    file_full_path = os.path.join(api.scratch_dir, f_name)
    if not os.path.isfile(file_full_path):
        logger.error(f"Scratch file not found: {file_full_path}")
        return False
    #getting the script to grab constraints' name to append to the path
    constraint_script_name = "angr_constraint_grabber.py"
    constraint_script_full_path = os.path.join(api.scripts_dir, constraint_script_name)
    if not os.path.isfile(constraint_script_full_path):
        logger.error(f"Script not found: {constraint_script_full_path}")
        return False
    #getting the script to run constraints' name to append to the path
    opt_script_name = "angr_optimization_test.py"
    opt_script_full_path = os.path.join(api.scripts_dir, opt_script_name)
    if not os.path.isfile(opt_script_full_path):
        logger.error(f"Script not found: {opt_script_full_path}")
        return False
    # we'll make as many commands as we have tactics
    tactic_cmds = []
    #initialize results dictionary as well
    results = {}
    for tactic in tactics:
        #appending a tuple: command, tactic
        tactic_cmds.append((f"python3 {opt_script_full_path} {SUBPROC} {oid} {z3_timeout} {config.multiproc_max} {tactic}",tactic))
        results[tactic] = {}
    angr_cmd = f"python3 {constraint_script_full_path} {file_full_path} {oid} {timeout} {z3_timeout}"
    results['with no tactic'] = {}
    #set up the proper python path for the environment
    pythonpath = ""
    for directory in sys.path:
        pythonpath = pythonpath + directory + ";"
    env = os.environ.copy()
    #log out how many runs, timeout
    logger.info(f"Timeout: {timeout}, z3 timeout: {z3_timeout}")
    logger.debug(f'Running command: {angr_cmd}')
    with open(os.devnull, "w") as null:
            try:
                sub_proc_out = subproc_run(angr_cmd,env,logger,null)
            except Exception as e:
                logger.error(f"Exception raised: {e}")
                if "sub_proc_out" in locals():
                    logger.error(f"Subprocess output: {sub_proc_out}")
                api.local_delete_data(SUBPROC,oid)
                return False
    #run multiple times to get some valid output and ensure angr isn't doing well as a one-off try
    for run in range(num_runs):
        with open(os.devnull, "w") as null:
            try:
                #get the output from angr and with tactics
                for tactic_cmd in tactic_cmds:
                    #using tuple: output, tactic
                    logger.debug(f'Run {run+1}: command: {tactic_cmd[0]}')
                    #run the command and handle subprocess exception
                    sub_proc_out = subproc_run(tactic_cmd[0],env,logger,null)
                    #grab from the local store, then clear the data store before the next run
                    results[tactic_cmd[1]][f'run {run+1}'] = api.local_retrieve(SUBPROC_B,oid)
                    results[tactic_cmd[1]][f'run {run+1} angr optimization test output'] = sub_proc_out
                    api.local_delete_data(SUBPROC_B,oid)
                #next we run w/o any tactic
                sub_proc_out = subproc_run(f"python3 {opt_script_full_path} {SUBPROC} {oid} {z3_timeout} {config.multiproc_max}",env,logger,null)
                results['with no tactic'][f'run {run+1}'] = api.local_retrieve(SUBPROC_B,oid)
                results['with no tactic'][f'run {run+1} angr optimization test output'] = sub_proc_out
                api.local_delete_data(SUBPROC_B,oid)
            except Exception as e:
                logger.error(f"Exception raised: {e},traceback: {traceback.format_exc()}")
                if "sub_proc_out" in locals():
                    logger.error(f"Subprocess output: {sub_proc_out}")
                api.local_delete_data(SUBPROC_B,oid)
                return False
    #get mean, standard deviation, t-test
    #check if we've done bare minimum amount of runs first
    if num_runs > 1:
        #TODO update this to calculate total seconds taken over the entire script's execution
        results['with no tactic']['mean seconds'] = statistics.mean(results['with no tactic']['total seconds'])
        results['with no tactic']['std. deviation'] = statistics.stdev(results['with no tactic']['total seconds'])
        for tactic in tactics:
            results[tactic]['mean seconds'] = statistics.mean(results[tactic]['total seconds'])
            results[tactic]['std. deviation'] = statistics.stdev(results['with no tactic']['total seconds'])
            t_test_p_value = scipy.stats.ttest_ind(results['with no tactic']['total seconds'], results[tactic]['total seconds'], equal_var=False).pvalue
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

def subproc_run(command, env, logger, null):
    sub_proc_out = ""
    try:
        sub_proc_out = subprocess.check_output(command, universal_newlines=True, shell=True, stderr=null,env=env)
    except subprocess.CalledProcessError as e:
        logger.error(f"Error occured running in subprocess: {e.output}")
        if e.returncode != 2:
            raise Exception(f"Subprocess data unrecoverable, return code {e.returncode}")
        else:
            logger.error(f"Traceback: {traceback.format_exc()}")
    return sub_proc_out
