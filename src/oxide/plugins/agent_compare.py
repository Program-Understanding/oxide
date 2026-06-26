'''
Author: Nate Buck
Last updated June 17th, 2026
'''

import logging
import os
import subprocess
import shutil
import sys
import time
import ollama
import json
from dotenv import load_dotenv

NAME = "agent_compare"

logger = logging.getLogger(NAME)



def agent_compare(args, opts):
    '''
    This is a tool where you can choose an AI-powered reverse engineering tool
    to compare backdoored files to determine if an LLM is able to identify the backdoor.

    These are the following tools you can choose from (more to be added in the future):
    - 'oghidra'

    When inputting files, label which ones are clean and which ones are not using the
    following flags: 
    - 'clean'
    - 'backdoored'

    There are 4 evaluation techniques, each with a respective flag:
    - 'e1': Tool found the malicious function being deployed.
    - 'e2': Tool found the insertion point of the backdoor.
    - 'e3': Tool found the backdoor's trigger.
    - 'e4': Tool found the backdoor's technique.
    If you don't specify any of these flags, it will default to e1.

    You can also specify the amount of runs you want to do per binary. The default is 1. 
    To change it, add this flag to your command:
        '--runs=5'
    This must be an integer.

    You can also choose to have an llm parse the output and return the shortened summary
    for quicker review. To do this, simply add '--llm_outprocess=True'

    When using this plugin, provide the tool you want to use first, then the evaluation 
    level, the extra tools, and then clean file followed by one or more backdoored files. 
    For example: 
        
        tool_compare --runs=5 --tool=oghidra --eval=e3 &safe_files &backdoored_files

    Disclaimer:
        - For OGhidra to work correctly, you need to have all of its dependencies. The best 
        way to do this is to get a .venv in your oxide with all of the requirements for OGhidra.
        These can be found in OGhidra's requirements.txt file.
    '''
    from oxide.core import api
    llm_responses = {}
    eval_strats = {
        "e1": """
        If there is a backdoor, provide the specific malicious function that it comes from.
        Explain what caused you to think that it is a malicious function, citing what it does
        and why that goes against what the original program did.

        If you decide there is a backdoor, answer with the name of the function(s) and the relative offsets of the function(s).
        If you decide there is not a backdoor, simply put "there is no backdoor in this program".
        """,
        "e2": """
        If there is a backdoor, provide the insertion point of the backdoor. Like where backdoor capability enters pre-existing code.
        Describe the exact location (function, address range), structural evidence (such as from the call graph, control flow graph, etc.),
        evidence in the pseudo code, and what makes this differ from code surrounding it.

        If there is a backdoor, answer with where you believe it is.
        If you decide there is not a backdoor, simply put "there is no backdoor in this program".
        """,
        "e3": """
        If there is a backdoor, provide the condition or mechanism that causes that activates the malicious behavior. 
        Such as, but not limited to, any of the following:
        - Specific input value
        - Magic byte sequence
        - Time condition
        - Network packet
        - Environment variable
        - Authenticated command

        If you decide there is not a backdoor, simply put "there is no backdoor in this program".
        """, 
        "e4": """
        If there is a backdoor, find the backdoor's technique such as, but not limited to, the following:
        - persistence 
        - command and control (C2) communication
        - obfuscation and evasion 
        - Execution and injection
        - Credential and privilege abuse
        - Data exfiltration
        - Structural / Code-level red flags

        If you decide there is not a backdoor, simply put "there is no backdoor in this program".
        """
    }

    # Ensure oids are valid and two are provided
    if len(args) != 2:
        logger.critical("You must provide two arguments: one clean, either a file or collection, and one backdoored, either a file or collection.")
        return
    # Get clean files vs backdoored files
    clean_args = args[0]
    backdoored_args = args[1]

    valid_clean, invalid = api.valid_oids([clean_args])
    valid_backdoored, invalid = api.valid_oids([backdoored_args])

    clean_oids = api.expand_oids(valid_clean)
    backdoored_oids = api.expand_oids(valid_backdoored)

    # Get evaluation strategy or default to e1
    eval_strat = opts.get("eval", "e1")
    if eval_strat not in eval_strats:
        logger.warning(f"Invalid evaluation given: {eval_strat}. Using e1 instead.")
        eval_strat = "e1"
    
    # Total amount of OGhidra queries that will be done per binary
    try: 
        run_amt = int(opts.get("runs", 1))
        if run_amt <= 0:
            logger.warning("The amount of runs cannot be 0 or less than 0. Defaulting to 1.")
            run_amt = 1
    except:
        logger.warning("The amount of runs is invalid. Defaulting to 1.")
        run_amt = 1

    # Using Ghidra    
    if "oghidra" in opts.get("tool", ""):
        print("\n\tDon't forget to activate the venv before running!\n")
        ghidra_path = getattr(api, "ghidra_path", None)
        print(f"Ghidra path: {ghidra_path}")
        if not ghidra_path:
            logger.critical("Ghidra path not found. Please ensure it is in your config file.")
            return
        ghidra_projects_path = api.scratch_dir
        print(f"Ghidra projects path: {ghidra_projects_path}")
        if not ghidra_projects_path:
            logger.critical("Ghidra project path not found. Please ensure it is in your config file.")
            return
        oghidra_path = getattr(api, "oghidra_path", None)
        print(f"OGhidra path: {oghidra_path}")
        if not oghidra_path:
            logger.critical("OGhidra path not found. Please ensure it is in your config file.")
            return
        # Get OGhidra's .env file for Ollama info
        oghidra_env = os.path.join(oghidra_path, ".env")
        load_dotenv(dotenv_path=oghidra_env)

        # Set up the generic project to be used
        project_dir = os.path.join(ghidra_projects_path, "project_name")
        project_file = project_dir + ".gpr"
        project_repo = project_dir + ".rep"

        # Remove previous execution of Ghidra on generic projects 
        if (os.path.exists(project_file)):
            os.remove(project_file)
            shutil.rmtree(project_repo)

        # Make tmp files for each of the clean files
        clean_tmp_files = []
        for i, oid in enumerate(clean_oids):
            file_name = api.get_field("file_meta", oid, "names").pop()
            clean_tmp_files.append(os.path.splitext(os.path.basename(file_name))[0])
            data = api.get_field(api.source(oid), oid, "data", {})
            if not data:
                logger.warning(f"No data in {file_name}")
                continue
            tmp_file = api.tmp_file(file_name, data)
            # Analyze the clean binary to create the clean analysis in Ghidra. Uses enumerate to label each of them.
            result = subprocess.run(["bash", ghidra_path + "/support/analyzeHeadless", ghidra_projects_path, f"project_name/clean{i + 1}", "-overwrite", "-import", tmp_file] , capture_output=True, text=True)
            if result.returncode != 0:
                print(f"Error running headless analysis on clean: {result.stderr}")
                logger.critical("analyzeHeadless failed")
                return
            else:
                print(f"Analysis on clean file {i + 1} succeeded.{result.stdout}")

        # Make tmp files for each of the backdoored files
        backdoored_tmp_files = []
        for i, oid in enumerate(backdoored_oids):
            file_name = api.get_field("file_meta", oid, "names").pop()
            backdoored_tmp_files.append(os.path.splitext(os.path.basename(file_name))[0])
            data = api.get_field(api.source(oid), oid, "data", {})
            if not data:
                logger.warning(f"No data in {file_name}")
                continue
            tmp_file = api.tmp_file(file_name, data)
            # Analyze all of the backdoored programs entered. Uses enumerate to label each of them as well.
            result = subprocess.run(["bash", ghidra_path + "/support/analyzeHeadless", ghidra_projects_path, f"project_name/backdoored{i + 1}", "-overwrite", "-import", tmp_file] , capture_output=True, text=True)
            if result.returncode != 0:
                print(f"Error running headless analysis on backdoored: {result.stderr}")
                logger.critical("analyzeHeadless failed")
                return
            else:
                print(f"Analysis on backdoored file {i + 1} succeeded.{result.stdout}")

        # Open Ghidra
        result = subprocess.run([ghidra_path + "/ghidraRun", project_file] , capture_output=True, text=True)
        if result.returncode != 0:
            logger.critical("Ghidra failed to open.")
            return
        # Quick pause to let user open the files in Ghidra to allow OGhidra to connect.
        # Maybe add ability to be able to distinguish between what is being opened regardless of the order.
        input("Open new testing files. Open clean first then open the backdoored ones after. Press enter to continue when ready.\n")

        # Using sys to import necessary OGhidra modules
        sys.path.insert(0, oghidra_path)

        from src.bridge import Bridge
        from src.config import get_config

        # Use config in Bridge and using include_capabilities to ensure ability for tool use.
        config = get_config()
        bridge = Bridge(config=config, include_capabilities=True)

        # Get all ports open and ensure there are the right amount open before continuing
        total_instances = bridge.ghidra.active_instances
        if not total_instances:
            logger.critical("There are no active Ghidra instances open. Open the ones you want to test.")
            return
        ports = sorted(total_instances.keys())
        all_oids = clean_oids + backdoored_oids
        if not len(ports) == len(all_oids):
            logger.critical(f"Error. Mismatched amount of ports vs files desired.")
            return
        # Getting the file type for each file to ensure correct tool usage
        file_info = {}
        for i, oid in enumerate(all_oids):
            file_info[oid] = api.get_field("src_type", oid, "type")

        prompt = f"""
        You are an experienced reverse engineer and binary security analyst. 
        Determine if this binary has a backdoor.

        {eval_strats[eval_strat]}

        File type: 
        """
        
        # Loop to use OGhidra on each open instance ensuring each output is stored into the llm_responses dict.
        for n, port in enumerate(ports):
            if reset_bridge_state(bridge) != 1:
                logger.warning("This port will be skipped due to issues clearing the bridge. Will continue in 5 seconds.")
                time.sleep(5)
                continue
            bridge.ghidra.instances_use(port)
            # 'malware' mode allows OGhidra to use malware pattern detection and severity matching for different
            # malicious techniques that make it useful for determining backdoor existence over other modes
            bridge.set_task_mode(enabled=True, mode="malware")
            # Since we are using all_oids, the clean files will be at the beginning
            clean = n < len(clean_oids)
            file_name = os.path.basename(api.get_field("file_meta", all_oids[n], "names").pop())
            if clean:
                file_label = f"clean_{file_name}"
            else:
                file_label = f"backdoored_{file_name}"
            
            # Creating a dict of dicts in order to keep files and runs straight
            llm_responses[file_label] = {}
            width = 80
            # Allows multiple runs on the same file
            for run in range(run_amt):
                # Gives the user a visual of where the program is at
                print("=" * width)
                print(f"\t{file_name} run #{run + 1}")
                print("=" * width)
                # Queries the model with the prompt and file info before returning to llm_responses
                response = bridge.process_query(prompt + str(file_info[all_oids[n]]))
                llm_responses[file_label][f"Run {run + 1}"] = response
        if opts.get("llm_outprocess", False) is True:
            _llm_outprocessing(llm_responses, eval_strat)
        else:
            _get_results(llm_responses, eval_strat)
    return llm_responses

# Gets results using programatic pattern matching
def _get_results(llm_responses, eval_strat):
    width = 80

    print("\n" + "=" * width)
    print(f"    RESULTS     |   EVALUATION STRATEGY: {eval_strat}")
    print("\n" + "=" * width)

    summary_data = {}

    for file, run_dict in llm_responses.items():
        clean = (file.startswith("clean_"))
        if clean:
            print("\n" + "-" * width)
            print(f"CLEAN FILE: {file}")
            print("\n" + "-" * width)
        else:
            print("\n" + "-" * width)
            print(f"BACKDOORED FILE: {file}")
            print("\n" + "-" * width)
        
        found_backdoor_runs = []

        for run_name, response_txt in run_dict.items():
            print(f"\n\t<<< {run_name} >>>\n\n")
            print(response_txt)
            # Pattern matching to seen patterns of how OGhidra likes to say there is no backdoor
            # If not in this list, it most likely found a backdoor
            if not any(phrase in response_txt.lower() for phrase in ["no backdoor", "there is no backdoor", "not a backdoor", "no proof of a backdoor", "no definitive evidence of a backdoor", "no pre-installed backdoor exists", ]):
                found_backdoor_runs.append(run_name)
        # Uses this dict to keep track of all of the info needed for the final summary
        summary_data[file] = {
                "clean": clean,
                "total_runs": len(run_dict),
                "caught": found_backdoor_runs
            }
        
        
    print("\n" + "." * (width))
    print(f"\nFinal Summary")
    # Counts all of the backdoors found and labels them either
    # as backdoors or false positives depending on what kind
    # of file it was counted in. Also returns which run it 
    # was flagged in for further analysis.
    for file, stats in summary_data.items():
        total = stats["total_runs"]

        print(f"\n\n\tAnalysis on {file}:")

        if stats["clean"]:
            print(f"\n\t - False positives: {len(stats['caught'])}/{total}")
            if len(stats["caught"]) > 0:
                print(f"\n\t\t - False positives found here: {', '.join(stats['caught'])}")
            else:
                print(f"\n\t - Agent successfully labeled this as clean.")
            
        else:
            print(f"\n\t - Backdoor detected {len(stats['caught'])}/{total}")   
            if len(stats["caught"]) > 0:
                print(f"\n\t\t - Backdoors detected here: {', '.join(stats['caught'])}")
            else:
                print(f"\n\t - Agent failed to find the backdoor completely.")
            
        print("\n" + "-" * (width))
    print("\n" + "=" * width)

# When doing multiple runs, you must clear the bridge to 
# ensure the model isn't using previously gathered information.
def reset_bridge_state(bridge):
    try:
        bridge.clear_cache()
        bridge.session.analysis_state.functions_decompiled.clear()
        bridge.session.analysis_state.functions_renamed.clear()
        bridge.session.analysis_state.comments_added.clear()
        bridge.session.analysis_state.functions_analyzed.clear()
        bridge.session.analysis_state.cached_results.clear()
        bridge.session.messages.clear()    
        bridge.session.tool_executions.clear()
        bridge.executed_tools = set()
        bridge.step_result_map = {}
        return 1
    except Exception as e:
        logger.warning(f"There was an error resetting the bridge: {type(e).__name__}: {e}")
        return 0
    
# Gets the results using an LLM for pattern matching.
# This is the better way since OGhidra doesn't always
# listen to direct prompting.
def _llm_outprocessing(llm_responses, eval_strat):
    width = 80

    print("\n" + "=" * width)
    print(f"    RESULTS     |   EVALUATION STRATEGY: {eval_strat}")
    print("\n" + "=" * width)

    summary_data = {}

    for file, run_dict in llm_responses.items():
        clean = (file.startswith("clean_"))
        if clean:
            print("\n" + "-" * width)
            print(f"CLEAN FILE: {file}")
            print("\n" + "-" * width)
        else:
            print("\n" + "-" * width)
            print(f"BACKDOORED FILE: {file}")
            print("\n" + "-" * width)
        
        found_backdoor_runs = []

        for run_name, response_txt in run_dict.items():
            print(f"\n\t<<< {run_name} >>>\n\n")
            print(response_txt)
            prompt = f"""
            You are tasked to do two things:
            1. Find the section explicitly starting with the header '### Conclusion'. Copy everything under that header verbatim and put it into the 'conclusion' JSON field.
            2. Evaluate the entire text to determine if a backdoor is confirmed present. 

            Text to analyze:
            \"\"\"{response_txt}\"\"\"

            Respond ONLY in this JSON format:
            {{
                "backdoor_found": True/False,
                "conclusion": "The text from the '### Conclusion' section goes here"
            }} 
            Do not put a preamble or markdown markings such as (''').
            """

            
            try:
                model_name = os.environ.get("OLLAMA_MODEL", "qwen3-coder-next")
                # Using Ollama and having it with a low temperature to
                # make more logical matches and using format to output as json
                # for easy parsing.
                ollama_host = os.environ.get("OLLAMA_HOST", "http://localhost:11434")
                client = ollama.Client(host=ollama_host)
                response = client.chat(
                    model=model_name,
                    messages=[{"role":"user", "content":prompt}],
                    options={"temperature": 0.0},
                    format="json",
                )

                result = json.loads(response.message.content)

                # Just showing conclusion to get a quick overview of each run
                print(result.get("conclusion"))
                # Checks for if there was a backdoor using the json format
                # with an option for if it doesn't write it like a boolean
                if result.get("backdoor_found") is True or str(result.get("backdoor_found").lower() == "true"):
                    found_backdoor_runs.append(run_name)
            except Exception as e:
                print(f"Error processing with the llm for {run_name}: {e}")
                
        summary_data[file] = {
                "clean": clean,
                "total_runs": len(run_dict),
                "caught": found_backdoor_runs
            }    
        
        
    print("\n" + "." * (width))
    print(f"\nFinal Summary")
    
    for file, stats in summary_data.items():
        total = stats["total_runs"]

        print(f"\n\n\tAnalysis on {file}:")

        if stats["clean"]:
            print(f"\n\t - False positives: {len(stats['caught'])}/{total}")
            if len(stats["caught"]) > 0:
                print(f"\n\t\t - False positives found here: {', '.join(stats['caught'])}")
            else:
                print(f"\n\t - Agent successfully labeled this as clean.")
            
        else:
            print(f"\n\t - Backdoor detected {len(stats['caught'])}/{total}")   
            if len(stats["caught"]) > 0:
                print(f"\n\t\t - Backdoors detected here: {', '.join(stats['caught'])}")
            else:
                print(f"\n\t - Agent failed to find the backdoor completely.")
            
        print("\n" + "-" * (width))
    print("\n" + "=" * width)

exports = [agent_compare]