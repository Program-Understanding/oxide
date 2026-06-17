'''
Author: Nate Buck
Last updated June 17th, 2026
'''

import logging
import os
import subprocess
import shutil
import sys

from oxide.core.oxide import api

logger = logging.getLogger(__name__)

def tool_compare(args, opts):
    '''
    This is a tool where you can choose an AI-powered reverse engineering tool
    to compare backdoored files to determine if an LLM is able to identify the backdoor.

    These are the following tools you can choose from (more to be added in the future):
    - 'oghidra'

    There are 4 evaluation techniques, each with a respective flag:
    - 'e1': Tool found the malicious function being deployed.
    - 'e2': Tool found the insertion point of the backdoor.
    - 'e3': Tool found the backdoor's trigger.
    - 'e4': Tool found the backdoor's technique.
    If you don't specify any of these flags, it will default to e1.

    When using this plugin, provide the tool you want to use first, then the evaluation 
    level, the extra tools, and then clean file followed by one or more backdoored files. 
    For example: 
        
        tool_compare --tool=oghidra --eval=e3 ^clean_file.exe ^backdoored_file.exe

    You can also add multiple backdoored files to compare against the clean file, like this:
        
        tool_compare --tool=oghidra --eval=e3 ^clean_file.exe ^backdoored_file1.exe ^backdoored_file2.exe
    '''
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

    # Ensure oids are valid and at least two are provided
    oids, invalid = api.valid_oids(args)
    oids = api.expand_oids(oids)
    if len(oids) < 2:
        logger.critical("""You must provide at least one valid clean and one valid modified program to compare.
                        Check that your input is valid.""")
        return
    
    # Get evaluation strategy or default to e1
    eval_strat = opts.get("eval", "e1")
    if eval_strat not in eval_strats:
        logger.warning(f"Invalid evaluation given: {eval_strat}. Using e1 instead.")
        eval_strat = "e1"

      # Using Ghidra
    if "oghidra" in opts.get("tool", ""):
        # Checking paths (TODO: Fix api.api. calls when possible)
        oghidra_path = api.api.oghidra_path
        if not oghidra_path:
            logger.critical("OGhidra path not found. Please ensure it is in your config file.")
            return
        ghidra_path = api.api.ghidra_path
        print(ghidra_path)
        if not ghidra_path:
            logger.critical("Ghidra path not found. Please ensure it is in your config file.")
        ghidra_projects_path = api.api.scratch_dir
        print(ghidra_projects_path)
        if not ghidra_projects_path:
            logger.critical("Ghidra project path not found. Please ensure it is in your config file.")
            return
        # Get OGhidra's .env file for Ollama info
        oghidra_env = os.path.join(oghidra_path, ".env")
        subprocess.run(["cp", oghidra_env, ".env"]) 

        # Set up the generic project to be used
        project_dir = os.path.join(ghidra_projects_path, "project_name")
        project_file = project_dir + ".gpr"
        project_repo = project_dir + ".rep"

        # Remove previous execution of Ghidra on generic projects
        if (os.path.exists(project_file)):
            os.remove(project_file)
            shutil.rmtree(project_repo)
        # Get all of the original file paths for the oids
        file_paths = []
        for file in oids:
            true_file = api.retrieve("original_path", file)
            file_paths.append(list(true_file[file])[0])

        # Analyze the clean binary to create the clean analysis in Ghidra
        result = subprocess.run(["bash", ghidra_path + "/support/analyzeHeadless", ghidra_projects_path, "project_name/clean", "-overwrite", "-import", file_paths[0]] , capture_output=True, text=True)
        if result.returncode != 0:
            print(f"Error running headless analysis on clean: {result.stderr}")
            logger.critical("analyzeHeadless failed")
        else:
            print(f"Analysis on clean file succeeded.{result.stdout}")
        # Analyze all of the backdoored programs entered. Uses enumerate to label each of them.
        for j, file in enumerate(file_paths[1:]):
            result = subprocess.run(["bash", ghidra_path + "/support/analyzeHeadless", ghidra_projects_path, f"project_name/backdoored{j + 1}", "-overwrite", "-import", file] , capture_output=True, text=True)
            if result.returncode != 0:
                print(f"Error running headless analysis on backdoored: {result.stderr}")
                logger.critical("analyzeHeadless failed")
            else:
                print(f"Analysis on backdoored file {j+1} succeeded.{result.stdout}")
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
        if not len(ports) == len(file_paths):
            missing = len(file_paths) - len(ports)
            logger.warning(f"Error. Mismatched amount of ports vs files desired. Open {missing} more file(s) in Ghidra then press enter.")
            input()
        # Getting the file type for each file to ensure correct tool usage
        file_info = {}
        for i, file in enumerate(oids):
            file_info[os.path.basename(file_paths[i])] = api.api.get_field("src_type", file, "type")

        prompt = f"""
        You are an experienced reverse engineer and binary security analyst. 
        Determine if this binary has a backdoor.

        {eval_strats[eval_strat]}

        File type: 
        """
        
        # Loop to use OGhidra on each open instance ensuring each output is stored into the llm_responses dict.
        clean = True
        for n, port in enumerate(ports):
            bridge.ghidra.instances_use(port)
            key = os.path.basename(file_paths[n])
            bridge.set_task_mode(enabled=True, mode="malware")
            response = bridge.process_query(prompt + str(file_info[key]))
            if clean:
                llm_responses["clean"] = response
                clean = False
            else:
                llm_responses[os.path.basename(file_paths[n]) + str(n)] = response
        # Remove OGhidra .env file because it is no longer needed
        subprocess.run("bash", "rm", ".env")
    return llm_responses

exports = [tool_compare]