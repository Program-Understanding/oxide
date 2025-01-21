AUTHOR="KEVAN"
NAME="angr_function_time_analyzer"
DESC="Analyze output from angr_function_time extractor module"

from oxide.core import api
import logging
import statistics
from time import sleep
import numpy
from output_assistant import output_data

logger = logging.getLogger(NAME)
opts_doc = {"timeout": {"type":int,"mangle":True,"default":600,"description":"timeout in seconds per function"},
            "summaries": {"type":bool, "mangle":False,"default":True,"description":"Include function summaries from function summary module as well"},
            "bins": {"type": int,"mangle":True,"default":3,"Description":"How many time bins"},
            "filter":{"type":bool,"mangle":False,"default":True,"Description":"Get rid of some of the less useful fields in the output"},
            "data-path":{"type":str,"mangle":False,"default":"","Description":"Path toa directory to output a csv file and some graphs to"},
            "allow-missing-ret":{"type":bool,"mangle":False,"default":False,"Description":"Allow functions in results that don't have a ret instruction"}}

def documentation():
    return {"description":DESC, "opts_doc": opts_doc, "private": False,"set":False, "atomic": True}

def find_bin_key(bins,time,timeout):
    for i in range(len(bins)):
        bn = bins[i]
        if i == 0:
            key = f"0-{bn}"
        else:
            key = f"{bins[i-1]}-{bn}"
        if time < bn:
            return key
    return f"> {timeout}"

def opcode_mapper(all_opcodes,df_opcodes,data_dict):
    #in order of function, should append the number of occurrences
    #of each opcode to the passed in dictionary
    for opcode in all_opcodes:
        data_dict[opcode] = []
    data_dict["j*"] = []
    data_dict["mov*"] = []
    data_dict["*xor*"] = []
    data_dict["cmov*"] = []
    for fun_opcode_dict in df_opcodes:
        j_star = 0
        mov_star = 0
        xor_star = 0
        cmov_star = 0
        for opcode in all_opcodes:
            if opcode in fun_opcode_dict:
                data_dict[opcode].append(fun_opcode_dict[opcode])
                if opcode.startswith("j"):
                    j_star += 1
                if opcode.startswith("mov"):
                    mov_star += 1
                if "xor" in opcode:
                    xor_star += 1
                if opcode.startswith("cmov"):
                    cmov_star += 1
            else:
                data_dict[opcode].append(0)
        data_dict["j*"].append(j_star)
        data_dict["mov*"].append(mov_star)
        data_dict["*xor*"].append(xor_star)
        data_dict["cmov*"].append(cmov_star)

def mapper(oid, opts, jobid=False):
    if api.exists(NAME,oid,opts):
        return oid
    if not opts["summaries"]:
        logger.error("module w/o summary is not implemented yet")
        return False
    if opts["bins"] < 3:
        logger.error("Not enough bins! Probably should use at least 3")
        return False
    results={}
    results["time_result"] = api.retrieve("angr_function_time",oid,opts)
    if results["time_result"] is None:
        logger.error(f"couldn't get time result for {oid}")
        return False
    results["opcode_by_func"] = api.retrieve("opcodes",oid,{"by_func":True})
    results["path_complexity"] = api.retrieve("path_complexity",oid,opts)
    if results["opcode_by_func"] is None or results["path_complexity"] is None:
        logger.error(f"couldn't get either path complexity or opcode by func for {oid}")
        return False
    while not api.store(NAME,oid,results,opts):
        sleep(1)
    return oid

def reducer(intermediate_output, opts, jobid):
    #gathering results into a dict to analyze
    complexity_vs_time = {}
    bins_w_time = {}
    functions_w_angr_errors = 0
    oids_w_angr_errors = 0
    functions_w_no_ret = 0
    if opts["data-path"]:
        import pandas as pd
        df_time = []
        df_bin = []
        df_complexity = []
        df_instructions = []
        df_imm = []
        df_mem = []
        df_reg = []
        df_index = []
        df_opcodes = []
        df_O = []
        all_opcodes = set()
    for complexity in ["simple", "moderate", "needs refactor", "complex"]:
        complexity_vs_time[complexity] = {"times":[],
                                          "instructions": [],
                                          "operands": {
                                              "imm":[],
                                              "reg":[],
                                              "mem":[]},
                                          "opcodes": {},
                                          "interesting":{}}

    #binkeys = [i*time_bin_size for i in range(1,opts["bins"]+1)]
    binkeys = [round(i,1) for i in numpy.logspace(numpy.log10(0.1),numpy.log10(600),num=opts["bins"]-1)]
    binkeys[-1] = opts["timeout"]
    for i in range(len(binkeys)):
        bn = binkeys[i]
        if i == 0:
            key = f"0-{bn}"
        else:
            key = f"{binkeys[i-1]}-{bn}"
        bins_w_time[key] = {"opcodes": {},
                            "operands": {
                                "imm":[],
                                "mem":[],
                                "reg":[]},
                            "complexity": {
                                "simple": 0,
                                "moderate": 0,
                                "needs refactor": 0,
                                "complex": 0
                            },
                            "num instructions": []
                            }
    bins_w_time[f"> {opts['timeout']}"] = {"opcodes": {},
                                           "operands": {
                                               "imm":[],
                                               "mem":[],
                                               "reg":[]},
                                           "complexity": {
                                               "simple": 0,
                                               "moderate": 0,
                                               "needs refactor": 0,
                                               "complex": 0
                                           },
                                           "num instructions": []
                                           }
    bins_w_time["low memory"] = {"opcodes": {},
                                           "operands": {
                                               "imm":[],
                                               "mem":[],
                                               "reg":[]},
                                           "complexity": {
                                               "simple": 0,
                                               "moderate": 0,
                                               "needs refactor": 0,
                                               "complex": 0
                                           },
                                           "num instructions": []
                                           }
    for oid in intermediate_output:
        if oid:
            time_result = api.get_field(NAME,oid,"time_result",opts)
            opcode_by_func = api.get_field(NAME,oid,"opcode_by_func",opts)
            complexitys = api.get_field(NAME,oid,"path_complexity",opts)
            if time_result is None or opcode_by_func is None:
                logger.warning(f"None result for {oid}")
                oids_w_angr_errors += 1
                continue
            for fun in time_result:
                f_dict = time_result[fun]
                if "error" in f_dict["angr seconds"]:
                    functions_w_angr_errors += 1
                    logger.info(f"Function has error in angr seconds and complexity {complexitys[fun]['O']}")
                    continue
                time = float(f_dict["angr seconds"].split(" ")[0])                
                f_bin = find_bin_key(binkeys,time,opts["timeout"])
                if "stopped early for" in f_dict and f_dict["stopped early for"] != "timed out":
                    functions_w_angr_errors += 1
                    f_bin = "low memory"
                complexity_level = f_dict["summary"]["complexity_desc"]
                complexity_vs_time[complexity_level]["times"].append(time)
                bins_w_time[f_bin]["complexity"][complexity_level] += 1
                if fun not in opcode_by_func:
                    logger.error(f"Need to delete {oid} from local store")
                opcodes = opcode_by_func[fun]
                #count the occurrence of opcodes
                mncs = {}
                for opcode in opcodes:
                    opcode = opcodes[opcode]
                    if not opcode in mncs:
                        mncs[opcode] = 1
                    else:
                        mncs[opcode] += 1
                fun_opcodes = {}
                for opcode in mncs:
                    if not opcode in complexity_vs_time[complexity_level]["opcodes"]:
                        complexity_vs_time[complexity_level]["opcodes"][opcode] = [mncs[opcode]]
                    else:
                        complexity_vs_time[complexity_level]["opcodes"][opcode].append(mncs[opcode])
                    if not opcode in bins_w_time[f_bin]["opcodes"]:
                        bins_w_time[f_bin]["opcodes"][opcode] = [mncs[opcode]]
                    else:
                        bins_w_time[f_bin]["opcodes"][opcode].append(mncs[opcode])
                    if opcode in fun_opcodes:
                        fun_opcodes[opcode] += 1
                    else:
                        fun_opcodes[opcode] = 1
                    if opts["data-path"]:
                        all_opcodes.add(opcode)
                if not "ret" in fun_opcodes:
                    functions_w_no_ret += 1
                    if not opts["allow-missing-ret"]:
                        continue
                if time > 5:
                    complexity_vs_time[complexity_level]["interesting"][fun] = {"instructions": f_dict["instructions"],
                                                                                "seconds": time,
                                                                                "from": oid,
                                                                                "complexity": f_dict["summary"]["complexity"]}
                num_insns = f_dict["summary"]["num_insns"]
                if opts["data-path"]:
                    df_time.append(time)
                    df_bin.append(f_bin)
                    df_complexity.append(complexity_level)
                    df_instructions.append(num_insns)
                    df_opcodes.append(fun_opcodes)
                    df_O.append(complexitys[fun]["O"])
                complexity_vs_time[complexity_level]["instructions"].append(num_insns)
                bins_w_time[f_bin]["num instructions"].append(num_insns)
                operands = f_dict["summary"]["operands"]
                for op_type in ["imm", "reg", "mem"]:
                    complexity_vs_time[complexity_level]["operands"][op_type].append(operands[op_type])
                    bins_w_time[f_bin]["operands"][op_type].append(operands[op_type])
                    if opts["data-path"]:
                        match op_type:
                            case "imm":
                                df_imm.append(operands[op_type])
                            case "mem":
                                df_mem.append(operands[op_type])
                            case "reg":
                                df_reg.append(operands[op_type])
                if opts["data-path"]:
                    df_index.append(f"{oid}{fun}")
    #eliminate empty bins
    for bn in bins_w_time:
        if not bins_w_time[bn]["opcodes"] and not bins_w_time[bn]["num instructions"]:
            bins_w_time[bn] = None
    #meta analysis on bins of times
    for bn in bins_w_time:
        if bins_w_time[bn] is None: continue
        if len(bins_w_time[bn]["num instructions"]) > 1:
            bins_w_time[bn]["instructions stats"] = {"mean instructions":statistics.mean(bins_w_time[bn]["num instructions"]),
                                                     "std dev":statistics.stdev(bins_w_time[bn]["num instructions"]),
                                                     "median": statistics.median(bins_w_time[bn]["num instructions"])}
        bins_w_time[bn]["number of functions"] = len(bins_w_time[bn]["num instructions"])
        for opcode in bins_w_time[bn]["opcodes"]:
            if len(bins_w_time[bn]["opcodes"][opcode]) > 1:
                bins_w_time[bn][f"opcode {opcode} stats"] = {
                    "mean": statistics.mean(bins_w_time[bn]["opcodes"][opcode]),
                    "std dev": statistics.stdev(bins_w_time[bn]["opcodes"][opcode]),
                    "median": statistics.median(bins_w_time[bn]["opcodes"][opcode])
                }
        for op_type in ["imm", "reg", "mem"]:
            if len(bins_w_time[bn]["operands"][op_type]) > 1:
                   bins_w_time[bn][f"operand type {op_type} stats"] = {
                       f"mean {op_type}": statistics.mean(bins_w_time[bn]["operands"][op_type]),
                       "std dev": statistics.stdev(bins_w_time[bn]["operands"][op_type]),
                       "median": statistics.median(bins_w_time[bn]["operands"][op_type])
                   }
    if opts["data-path"]:
        data_dict = {"time":df_time,
                     "bin":df_bin,
                     "complexity":df_complexity,
                     "instructions":df_instructions,
                     "imms":df_imm,
                     "mems":df_mem,
                     "regs":df_reg,
                     "O": df_O}
        opcode_mapper(all_opcodes,df_opcodes,data_dict)
        dataframe = pd.DataFrame(data_dict,
                                 index=df_index)
        from pathlib import Path
        outpath = Path(opts["data-path"])
        if not output_data(outpath,dataframe,list(bins_w_time.keys())):
            logger.error(f"Unable to save data to {outpath}!")
        else:
            logger.info(f"Data saved to {outpath} directory")
    if opts["filter"]:
        filtered_bins_w_time = {}
        for bn in bins_w_time:
            if bins_w_time[bn] is None: continue
            filtered_bins_w_time[bn]={}
            for key in list(bins_w_time[bn].keys()):
                if "stats" in key:
                    if "opcode" in key:
                        if not "opcodes" in filtered_bins_w_time[bn]: filtered_bins_w_time[bn]["opcodes"]={}
                        opcode : str = key.split(" ")[1]
                        filtered_bins_w_time[bn]["opcodes"][opcode] = bins_w_time[bn][key]
                    elif "operand" in key:
                        if not "operands" in filtered_bins_w_time[bn]: filtered_bins_w_time[bn]["operands"]={}
                        operand = key.split(" ")[2]
                        filtered_bins_w_time[bn]["operands"][operand] = bins_w_time[bn][key]
                    else:
                        filtered_bins_w_time[bn][key] = bins_w_time[bn][key]
            filtered_bins_w_time[bn]["number of functions"] = len(bins_w_time[bn]["num instructions"])
        filtered_complexity_vs_time = {}
        for complexity in ["simple", "moderate", "needs refactor", "complex"]:
            if len(complexity_vs_time[complexity]["instructions"]) > 1:
                filtered_complexity_vs_time[complexity] = {"instructions": {"mean": statistics.mean(complexity_vs_time[complexity]["instructions"]),
                                                                            "std dev": statistics.stdev(complexity_vs_time[complexity]["instructions"]),
                                                                            "median": statistics.median(complexity_vs_time[complexity]["instructions"])},
                                                           "times": {"mean": statistics.mean(complexity_vs_time[complexity]["times"]),
                                                                     "std dev": statistics.stdev(complexity_vs_time[complexity]["times"]),
                                                                     "median": statistics.median(complexity_vs_time[complexity]["times"])}}
            else:
                filtered_complexity_vs_time[complexity] = {"instructions": complexity_vs_time[complexity]["instructions"],
                                                           "times": complexity_vs_time[complexity]["times"]}
        if opts["data-path"]:
            return {"filtered_bins_w_time": filtered_bins_w_time, "filtered_complexity_vs_time": filtered_complexity_vs_time, "functions with angr errors": functions_w_angr_errors,"oids with angr errors": oids_w_angr_errors, "functions without ret instruction": functions_w_no_ret,"dataframe":dataframe}
        else:
            return {"filtered_bins_w_time": filtered_bins_w_time, "filtered_complexity_vs_time": filtered_complexity_vs_time, "functions with angr errors": functions_w_angr_errors,"oids with angr errors": oids_w_angr_errors, "functions without ret instruction": functions_w_no_ret}
    else:
        if opts["data-path"]:
            return {"bins_w_time": bins_w_time, "complexity_vs_time": complexity_vs_time,\
                "functions with angr errors": functions_w_angr_errors,"oids with angr errors": oids_w_angr_errors,\
                    "functions without ret instruction":functions_w_no_ret,\
                    "dataframe":dataframe}
        else:
            return {"bins_w_time": bins_w_time, "complexity_vs_time": complexity_vs_time,\
                "functions with angr errors": functions_w_angr_errors,"oids with angr errors": oids_w_angr_errors,\
                "functions without ret instruction":functions_w_no_ret}
