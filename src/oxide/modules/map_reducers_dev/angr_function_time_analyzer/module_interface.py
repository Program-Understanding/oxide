AUTHOR="KEVAN"
NAME="angr_function_time_analyzer"
DESC="Analyze output from angr_function_time extractor module"

from oxide.core import api
import logging
import statistics

logger = logging.getLogger(NAME)
opts_doc = {"timeout": {"type":int,"mangle":True,"default":600,"description":"timeout in seconds per function"},
            "summaries": {"type":bool, "mangle":False,"default":True,"description":"Include function summaries from function summary module as well"},
            "bins": {"type": int,"mangle":True,"default":3,"Description":"How many time bins"},
            "filter":{"type":bool,"mangle":False,"default":True,"Description":"Get rid of some of the less useful fields in the output"}}

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
        return False
    results["opcode_by_func"] = api.retrieve("opcodes",oid,{"by_func":True})
    if results["opcode_by_func"] is None:
        return False
    api.store(NAME,oid,results,opts)
    return oid

def reducer(intermediate_output, opts, jobid):
    #gathering results into a dict to analyze
    complexity_vs_time = {}
    bins_w_time = {}
    functions_w_angr_errors = 0
    for complexity in ["simple", "moderate", "needs refactor", "complex"]:
        complexity_vs_time[complexity] = {"times":[],
                                          "instructions": [],
                                          "operands": {
                                              "imm":[],
                                              "reg":[],
                                              "mem":[]},
                                          "opcodes": {},
                                          "interesting":{}}

    time_bin_size = opts["timeout"] / opts["bins"]
    binkeys = [i*time_bin_size for i in range(1,opts["bins"]+1)]
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
    for oid in intermediate_output:
        if oid:
            time_result = api.get_field(NAME,oid,"time_result",opts)
            opcode_by_func = api.get_field(NAME,oid,"opcode_by_func",opts)
            if time_result is None or opcode_by_func is None:
                logger.warning(f"None result for {oid}")
                continue
            for fun in time_result:
                f_dict = time_result[fun]
                if "error" in f_dict["angr seconds"]:
                    functions_w_angr_errors += 1
                    continue
                time = float(f_dict["angr seconds"].split(" ")[0])
                f_bin = find_bin_key(binkeys,time,opts["timeout"])
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
                for opcode in mncs:
                    if not opcode in complexity_vs_time[complexity_level]["opcodes"]:
                        complexity_vs_time[complexity_level]["opcodes"][opcode] = [mncs[opcode]]
                    else:
                        complexity_vs_time[complexity_level]["opcodes"][opcode].append(mncs[opcode])
                    if not opcode in bins_w_time[f_bin]["opcodes"]:
                        bins_w_time[f_bin]["opcodes"][opcode] = [mncs[opcode]]
                    else:
                        bins_w_time[f_bin]["opcodes"][opcode].append(mncs[opcode])
                if time > 5:
                    complexity_vs_time[complexity_level]["interesting"][fun] = {"instructions": f_dict["instructions"],
                                                                                "seconds": time,
                                                                                "from": oid,
                                                                                "complexity": f_dict["summary"]["complexity"]}
                num_insns = f_dict["summary"]["num_insns"]
                complexity_vs_time[complexity_level]["instructions"].append(num_insns)
                bins_w_time[f_bin]["num instructions"].append(num_insns)
                operands = f_dict["summary"]["operands"]
                for op_type in ["imm", "reg", "mem"]:
                    complexity_vs_time[complexity_level]["operands"][op_type].append(operands[op_type])
                    bins_w_time[f_bin]["operands"][op_type].append(operands[op_type])
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
    if opts["filter"]:
        filtered_bins_w_time = {}
        for bn in bins_w_time:
            if bins_w_time[bn] is None: continue
            filtered_bins_w_time[bn]={}
            for key in list(bins_w_time[bn].keys()):
                if "stats" in key:
                    if "opcode" in key:
                        if not "opcodes" in filtered_bins_w_time[bn]: filtered_bins_w_time[bn]["opcodes"]={}
                        opcode = key.split(" ")[1]
                        filtered_bins_w_time[bn]["opcodes"][opcode] = bins_w_time[bn][key]
                    elif "operand" in key:
                        if not "operands" in filtered_bins_w_time[bn]: filtered_bins_w_time[bn]["operands"]={}
                        operand = key.split(" ")[2]
                        filtered_bins_w_time[bn]["operands"][operand] = bins_w_time[bn][key]
                    else:
                        filtered_bins_w_time[bn][key] = bins_w_time[bn][key]
        filtered_complexity_vs_time = {}
        for complexity in ["simple", "moderate", "needs refactor", "complex"]:
            if len(complexity_vs_time[complexity]["instructions"]) > 1:
                filtered_complexity_vs_time[complexity] = {"instructions": {"mean": statistics.mean(complexity_vs_time[complexity]["instructions"]),
                                                                                 "std dev": statistics.stdev(complexity_vs_time[complexity]["instructions"])},
                                                           "times": {"mean": statistics.mean(complexity_vs_time[complexity]["times"]),
                                                                          "std dev": statistics.stdev(complexity_vs_time[complexity]["times"])}}
            else:
                filtered_complexity_vs_time[complexity] = {"instructions": complexity_vs_time[complexity]["instructions"],
                                                           "times": complexity_vs_time[complexity]["times"]}
        return {"filtered_bins_w_time": filtered_bins_w_time, "filtered_complexity_vs_time": filtered_complexity_vs_time, "functions with angr errors": functions_w_angr_errors}
    else:
        return {"bins_w_time": bins_w_time, "complexity_vs_time": complexity_vs_time,\
            "functions with angr errors": functions_w_angr_errors}
