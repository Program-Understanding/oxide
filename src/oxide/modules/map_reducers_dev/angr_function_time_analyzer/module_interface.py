AUTHOR="KEVAN"
NAME="angr_function_time_analyzer"
DESC="Analyze output from angr_function_time extractor module"

from oxide.core import api
import logging
import statistics
from time import sleep
import numpy
from typing import Any, TypedDict
import pandas as pd
from output_assistant import output_data, analyze_dataframe

logger = logging.getLogger(NAME)
opts_doc = {"timeout": {"type":int,"mangle":True,"default":600,"description":"timeout in seconds per function"},
            "bins": {"type": int,"mangle":True,"default":3,"Description":"How many time bins"},
            "data-path":{"type":str,"mangle":False,"default":"","Description":"Path to a directory to output a csv file and some graphs to"},
            "allow-missing-ret":{"type":bool,"mangle":False,"default":False,"Description":"Allow functions in results that don't have a ret instruction"},
            "allow-low-memory":{"type":bool,"mangle":False,"default":False,"Description":"Allow functions in results which ran into memory issues within angr"}}

def documentation():
    return {"description":DESC, "opts_doc": opts_doc, "private": False,"set":False, "atomic": True}

class OperandsDict(TypedDict):
    imm : list[int]
    mem : list[int]
    reg : list[int]

ComplexityDict = TypedDict(
    "ComplexityDict",
    {
        "simple": int,
        "moderate" : int,
        "needs refactor": int,
        "complex": int
    }
    )
Bins_w_time = TypedDict(
    "Bins_w_time",
    {
        "opcodes": dict[str,int],
        "operands": OperandsDict,
        "complexity": ComplexityDict,
        "num instructions": list[int],
        "num params": list[int]
    }
)

Opts = TypedDict(
    "Opts",
    {
        "timeout": int,
        "bins": int,
        "data-path": str,
        "allow-missing-ret": bool,
        "allow-low-memory": bool,
    }
)

class Summary(TypedDict):
    offset: int
    signature: str
    num_insns: int
    complexity: int
    complexity_desc: str
    operands: dict[str,int]
    params: list[tuple[int,str]]

F_Dict = TypedDict(
    "F_Dict",
    {
        "summary": Summary,
        "angr seconds": str,
        "instructions": dict[int,str]
        
    }
)    
    
def find_bin_key(bins : list[int] ,time:float,timeout:int) -> str:
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

def mapper(oid:str, opts: dict[str,Any], jobid=False):
    if api.exists(NAME,oid,opts):
        return oid
    if not opts["data-path"]:
        logger.error("Need a data path to output to!")
        return False
    if opts["bins"] < 3:
        logger.error("Not enough bins! Probably should use at least 3")
        return False
    results={}
    results["time_result"] = api.retrieve("angr_function_time",oid,opts)
    if results["time_result"] is None:
        logger.error(f"couldn't get time result for {oid}")
        return False
    for fun in results["time_result"]:
        if results["time_result"][fun]["summary"]["complexity_desc"] is None:
            logger.error(f"complexity description for {fun} in {oid} is none")
            return False
    results["opcode_by_func"] = api.retrieve("opcodes",oid,{"by_func":True})
    results["path_complexity"] = api.retrieve("path_complexity",oid,opts)
    if results["opcode_by_func"] is None or results["path_complexity"] is None:
        logger.error(f"couldn't get either path complexity or opcode by func for {oid}")
        return False
    while not api.store(NAME,oid,results,opts):
        sleep(1)
    return oid

def reducer(intermediate_output : list[str], opts : Opts, jobid):
    #gathering results into a dict to analyze
    complexity_vs_time = {}
    bins_w_time : dict[str,Bins_w_time | None] = {}
    functions_w_angr_errors = 0
    oids_w_angr_errors = 0
    functions_w_no_ret = 0
    functions_w_none_complexity = 0
    total_functions = 0
    functions_analyzed = 0
    functions_w_memory_issues = 0
    df_time = []
    df_bin = []
    df_cyclo_complexity_level = []
    df_cyclo_complexity_int = []
    df_instructions = []
    df_imm = []
    df_mem = []
    df_reg = []
    df_index = []
    df_opcodes = []
    df_O = []
    df_O_degree = []
    all_opcodes = set()
    df_num_params = []
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
    binkeys : list[int] = [round(i,1) for i in numpy.logspace(numpy.log10(0.3),numpy.log10(600),num=opts["bins"]-1)]
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
                            "num instructions": [],
                            "num params": []
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
                                           "num instructions": [],
                                           "num params": []
                                           }
    if opts["allow-low-memory"]:
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
                                     "num instructions": [],
                                     "num params": []
                                     }
    for oid in intermediate_output:
        if oid:
            time_result : dict[int, F_Dict] | None = api.get_field(NAME,oid,"time_result",opts)
            opcode_by_func : dict[int, dict[str,str]] | None  = api.get_field(NAME,oid,"opcode_by_func",opts)
            complexitys : dict[str, Any] | None = api.get_field(NAME,oid,"path_complexity",opts)
            if time_result is None or opcode_by_func is None or complexitys is None:
                logger.warning(f"None result for {oid}")
                oids_w_angr_errors += 1
                continue
            for fun in time_result:
                total_functions += 1
                f_dict : F_Dict = time_result[fun]
                if "error" in f_dict["angr seconds"]:
                    functions_w_angr_errors += 1
                    logger.info(f"Function has error in angr seconds and complexity {complexitys[fun]['O']}")
                    continue
                if f_dict["summary"]["complexity_desc"] is None:
                    logger.error(f"complexity desc is none for {oid} function {fun}")
                    functions_w_none_complexity += 1
                    continue
                #need to assess whether we have a ret in the function or if we should skip it
                opcodes : dict[str, str] = opcode_by_func[fun]
                num_params = len(f_dict["summary"]["params"])
                #count the occurrence of opcodes
                mncs : dict[str, int] = {}
                for opcode in opcodes:
                    opcode = opcodes[opcode]
                    if not opcode in mncs:
                        mncs[opcode] = 1
                    else:
                        mncs[opcode] += 1
                fun_opcodes = {}
                for opcode in mncs:
                    if opcode in fun_opcodes:
                        fun_opcodes[opcode] += 1
                    else:
                        fun_opcodes[opcode] = 1
                #after we've tracked the opcodes of this function, we can check
                #if it has a ret or not
                if not "ret" in fun_opcodes:
                    functions_w_no_ret += 1
                    if not opts["allow-missing-ret"]:
                        continue
                #add the unique opcodes to our list of all opcodes
                for opcode in mncs:
                    all_opcodes.add(opcode)
                #check if we have less than 10 instructions and no jump,
                #we should just skip these kinds of functions
                if f_dict["summary"]["num_insns"] < 10:
                    intersting = False
                    for opcode in fun_opcodes:
                        if opcode.startswith("j"):
                            intersting = True
                            break
                    if intersting:
                        continue
                time : float = float(f_dict["angr seconds"].split(" ")[0])
                f_bin: str = find_bin_key(binkeys,time,opts["timeout"])
                if "stopped early for" in f_dict and f_dict["stopped early for"] != "timed out":
                    functions_w_memory_issues += 1
                    if not opts["allow-low-memory"]:
                        continue
                    f_bin = "low memory"
                complexity_level = f_dict["summary"]["complexity_desc"]
                cyclomatic_complexity = f_dict["summary"]["complexity"]
                complexity_vs_time[complexity_level]["times"].append(time)
                bins_w_time[f_bin]["complexity"][complexity_level] += 1
                if fun not in opcode_by_func:
                    logger.error(f"Need to delete {oid} from local store")

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
                df_time.append(time)
                df_bin.append(f_bin)
                df_cyclo_complexity_level.append(complexity_level)
                df_cyclo_complexity_int.append(cyclomatic_complexity)
                df_instructions.append(num_insns)
                df_opcodes.append(fun_opcodes)
                df_num_params.append(num_params)
                big_o = complexitys[fun]["O"]
                if "n**" in big_o:
                    big_o_degree = int(big_o[5:].strip(")"))
                    big_o = "O(n**x)"
                elif "O(0" in big_o:
                    big_o = "Error"
                    big_o_degree = None
                elif "O(1" in big_o:
                    big_o_degree = 0
                elif "O(n)" in big_o:
                    big_o_degree = 1
                else:
                    big_o_degree = None
                df_O.append(big_o)
                df_O_degree.append(big_o_degree)
                complexity_vs_time[complexity_level]["instructions"].append(num_insns)
                bins_w_time[f_bin]["num instructions"].append(num_insns)
                operands = f_dict["summary"]["operands"]
                for op_type in ["imm", "reg", "mem"]:
                    complexity_vs_time[complexity_level]["operands"][op_type].append(operands[op_type])
                    bins_w_time[f_bin]["operands"][op_type].append(operands[op_type])
                    match op_type:
                        case "imm":
                            df_imm.append(operands[op_type])
                        case "mem":
                            df_mem.append(operands[op_type])
                        case "reg":
                            df_reg.append(operands[op_type])
                df_index.append(f"{oid}{fun}")
                functions_analyzed+=1
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
    data_dict = {"time":df_time,
                 "bin":df_bin,
                 "cyclomatic complexity": df_cyclo_complexity_int,
                 "cyclomatic complexity level":df_cyclo_complexity_level,
                 "Big O": df_O,
                 "Big O degree": df_O_degree,
                 "instructions":df_instructions,
                 "imms":df_imm,
                 "mems":df_mem,
                 "regs":df_reg,
                 "num params": df_num_params
                 }
    opcode_mapper(all_opcodes,df_opcodes,data_dict)
    dataframe = pd.DataFrame(data_dict,
                             index=df_index)
    from pathlib import Path
    outpath = Path(opts["data-path"])
    if not output_data(outpath,dataframe,list(bins_w_time.keys())):
        logger.error(f"Unable to save data to {outpath}!")
    else:
        logger.info(f"Data saved to {outpath} directory")
        df = analyze_dataframe(outpath,dataframe,list(all_opcodes))
        dataframe = df
        logger.info(f"Analysis saved to {outpath} directory")

    filtered_bins_w_time : dict[str,dict[str,dict[str,float]]] = {}
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
                    operand : str = key.split(" ")[2]
                    filtered_bins_w_time[bn]["operands"][operand] = bins_w_time[bn][key]
                else:
                    filtered_bins_w_time[bn][key] = bins_w_time[bn][key]
        filtered_bins_w_time[bn]["number of functions"] = len(bins_w_time[bn]["num instructions"])
    filtered_complexity_vs_time : dict[str,dict[str, dict[str, float]]] = {}
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
            return {"filtered_bins_w_time": filtered_bins_w_time, "filtered_complexity_vs_time": filtered_complexity_vs_time, "functions with angr errors": functions_w_angr_errors,"oids with angr errors": oids_w_angr_errors, "functions without ret instruction": functions_w_no_ret,"dataframe":dataframe, "functions with no complexity": functions_w_none_complexity, "total functions": total_functions, "functions analyzed":functions_analyzed, "functions which ran out of memory": functions_w_memory_issues}
        else:
            return {"filtered_bins_w_time": filtered_bins_w_time, "filtered_complexity_vs_time": filtered_complexity_vs_time, "functions with angr errors": functions_w_angr_errors,"oids with angr errors": oids_w_angr_errors, "functions without ret instruction": functions_w_no_ret, "functions with no complexity": functions_w_none_complexity, "total functions": total_functions, "functions analyzed": functions_analyzed, "functions which ran out of memory": functions_w_memory_issues}
