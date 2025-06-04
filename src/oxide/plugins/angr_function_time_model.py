""" Plugin: linear regression model for angr function time data
should be used after running angr_function_time_analyzer on a collection
"""
NAME="angr_function_time_model"
AUTHOR="Kevan"

import xgboost
from oxide.core import api
import logging
logger = logging.getLogger(NAME)
import pandas as pd
import numpy as np
import torch
from typing import TypedDict, Literal
#from sklearn.metrics import mean_squared_error
import random
from sklearn.metrics import accuracy_score, f1_score,mean_absolute_error, mean_squared_error
from sklearn.model_selection import train_test_split
from sklearn.decomposition import PCA
from sklearn.preprocessing import StandardScaler
from sklearn.cluster import DBSCAN
import matplotlib.pyplot as plt
import matplotlib.colors as mcolors
import matplotlib.cm as cm
import seaborn as sns
from pathlib import Path
import networkx as nx
from lifelines.utils import concordance_index
Opts = TypedDict(
    "Opts",
    {
        "timeout": int,
        "bins": int,
        "data-path": str,
        "allow-missing-ret": bool,
        "allow-low-memory": bool,
        "epochs":int,
        "data-name": str,
        "delete-cached": bool,
        "all": bool,
        "by-function-name": bool,
    }
)

class GhidraDisasmFunctions(TypedDict):
    blocks : list[int]
    name: str
    vaddr: str
    params: list[tuple[int,str]]
    retType: str
    signature: str
    returning: str

AngrFunctionTime = TypedDict(
    "AngrFunctionTime",
    {
        "angr seconds": str,
        "summary": dict[str,int|float|dict[str,int|str]],
        "instructions": dict[int,str],
        "number of states": int,
        "stopped early for": str | None,
    }
)

Outlier_opts = TypedDict(
    "Outlier_opts",
    {
        "timeout": int,
        "bins": int,
        "data-path": str,
        "allow-missing-ret": bool,
        "allow-low-memory": bool,
        "epochs":int,
        "no-prompts": bool,
        "data-name": str,
        "delete-cached": bool
    }
)

class GhidraDisasmFunctions(TypedDict):
    blocks : list[int]
    name: str
    vaddr: str
    params: list[tuple[int,str]]
    retType: str
    signature: str
    returning: str

def clear_data(data_name:str = "default") -> bool:
    return api.local_delete_data("angr_function_time_model",data_name)

def get_data(oid_list: list[str], timeout: int=300, bins: int=3, data_name:str="default",data_path:str="") -> pd.DataFrame | Literal[False]:
    if data_path == "":
        data_path = str(Path.home() / "output")
    opts = {"timeout": timeout, "data-path": data_path, "bins": bins}
    res : pd.DataFrame | None = api.local_retrieve("angr_function_time_model",data_name)
    if res is None:
        df : pd.DataFrame | None = api.get_field("angr_function_time_analyzer", oid_list, "dataframe", opts)
        if df is None:
            logger.error("Couldn't get dataframe!")
            if not oid_list:
                logger.error("Missing list of OIDs!")
            return False
        else:
            api.local_store("angr_function_time_model",data_name,df)
            return df
    else:
        return res

def train_xgboost(args : list[str], opts : Opts):
    """
    Train an XGBsurvival model to predict time taken to run angr.
    Usage: train [--timeout=<int>] [--bins=<number of bins>] [--epochs=<int>] &<collection>
    """
    if "timeout" in opts:
        timeout = opts["timeout"]
    else:
        timeout = 300
    if "bins" in opts:
        bins = opts["bins"]
    else:
        bins = 3
    if "data-name" in opts:
        data_name = opts["data-name"]
    else:
        data_name = "default"
    if "delete-cached" in opts:
        delete_cached = opts["delete-cached"]
    else:
        delete_cached = False
    if delete_cached:
        res = clear_data(data_name)
        if res:
            logger.info("Successfully cleared data!")
        else:
            logger.info("Didn't clear data!")
    df = get_data(args, timeout, bins,data_name)
    if df is False:
        logger.error("Couldn't get dataframe when requested")
        return False

    idp = df[[column for column in df.columns if column != "time" and column != "bin int" and column != "chat gpt generated function's estimated seconds"]]
    columns : list[str] = list(idp)
    # #sort out our independent (stuff that time depends on) and dependent (time) variables
    # dep: np.ndarray[tuple[int], np.dtype[np.int64]] = df["bin int"].to_numpy()
    # indep : np.ndarray[tuple[int,int],np.dtype[np.float32]]= idp.to_numpy()

    #split training and testing data
    # Create the event indicator: 1 if time > 1.5, else 0
    event = (df["time"] > 1.5).astype(int)
    time = df["time"]

    #split train and test
    X_train, X_test, time_train, time_test, event_train, event_test = train_test_split(idp,time, event,test_size=0.2,random_state=42)

    #make into proper format for xgboost
    train = xgboost.DMatrix(X_train, label=time_train, weight=event_train)
    test = xgboost.DMatrix(X_test, label=time_test, weight=event_test)
    #xgboost model
    params = {"objective" : "survival:cox", "eval_metric": "cox-nloglik", "learning_rate": 0.1, "max_depth":5}
    model = xgboost.train(params,train,num_boost_round=100,evals=[(test,"eval")])

    api.local_store("angr_function_time_model","model",model)
    data = (X_train, X_test, time_train, time_test, event_train, event_test)
    api.local_store("angr_function_time_model","data",data)
    return True

def train_dbscan_cluster(args : list[str], opts:Opts):
    """
    Train a dbscan clustering model to cluster our dataset
    """
    if "timeout" in opts:
        timeout = opts["timeout"]
    else:
        timeout = 300
    if "bins" in opts:
        bins = opts["bins"]
    else:
        bins = 3
    if "data-name" in opts:
        data_name = opts["data-name"]
    else:
        data_name = "default"
    if "delete-cached" in opts:
        delete_cached = opts["delete-cached"]
    else:
        delete_cached = False
    if "data-path" in opts:
        outpath = Path(opts["data-path"])
    else:
        logger.error("Need to provide a data path to output to! --data-path='/output/path'")
        return False
    if delete_cached:
        res = clear_data(data_name)
        if res:
            logger.info("Successfully cleared data!")
        else:
            logger.info("Didn't clear data!")
    df = get_data(args, timeout, bins,data_name,outpath)
    if df is False:
        logger.error("Couldn't get dataframe when requested")
        return False
    time = df["time"]
    X = df[[col for col in df.columns if col != "time" and "chat gpt" not in col]]

    # # Normalize the features before clustering
    # scaler = StandardScaler()
    # X_scaled = scaler.fit_transform(X)

    # Run DBSCAN
    dbscan = DBSCAN(eps=0.5, min_samples=5)  # You can tune eps and min_samples
    labels = dbscan.fit_predict(X)

    # 4. variances
    pca = PCA(n_components=2)
    pca.fit(X)
    loading_scores_pc1 = pd.Series(np.abs(pca.components_[0]), index=X.columns)
    loading_scores_pc2 = pd.Series(np.abs(pca.components_[1]), index=X.columns)
    top_features_pc1 = loading_scores_pc1.sort_values(ascending=False).index[0]
    top_features_pc2 = loading_scores_pc2.sort_values(ascending=False).index[0]
    feature_x, feature_y = top_features_pc1, top_features_pc2

    #make that seaborn pairplot
    plot_features = [feature_x, feature_y, "time"]
    # Add the cluster labels back to the DataFrame
    df_log = df.copy()
    df_log[plot_features] = df_log[plot_features].apply(lambda col: np.log10(col + 1e-9))  # Avoid log(0)

    # Cluster column needs to be string for coloring
    df_log["cluster"] = labels
    df["cluster"] = labels
    sns.pairplot(df_log, hue="cluster", vars=plot_features)
    plt.tight_layout()
    plt.savefig(outpath/ "cluster_graph_seaborn.png",dpi=1200)
    plt.clf()
    #cluster graph per cluster
    feature_cols = [col for col in df.columns if col not in ["time", "cluster"] and "chat gpt" not in col]
    for feature in feature_cols:
        plt.figure(figsize=(16,12))
        sns.kdeplot(data=df, x=feature,hue="cluster",fill=True,alpha=0.5)
        plt.title(f"Distribution of {feature} by cluster")
        plt.xlabel(feature)
        plt.ylabel("Density")
        plt.tight_layout()
        plt.savefig(outpath / f"cluster_{feature}_graph.png",dpi=1200)
        plt.close("all")
    #3d plot
    fig = plt.figure(figsize=(16,12))
    ax = fig.add_subplot(111, projection="3d")
    X_log = np.log10(df[feature_x] + 1e-9)  # Add small constant to avoid log(0)
    Y_log = np.log10(df[feature_y] + 1e-9)
    Z_log = np.log10(time + 1e-9)
    scatter = ax.scatter(X_log, Y_log, Z_log,c=labels,cmap="tab10",s=20,edgecolor="k",alpha=0.8)
    ax.set_xlabel(feature_x)
    ax.set_ylabel(feature_y)
    ax.set_zlabel("Time in seconds (log scaled)")
    ax.set_title(f"Log Scaled DBSCAN clustering: {feature_x}, {feature_y}, and Time")

    cbar = fig.colorbar(scatter, ax=ax, pad=0.1)
    cbar.set_label("Cluster label")
    plt.tight_layout()
    plt.savefig(outpath / "cluster_graph.png",dpi=1200)
    plt.close("close")

def test_xgboost(args : list[str], opts : dict[Literal["tests"],bool]):
    """
    Test the model after training. Can provide a number of tests.
    
    Usage: test [--tests=<int>] &<collection> | show
    """
    res = api.local_retrieve("angr_function_time_model","model")
    if res is None: return False
    model : xgboost.XGBModel = res
    res = api.local_retrieve("angr_function_time_model","data")
    if res is None: return False
    X_train, X_test, time_train, time_test, event_train, event_test = res
    
    if "tests" in opts:
        tests = opts["tests"]
    else:
        tests = 1

    train = xgboost.DMatrix(X_train, label=time_train, weight=event_train)
    test = xgboost.DMatrix(X_test, label=time_test, weight=event_test)
    
    results = []
    scores = model.predict(test)
    results = str(scores[:tests])
    return results

def get_accuracy(args : list[str], opts : dict[Literal["tests"],bool]):
    """
    Evaluate the model's accuracy against the cached training set
    
    Usage: get_accuracy | show
    """
    res = api.local_retrieve("angr_function_time_model","model")
    if res is None: return False
    model : xgboost.XGBModel = res
    res = api.local_retrieve("angr_function_time_model","data")
    if res is None: return False
    X_train, X_test, time_train, time_test, event_train, event_test = res
    
    test = xgboost.DMatrix(X_test, label=time_test, weight=event_test)
    scores = model.predict(test)
    # concordance index: higher is better, max=1
    c_index = concordance_index(time_test, -scores, event_observed=event_test)
    return {"concordance index" : c_index}

def evaluate(args : list[str], opts : Opts):
    """
    Evaluate the angr function time analyzer model against a differnet collection that wasn't use to train the model.
    Not recommended to use against data used to train the model as this can result in training data being used in testing.

    Usage: evaluate [--timeout=<int>] [--bins=<number of bins>] &<collection>
    """
    res = api.local_retrieve("angr_function_time_model","model")
    if res is None: return False
    model : xgboost.XGBModel = res
    opts["timeout"] = 5
    results = {}
    for oid in args:
        df : pd.DataFrame | None = api.get_field("angr_function_time_analyzer", oid, "dataframe", opts)
        if df is None:
            logger.error(f"Couldn't get dataframe for oid {oid}")
            return False
        g_d : dict[int,GhidraDisasmFunctions] | None = api.get_field("ghidra_disasm",oid,"functions")
        if not g_d:
            logger.error(f"Error with ghidra disassembly for {oid}!")
            continue
        #reorder the dataframe to match what the model expects
        expected_features = model.feature_names
        df = df[expected_features]
        idp = df[[column for column in df.columns if column != "time" and column != "bin int" and column != "chat gpt generated function's estimated seconds"]]
        #have model predict the function risk per function
        dmatrix = xgboost.DMatrix(idp)
        oid_scores = model.predict(dmatrix)
        if not len(oid_scores):
            logger.warning(f"Didn't get any risk scores for oid {oid}")
            continue
        scores_with_function_names = pd.Series(oid_scores, index=df.index.str.slice(start=len(oid)), name="predicted_risk")
        #now we can evaluate per oid how well our prediction did against the reality
        results[oid] = {}
        good_ones = 0
        total = 0
        for row_name, risk_score in scores_with_function_names.items():
            time_taken = float(df.loc[oid+row_name,"time"])
            results[oid][row_name] = {"seconds taken": time_taken, "predicted risk score": risk_score}
            #not sure if using a threshold of 0.3 for a risk score is signficant or not but its something
            if (time_taken <= 1.0 and risk_score <= 0.3) or (time_taken > 1.0 and risk_score > 0.3):
                good_ones += 1
            total+=1
        results[oid]["OID stats"] = {"total predictions": total, "predictions where risk score was > 0.3 and seconds taken was > 1 or vice versa": good_ones}
    return results
    

def identify_outliers2(args: list[str], opts: Outlier_opts):
    if "timeout" in opts:
        timeout = opts["timeout"]
    else:
        timeout = 300
    if "bins" in opts:
        bins = opts["bins"]
    else:
        bins = 3
    if "data-name" in opts:
        data_name = opts["data-name"]
    else:
        data_name = "default"
    if "delete-cached" in opts:
        delete_cached = opts["delete-cached"]
    else:
        delete_cached = False
    if delete_cached:
        res = clear_data(data_name)
        if res:
            logger.info("Successfully cleared data!")
        else:
            logger.info("Didn't clear data!")
    df = get_data(args, timeout, bins,data_name)
    if df is False:
        logger.error("Couldn't get dataframe when requested")
        return False
    for index, row in df.iterrows():
        #check if the current row has a low time
        for col in df.columns:
            if row[col] > 1e10:
                print(f"index: {index}, row: {row}")

def identify_outliers(args: list[str], opts: Outlier_opts):
    if "timeout" in opts:
        timeout = opts["timeout"]
    else:
        timeout = 300
    if "bins" in opts:
        bins = opts["bins"]
    else:
        bins = 3
    if "data-name" in opts:
        data_name = opts["data-name"]
    else:
        data_name = "default"
    if "delete-cached" in opts:
        delete_cached = opts["delete-cached"]
    else:
        delete_cached = False
    if delete_cached:
        res = clear_data(data_name)
        if res:
            logger.info("Successfully cleared data!")
        else:
            logger.info("Didn't clear data!")
    df = get_data(args, timeout, bins,data_name)
    if df is False:
        logger.error("Couldn't get dataframe when requested")
        return False
    if "no-prompts" in opts and opts["no-prompts"] == False:
        for index, row in df.iterrows():
            #check if the current row has a low time
            if row["time"] <= 1.0:
                for col in df.columns:
                    #don't evaluate bin number or time
                    if col == "time" or col == "bin int": continue
                    #not concerned w/ non-numerical values
                    if type(row[col]) is str:
                        logger.info(f"type {col} is {type(row[col])}")
                        return False
                    #now we check for weird things
                    if row[col] > 10:
                        logger.info(f"row {index}, column '{col}' has value of {row[col]}")
                        if "y" in input("View entire row? [y/n]"):
                            logger.info(f"{index}: {list(row)}")
                    else:
                         logger.info(f"row {index} is good")
                if "y" not in input("Keep going? [y/n]"):
                    break
    else:
        filtered_df = df[(df['time'] < 0.5) & (df["CC"].gt(50))]
        with open(Path.home().joinpath("outlier_dataframe.csv"), "w") as f:
            f.write(filtered_df.to_csv())
        return {"outliers": len(filtered_df), "non-outliers": len(df)-len(filtered_df)}
    return True

def get_detailed_call_graph(args:list[str],opts:Opts):
    """
    Get a detailed call graph that shows predicted function time per call

    Usage: get_detailed_call_graph --by-function-name=[bool] --data-path=/where/you/want/your/data
    """
    if not opts["data-path"]:
        logger.error("Missing data path")
        return False
    res = api.local_retrieve("angr_function_time_model","model")
    if res is None:
        logger.error("No existing trained model!")
        return False
    model : xgboost.XGBModel = res
    opts["timeout"] = 0
    results = {}
    for oid in args:
        call_graph : nx.DiGraph[int] | None = api.get_field("call_graph",oid,oid,opts)
        if call_graph is None:
            logger.error(f"Couldn't get call graph for oid {oid}")
            return False
        g_d : dict[int,GhidraDisasmFunctions] | None = api.get_field("ghidra_disasm",oid,"functions")
        if not g_d:
            logger.error(f"Error with ghidra disassembly for {oid}!")
            return False
        df : pd.DataFrame | None = api.get_field("angr_function_time_analyzer", oid, "dataframe", opts)
        if df is None:
            logger.error(f"Couldn't get dataframe for oid {oid}")
            return False
        #reorder the dataframe to match what the model expects
        expected_features = model.feature_names
        df = df[expected_features]
        idp = df[[column for column in df.columns if column != "time" and column != "bin int" and column != "chat gpt generated function's estimated seconds"]]
        #have model predict the function risk per function
        dmatrix = xgboost.DMatrix(idp)
        oid_scores = model.predict(dmatrix)
        if not len(oid_scores):
            logger.warning(f"Didn't get any risk scores for oid {oid}")
            continue
        scores_with_function_names = pd.Series(oid_scores, index=df.index.str.slice(start=len(oid)), name="predicted_risk")
        #logger.info(f"scores with function names = {scores_with_function_names}")
        #need to map function names back to their offsets and add their information to the call graph
        cols = list(scores_with_function_names.index)
        f_names : list[str] = []
        labels = {}
        for fun in g_d:
            f_name = g_d[fun]["name"]
            labels[fun] = f"{fun}: {f_name}"
            if g_d[fun]["blocks"] == [] or f_name in ["_start","__stack_chk_fail","_init","_fini","_INIT_0","_FINI_0", "__libc_start_main", "malloc", "puts",
                      #functions excluded by x86 sok
                      "__x86.get_pc_thunk.bx", # glibc in i386 function
               "__libc_csu_init",
               "__libc_csu_fini",
               "deregister_tm_clones",
               "register_tm_clones",
               "__do_global_dtors_aux",
               "frame_dummy",
               "_start",
               "atexit",
               "_dl_relocate_static_pie",
               "__stat",
               "stat64",
               "fstat64",
               "lstat64",
               "fstatat64",
               "__fstat"]:
                continue
            f_names.append(f_name)
            if f_name in cols:
                risk_score = float(scores_with_function_names[f_name])
                call_graph.nodes[fun]["risk score"] = risk_score
                #logger.info(f"node found for {f_name}")
        #logger.info(f"all cols: {cols}")
        #logger.info(f"all f_names: {f_names}")
        
        #now we can display the new call graph with the updated information
        risk_scores = np.array([call_graph.nodes[n]["risk score"] for n in call_graph.nodes if "risk score" in call_graph.nodes[n]])
        #logger.info(f"Risk scores: {risk_scores}")
        norm = mcolors.Normalize(vmin=risk_scores.min(), vmax=risk_scores.max())
        cmap = cm.get_cmap("RdYlGn_r")
        #we need to give a default color to the ones that aren't a risk
        default_color = (0.8, 0.8, 0.8, 1.0)  # light gray RGBA
        node_colors = []
        for n in call_graph.nodes:
            if "risk score" in call_graph.nodes[n]:
                risk_score = call_graph.nodes[n]["risk score"]
                node_colors.append(cmap(norm(risk_score)))
            else:
                node_colors.append(default_color)
        plt.figure(figsize=(7,7))
        pos = nx.kamada_kawai_layout(call_graph)#,seed=42,iterations=3*len(g_d),k=0.7)
        nx.draw(call_graph,pos,with_labels=True,labels=labels,node_color=node_colors,edge_color="gray",node_size=800,font_weight="bold")
        sm = plt.cm.ScalarMappable(cmap=cmap,norm=norm)
        sm.set_array([])
        ax = plt.gca()
        plt.colorbar(sm,ax=ax,label="Predicted risk score")
        plt.title(f"Call graph with predicted risk score for {oid}")
        save_path = Path(opts["data-path"]) / Path(f"{oid}_call_graph.png")
        plt.savefig(save_path,dpi=1200,bbox_inches="tight")
        plt.clf()
        plt.close("all")
        logger.info(f"Call graph for {oid} saved to {save_path}")
    return True

def correlations(args:list[str],opts:Opts):
    if "timeout" in opts:
        timeout = opts["timeout"]
    else:
        timeout = 300
    if "bins" in opts:
        bins = opts["bins"]
    else:
        bins = 3
    if "data-name" in opts:
        data_name = opts["data-name"]
    else:
        data_name = "default"
    df = get_data(args, timeout, bins,data_name)
    if df is False:
        logger.error("Couldn't get dataframe when requested")
        return False
    correlations = df.corr(numeric_only=True)["time"].sort_values(ascending=False)
    print("time\n------------------------------------------------\n",correlations)
    correlations = df.corr(numeric_only=True)["bin int"].sort_values(ascending=False)
    print("\nbin int\n------------------------------------------------\n",correlations)

def average_functions_per_oid(args:list[str],opts:Opts):
    if "timeout" in opts:
        timeout = opts["timeout"]
    else:
        timeout = 300
    if "all" in opts:
        show_all = opts["all"]
    else:
        show_all = False
    results : dict[str, int | float] = {}
    valid, _ = api.valid_oids(args)
    if not valid:
        logger.error("Couldn't get valid OIDs")
        return False
    args = api.expand_oids(valid)
    total_functions = 0
    oids_without_functions = 0
    for oid in args:
        functions : dict[str,dict[str,int|float|bool|tuple[float,str]]] | None = api.retrieve("angr_function_time", oid, {"timeout": timeout})
        if not functions:
            logger.error("Failed to extract disassembly")
            return False
        if show_all:
            results[oid] = len(functions)
        total_functions += len(functions)
        if len(functions) == 0:
            oids_without_functions += 1
    results["average functions per oid"] = total_functions/len(args)
    results["total functions"] = total_functions
    results["total oids"] = len(args)
    results["oids without functions"] = oids_without_functions
    return results

def identify_contender_for_case_study(args: list[str], opts: Opts):
    if "timeout" in opts:
        timeout = opts["timeout"]
    else:
        timeout = 300
    results : dict[str, int | float] = {}
    valid, _ = api.valid_oids(args)
    if not valid:
        logger.error("Couldn't get valid OIDs")
        return False
    args = api.expand_oids(valid)
    for oid in args:
        functions : dict[str,AngrFunctionTime] | None = api.retrieve("angr_function_time", oid, {"timeout": timeout})
        if not functions:
            logger.error(f"couldn't get angr function time results for oid {oid}")
            return False
        #we need to make sure we only find one good candidate, and that nothing stopped early
        found_good_candidate = False
        move_on = False
        candidate_function = ""
        for f in functions:
            if f == "main" or "error" in functions[f]["angr seconds"] or ("stopped early for" in functions[f] and "timed out" not in functions[f]["stopped early for"]):
                move_on = True
                break
            time_taken = float(functions[f]["angr seconds"].split(" ")[0])
            if time_taken >= timeout:
                if found_good_candidate:
                    #if we've already found a good candidate and then find another, move onto the next oid
                    move_on = True
                    break
                found_good_candidate = True
                candidate_function = f
        if move_on or not found_good_candidate:
            continue
        return {"candidate oid": oid , "candidate function": candidate_function, "angr_function_time_results": functions, "candidate results": functions[candidate_function]}
    logger.info(f"Couldn't find a candidate that was the one and only function in the binary that timed out without any other functions timing out or having an error")
    logger.info("broadening the search to allow for functions that stopped early...")
    for oid in args:
        functions : dict[str,AngrFunctionTime] | None = api.retrieve("angr_function_time", oid, {"timeout": timeout})
        if not functions:
            logger.error(f"couldn't get angr function time results for oid {oid}")
            return False
        #we need to make sure we only find one good candidate, and that nothing stopped early
        found_good_candidate = False
        move_on = False
        candidate_function = ""
        for f in functions:
            if f == "main" or "error" in functions[f]["angr seconds"]:
                move_on = True
                break
            time_taken = float(functions[f]["angr seconds"].split(" ")[0])
            if time_taken >= timeout:
                if found_good_candidate:
                    #if we've already found a good candidate and then find another, move onto the next oid
                    move_on = True
                    break
                found_good_candidate = True
                candidate_function = f
        if move_on or not found_good_candidate:
            continue
        return {"candidate oid": oid , "candidate function": candidate_function, "angr_function_time_results": functions, "candidate results": functions[candidate_function]}
    logger.info(f"Still couldn't find a good candidate...")
    logger.info("broadening the search to allow for functions that stopped early AND binaries that have multiple candidates...")
    for oid in args:
        functions : dict[str,AngrFunctionTime] | None = api.retrieve("angr_function_time", oid, {"timeout": timeout})
        if not functions:
            logger.error(f"couldn't get angr function time results for oid {oid}")
            return False
        #we need to make sure we only find one good candidate, and that nothing stopped early
        move_on = False
        candidate_function = ""
        for f in functions:
            if f == "main" or "error" in functions[f]["angr seconds"]:
                move_on = True
                break
            time_taken = float(functions[f]["angr seconds"].split(" ")[0])
            if time_taken >= timeout:
                candidate_function = f
        if move_on or not candidate_function:
            continue
        return {"candidate oid": oid , "candidate function": candidate_function, "angr_function_time_results": functions, "candidate results": functions[candidate_function]}

#plugin's exports to the shell (functions the shell can use)
exports = [train_xgboost,train_dbscan_cluster, test_xgboost,evaluate,identify_outliers,identify_outliers2,get_accuracy,correlations,average_functions_per_oid,identify_contender_for_case_study,get_detailed_call_graph]
