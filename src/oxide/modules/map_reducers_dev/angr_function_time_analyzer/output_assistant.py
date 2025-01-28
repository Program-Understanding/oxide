import matplotlib.pyplot as plt
import pandas as pd
import seaborn as sns
from sklearn.decomposition import PCA
import statsmodels.api as sm
from sklearn.ensemble import RandomForestRegressor
from sklearn.model_selection import train_test_split
from sklearn.metrics import mean_squared_error, r2_score
from sklearn.tree import plot_tree
from scipy.stats import spearmanr, pearsonr
#import numpy as np

def spearmanr_pval(x,y):
    # print(spearmanr(x,y))
    # print(spearmanr(x,y)[1])
    # print(spearmanr(x,y).pvalue)
    return spearmanr(x,y)[1]

def pearsonr_pval(x,y):
    return pearsonr(x,y)[1]

def output_data(outpath, dataframe : pd.DataFrame,binkeys):
    try:
        outpath.mkdir(parents=True,exist_ok=True)
    except:
        return False
    with open(outpath / "dataframe.csv","w") as f:
            dataframe.to_csv(f)
    #make a figure of jumps per bin
    jmps_by_bin = []
    movs_by_bin = []
    cmovs_by_bin = []
    xors_by_bin = []
    #track instructions and functions per bin
    instructions = []
    functions = []
    #imms, mems, regs per bin
    imms = []
    mems = []
    regs = []
    #complexity
    simple = []
    mod = []
    needs_ref = []
    cmplx = []
    #O
    unsorted_different_O = list(dataframe["Big O"].unique())
    different_O = []
    has_timeout = False
    has_error = False
    has_exponent = False
    for O in unsorted_different_O:
        if "Timeout" in O:
            has_timeout=True
            continue
        if "Error" in O:
            has_error=True
            continue
        if "**" in O:
            has_exponent=True
            continue
        different_O.append(O)
    if has_exponent:
        different_O.append("O(n**x)")
    if has_timeout:
        different_O.append("Timeout")
    if has_error:
        different_O.append("Error")
    big_o = {}
    for O in different_O:
        big_o[O] = []
    for bn in binkeys:
        if len(dataframe.loc[dataframe["bin"] == bn].index) > 0:
            #jumps/movs/cmovs/xors per bin
            jmps_by_bin.append(dataframe.loc[dataframe["bin"] == bn, "j*"].sum()/len(dataframe.loc[dataframe["bin"] == bn].index))
            movs_by_bin.append(dataframe.loc[dataframe["bin"] == bn, "mov*"].sum()/len(dataframe.loc[dataframe["bin"] == bn].index))
            cmovs_by_bin.append(dataframe.loc[dataframe["bin"] == bn, "cmov*"].sum()/len(dataframe.loc[dataframe["bin"] == bn].index))
            xors_by_bin.append(dataframe.loc[dataframe["bin"] == bn, "*xor*"].sum()/len(dataframe.loc[dataframe["bin"] == bn].index))
            #instructions and functions
            instructions.append(dataframe.loc[dataframe["bin"] == bn, "instructions"].sum()/len(dataframe.loc[dataframe["bin"] == bn].index))
            functions.append(len(dataframe.loc[dataframe["bin"] == bn].index))
            #imms, mems, regs per bin
            imms.append(dataframe.loc[dataframe["bin"] == bn, "imms"].sum()/len(dataframe.loc[dataframe["bin"] == bn].index))
            mems.append(dataframe.loc[dataframe["bin"] == bn, "mems"].sum()/len(dataframe.loc[dataframe["bin"] == bn].index))
            regs.append(dataframe.loc[dataframe["bin"] == bn, "regs"].sum()/len(dataframe.loc[dataframe["bin"] == bn].index))
            #complexity
            # simple.append(100*(len(dataframe[(dataframe["bin"] == bn) & (dataframe["cyclomatic complexity level"] == "simple")].index)/len(dataframe.loc[dataframe["bin"] == bn].index)))
            # mod.append(100*(len(dataframe.loc[(dataframe["bin"] == bn) & (dataframe["cyclomatic complexity level"]=="moderate")].index)/len(dataframe.loc[dataframe["bin"] == bn].index)))
            # needs_ref.append(100*(len(dataframe.loc[(dataframe["bin"] == bn) & (dataframe["cyclomatic complexity level"]=="needs refactor")].index)/len(dataframe.loc[dataframe["bin"] == bn].index)))
            # cmplx.append(100*(len(dataframe.loc[(dataframe["bin"] == bn) & (dataframe["cyclomatic complexity level"]=="complex")].index)/len(dataframe.loc[dataframe["bin"] == bn].index)))
            simple.append(len(dataframe[(dataframe["bin"] == bn) & (dataframe["cyclomatic complexity level"] == "simple")].index))
            mod.append(len(dataframe.loc[(dataframe["bin"] == bn) & (dataframe["cyclomatic complexity level"]=="moderate")].index))
            needs_ref.append(len(dataframe.loc[(dataframe["bin"] == bn) & (dataframe["cyclomatic complexity level"]=="needs refactor")].index))
            cmplx.append(len(dataframe.loc[(dataframe["bin"] == bn) & (dataframe["cyclomatic complexity level"]=="moderate")].index))
            for O in different_O:
                big_o[O].append(len(dataframe.loc[(dataframe["bin"] == bn) & (dataframe["Big O"]==O)]))
        else:
            jmps_by_bin.append(0)
            movs_by_bin.append(0)
            xors_by_bin.append(0)
            cmovs_by_bin.append(0)
            instructions.append(0)
            functions.append(0)
            imms.append(0)
            mems.append(0)
            regs.append(0)
            simple.append(0)
            mod.append(0)
            needs_ref.append(0)
            cmplx.append(0)
            for O in different_O:
                big_o[O].append(0)
    #matched j*/mov*/cmov*/*xor*
    df = pd.DataFrame({"j*" :jmps_by_bin,
                       "mov*":movs_by_bin,
                       "cmov*":cmovs_by_bin,
                       "*xor*":xors_by_bin},index=binkeys)
    df.plot.bar(rot=0)
    plt.xticks(rotation=45)
    #plt.title("Average instructions matching j*/mov*/cmov*/*xor* per function sorted by bin")
    plt.ylabel("Average instructions per function")
    plt.xlabel("Time range")
    plt.tight_layout()
    plt.savefig(outpath / "jmps_movs_cmovs_xors_by_bin.png",dpi=1000)
    plt.clf()
    #instructions and functions
    df = pd.DataFrame({"functions": functions},index=binkeys)
    df.plot.bar(rot=0)
    plt.xticks(rotation=45)
    #plt.title("Average instructions per function and total functions per bin")
    plt.ylabel("Total functions per bin")
    plt.xlabel("Time range")
    plt.yscale('log')
    plt.tight_layout()
    plt.savefig(outpath / "instructions_functions_by_bin.png",dpi=1000)
    plt.clf()
    #imms, mems, regs per bin        
    df = pd.DataFrame({"imms": imms,
                       "mems": mems,
                       "regs": regs,
                       }, index = binkeys)
    df.plot.bar(rot=0)
    plt.xticks(rotation=45)
    #plt.title("Average imms, mems, regs per function sorted by bin")
    plt.ylabel("Average occurrence of type per function")
    plt.xlabel("Time range")
    plt.tight_layout()
    plt.savefig(outpath / "imms_mems_regs_by_bin.png",dpi=1000)
    plt.clf()
    #path complexity by bin
    df = pd.DataFrame({"simple": simple,
                       "moderate": mod,
                       "complex": cmplx,
                       "needs refactor": needs_ref}, index = binkeys)
    df.plot.bar(rot=0)
    plt.xticks(rotation=45)
    #plt.title("Cyclomatic complexity of functions per bin")
    plt.ylabel("Occurrence of complexity")
    plt.xlabel("Time range")
    plt.yscale('log')
    plt.tight_layout()
    plt.savefig(outpath / "cyclomatic_complexity_by_bin.png",dpi=1000)
    plt.clf()
    #apc plot
    if len(different_O):
        df = pd.DataFrame(big_o,index = binkeys)
        print(f"apc dataframe:\n{df}")
        df.plot.bar(rot=0)
        plt.xticks(rotation=45)
        #plt.title("Big O of functions per bin")
        plt.ylabel("Occurrence of Complexity")
        plt.xlabel("Time range")
        plt.yscale('log')
        plt.tight_layout()
        plt.savefig(outpath / "path_complexity_by_bin.png",dpi=1000)
        plt.clf()
    #pi plots
    pi_df = df#.transpose()
    if len(different_O):
        #for bn in binkeys+["low memory"]:
        for O in different_O:
            ax = pi_df.plot(kind="pie",y=O,ylabel="",labeldistance=None)
            #plt.title(f"{O} across bins")
            #plt.legend('',frameon=False)
            plt.tight_layout()
            if "1" in O:
                plt.savefig(outpath / "path_complexity_pie_plot_constant.png",dpi=1000)
            elif "**" in O:
                plt.savefig(outpath / "path_complexity_pie_plot_exponential.png",dpi=1000)
            elif "n" in O:
                plt.savefig(outpath / "path_complexity_pie_plot_linear.png",dpi=1000)
            else:
                plt.savefig(outpath / f"path_complexity_pie_plot_{O}.png",dpi=1000)
            plt.clf()
        ax_arr = pi_df.plot(kind="pie",subplots=True,labeldistance=None,layout=(2,3))
        handles, labels = ax_arr[0][0].get_legend_handles_labels()
        for axes in ax_arr:
            for ax in axes:
                legend = ax.get_legend()
                if legend is not None:
                    legend.remove()
        fig = plt.gcf()
        fig.legend(handles, labels,loc="lower right",title="angr bin")#,bbox_to_anchor=(0,0,1,1),bbox_transform = plt.gcf().transFigure)
        #plt.legend('',frameon=False)
        # fig, axs = plt.subplots(3,2,figsize=(12,10))
        # axs = axs.flatten()
        # for i, (category, value) in enumerate(pi_df.values):
        #     ax = axs[i]
        #     ax.pie([category], [value], 'o', label=category)
        #     ax.set_title(category)
        #     ax.set_xlabel(f'{category}')
        #     ax.set_ylabel(f'{value}')
        # fig.legend(loc="upper right", bbox_to_anchor=(1.2,1))
        # for ax in axs[len(pi_df):]:
        #     ax.remove()
        plt.subplots_adjust(wspace=0.2,hspace=0.2)
        plt.tight_layout()
        #fig.suptitle("angr Bin per Metrinome Asymptotic Path Complexity Level")
        plt.savefig(outpath / "path_complexity_pie_plots.png",dpi=1000)
        plt.clf()
    return True

def analyze_dataframe(outpath,dataframe : pd.DataFrame,opcodes):
    #this function is to be called after output_data() so no need to verify
    #that the outpath is valid and stuff or this fucntion wouldn't be called
    # print out stats to the screen that don't necessarily need to be returned
    num_funs_exponential = dataframe[(dataframe["Big O"] == "O(n**x)")].count()
    num_funs_linear = dataframe[(dataframe["Big O"] == "O(n)")].count()
    num_funs_constant = dataframe[(dataframe["Big O"] == "O(1)")].count()
    print(f"number of funs with exponential apc: {num_funs_exponential}")
    print(f"number of funs with linear apc: {num_funs_linear}")
    print(f"number of funs with constant apc: {num_funs_constant}")
    #need to transform the dataframe to be able to be analyzed
    #it can't have strings
    columns_to_drop = ['bin', 'cyclomatic complexity level', 'Big O'] + opcodes
    #get rid of low memory results so they don't ill affect the time
    #get rid of columns which don't have numeric values
    df = dataframe[(dataframe["bin"] != "low memory")].drop(columns=columns_to_drop).dropna()
    df.rename(columns={"cyclomatic complexity": "CC","Big O degree": "APC","instructions":"length"},inplace=True)
    df["APC"] = df["APC"].astype(int)
    #correlation matrix
    corr_mat = df.corr(min_periods=0,numeric_only=True,method="pearson")
    with open(outpath / "pearson_corr_matrix.csv","w") as f:
        corr_mat.to_csv(f)
    sns.heatmap(corr_mat,annot = True,fmt=".2f")
    plt.xticks(rotation=90)
    plt.tight_layout()
    plt.savefig(outpath / "pearson_correlation_matrix_heatmap.png",dpi=1000)
    plt.clf()
    corr_mat = df.corr(min_periods=0,numeric_only=True,method="spearman")
    with open(outpath / "spearman_corr_matrix.csv","w") as f:
        corr_mat.to_csv(f)
    sns.heatmap(corr_mat,annot = True,fmt=".2f")
    plt.tight_layout()
    plt.savefig(outpath / "spearman_correlation_matrix_heatmap.png",dpi=1000)
    plt.clf()
    corr_mat = df.corr(min_periods=0,numeric_only=True,method=spearmanr_pval)
    with open(outpath / "spearman_p-val_corr_matrix.csv","w") as f:
        corr_mat.to_csv(f)
    sns.heatmap(corr_mat,annot = True,fmt=".2f")
    plt.tight_layout()
    plt.savefig(outpath / "spearman_p-val_correlation_matrix_heatmap.png",dpi=1000)
    plt.clf()
    corr_mat = df.corr(min_periods=0,numeric_only=True,method=pearsonr_pval)
    with open(outpath / "pearson_p-val_corr_matrix.csv","w") as f:
        corr_mat.to_csv(f)
    sns.heatmap(corr_mat,annot = True,fmt=".2f")
    plt.tight_layout()
    plt.savefig(outpath / "pearson_p-val_correlation_matrix_heatmap.png",dpi=1000)
    plt.clf()
    #pca
    pca = PCA(n_components=df.shape[1])
    pca.fit(df)
    components_dataframe = pd.DataFrame(pca.components_,columns=[f"PC{pc}" for pc in range(len(df.columns))],index=df.columns)
    with open(outpath / "pca_components.csv","w") as f:
        components_dataframe.to_csv(f)
    #multiple regression
    dep=pd.DataFrame(df["time"])
    indep=df[[column for column in df.columns if column != "time"]]
    model = sm.OLS(dep,indep)
    res = model.fit()
    print(res.summary())
    with open(outpath / "linear_regression.csv","w") as f:
        f.write(res.summary().as_text())
    #random forest
    # dep = np.array(df["time"].values)
    # indep = np.array(indep.values)
    print(dep)
    print(indep)
    feats_training, feats_testing, target_training, target_testing = train_test_split(indep,dep,test_size=0.3,random_state=100)
    forest = RandomForestRegressor(n_estimators=100, random_state=100,max_depth=3)
    forest.fit(feats_training, target_training)
    forest_predictions = forest.predict(feats_testing)
    mse = mean_squared_error(target_testing,forest_predictions)
    r2 = r2_score(target_testing, forest_predictions)
    print(f"mse: {mse}")
    print(f"r2: {r2}")
    plot_tree(forest.estimators_[0], feature_names=indep.columns, class_names=df["time"].unique(), filled=True, rounded=True)
    plt.tight_layout()
    plt.savefig(outpath / "random_forest_predictor_tree.png",dpi=1000)
    plt.clf()
