import matplotlib.pyplot as plt
import pandas as pd
def output_data(outpath, dataframe,binkeys):
    try:
        outpath.mkdir(parents=True,exist_ok=True)
    except:
        return False
    with open(outpath / "analysis.csv","w") as f:
            dataframe.to_csv(f)
    #make a figure of jumps per bin
    jmps_by_bin = []
    movs_by_bin = []
    cmovs_by_bin = []
    xors_by_bin = []
    #imms, mems, regs per bin
    imms = []
    mems = []
    regs = []
    #complexity
    simple = []
    mod = []
    needs_ref = []
    cmplx = []
    for bn in binkeys:
        if len(dataframe.loc[dataframe["bin"] == bn].index) > 0:
            #jumps/movs/cmovs/xors per bin
            jmps_by_bin.append(dataframe.loc[dataframe["bin"] == bn, "j*"].sum()/len(dataframe.loc[dataframe["bin"] == bn].index))
            movs_by_bin.append(dataframe.loc[dataframe["bin"] == bn, "mov*"].sum()/len(dataframe.loc[dataframe["bin"] == bn].index))
            cmovs_by_bin.append(dataframe.loc[dataframe["bin"] == bn, "cmov*"].sum()/len(dataframe.loc[dataframe["bin"] == bn].index))
            xors_by_bin.append(dataframe.loc[dataframe["bin"] == bn, "*xor*"].sum()/len(dataframe.loc[dataframe["bin"] == bn].index))
            #imms, mems, regs per bin
            imms.append(dataframe.loc[dataframe["bin"] == bn, "imms"].sum()/len(dataframe.loc[dataframe["bin"] == bn].index))
            mems.append(dataframe.loc[dataframe["bin"] == bn, "mems"].sum()/len(dataframe.loc[dataframe["bin"] == bn].index))
            regs.append(dataframe.loc[dataframe["bin"] == bn, "regs"].sum()/len(dataframe.loc[dataframe["bin"] == bn].index))
            #complexity
            simple.append(100*(len(dataframe[(dataframe["bin"] == bn) & (dataframe["complexity"] == "simple")].index)/len(dataframe.loc[dataframe["bin"] == bn].index)))
            mod.append(100*(len(dataframe.loc[(dataframe["bin"] == bn) & (dataframe["complexity"]=="moderate")].index)/len(dataframe.loc[dataframe["bin"] == bn].index)))
            needs_ref.append(100*(len(dataframe.loc[(dataframe["bin"] == bn) & (dataframe["complexity"]=="needs refactor")].index)/len(dataframe.loc[dataframe["bin"] == bn].index)))
            cmplx.append(100*(len(dataframe.loc[(dataframe["bin"] == bn) & (dataframe["complexity"]=="complex")].index)/len(dataframe.loc[dataframe["bin"] == bn].index)))
        else:
            jmps_by_bin.append(0)
            movs_by_bin.append(0)
            xors_by_bin.append(0)
            cmovs_by_bin.append(0)
            imms.append(0)
            mems.append(0)
            regs.append(0)
            simple.append(0)
            mod.append(0)
            needs_ref.append(0)
            cmplx.append(0)
    df = pd.DataFrame({"j*" :jmps_by_bin,
                       "mov*":movs_by_bin,
                       "cmov*":cmovs_by_bin,
                       "*xor*":xors_by_bin},index=binkeys)
    df.plot.bar(rot=0)
    plt.xticks(rotation=45)
    plt.title("Average instructions matching j*/mov*/cmov*/*xor* per function sorted by bin")
    plt.ylabel("Average instructions per function")
    plt.xlabel("Time range")
    plt.tight_layout()
    plt.savefig(outpath / "jmps_movs_cmovs_xors_by_bin.png",dpi=1000)
    plt.clf()
    #imms, mems, regs per bin        
    df = pd.DataFrame({"imms": imms,
                       "mems": mems,
                       "regs": regs,
                       }, index = binkeys)
    df.plot.bar(rot=0)
    plt.xticks(rotation=45)
    plt.title("Average imms, mems, regs per function sorted by bin")
    plt.ylabel("Average occurrence of type per function")
    plt.xlabel("Time range")
    plt.tight_layout()
    plt.savefig(outpath / "imms_mems_regs_by_bin.png",dpi=1000)
    plt.clf()
    #path complexity by bin
    df = pd.DataFrame({"simple": simple,
                       "moderate": mod,
                       "needs refactor": needs_ref,
                       "complex": cmplx}, index = binkeys)
    df.plot.bar(rot=0)
    plt.xticks(rotation=45)
    plt.title("Percent cyclomatic complexity occurred for functions per bin")
    plt.ylabel("Percent occurrence of complexity")
    plt.xlabel("Time range")
    plt.tight_layout()
    plt.savefig(outpath / "cyclomatic_complexity_by_bin.png",dpi=1000)
    return True
