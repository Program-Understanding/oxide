import matplotlib.pyplot as plt
import pandas as pd
def output_data(outpath, dataframe,binkeys):
    outpath.mkdir(parents=True,exist_ok=True)
    with open(outpath / "analysis.csv","w") as f:
            dataframe.to_csv(f)
    #make a figure of jumps per bin
    jmps_by_bin = []
    movs_by_bin = []
    for bn in binkeys:
        jmps_by_bin.append(dataframe.loc[dataframe["bin"] == bn, "j*"].sum())
        movs_by_bin.append(dataframe.loc[dataframe["bin"] == bn, "mov*"].sum())
    df = pd.DataFrame({"j*" :jmps_by_bin,
                       "mov*":movs_by_bin},index=binkeys)
    df.plot.bar(rot=0)
    plt.xticks(rotation=45)    
    plt.title("Instructions matching j*/mov* by bin")
    plt.tight_layout()
    plt.savefig(outpath / "jmps_movs_by_bin.png",dpi=1000)
    plt.clf()
    #imms, mems, regs per bin
    imms = []
    mems = []
    regs = []
    for bn in binkeys:
        imms.append(dataframe.loc[dataframe["bin"] == bn, "imms"].sum())
        mems.append(dataframe.loc[dataframe["bin"] == bn, "mems"].sum())
        regs.append(dataframe.loc[dataframe["bin"] == bn, "regs"].sum())
    df = pd.DataFrame({"imms": imms,
                       "mems": mems,
                       "regs": regs,
                       }, index = binkeys)
    df.plot.bar(rot=0)
    plt.xticks(rotation=45)
    plt.title("Imms, mems, regs by bin")
    plt.tight_layout()
    plt.savefig(outpath / "imms_mems_regs_by_bin.png",dpi=1000)
    plt.clf()
    simple = []
    mod = []
    needs_ref = []
    cmplx = []
    for bn in binkeys:
        simple.append(dataframe.loc[(dataframe["bin"] == bn) & (dataframe["complexity"] == "simple")].size)
        mod.append(dataframe.loc[(dataframe["bin"] == bn) & (dataframe["complexity"]=="moderate")].size)
        needs_ref.append(dataframe.loc[(dataframe["bin"] == bn) & (dataframe["complexity"]=="needs refactor")].size)
        cmplx.append(dataframe.loc[(dataframe["bin"] == bn) & (dataframe["complexity"]=="complex")].size)
    df = pd.DataFrame({"simple": simple,
                       "moderate": mod,
                       "needs refactor": needs_ref,
                       "complex": cmplx}, index = binkeys)
    df.plot.bar(rot=0)
    plt.xticks(rotation=45)
    plt.title("Cyclomatic complexity by bin")
    plt.tight_layout()
    plt.savefig(outpath / "cyclomatic_complexity_by_bin.png",dpi=1000)    
