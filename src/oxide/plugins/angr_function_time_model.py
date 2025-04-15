""" Plugin: linear regression model for angr function time data
should be used after running angr_function_time_analyzer on a collection
"""
NAME="angr_function_time_model"
AUTHOR="Kevan"

from oxide.core import api
import pandas as pd
import numpy as np
import torch
from typing import TypedDict, Literal
import random

Opts = TypedDict(
    "Opts",
    {
        "timeout": int,
        "bins": int,
        "data-path": str,
        "allow-missing-ret": bool,
        "allow-low-memory": bool,
        "epochs":int
    }
)

def get_data(oid_list: list[str], timeout: int=600, bins: int=6, data_name:str="default") -> pd.DataFrame | Literal[False]:
    opts = {"timeout": timeout, "data-path": "/home/kevan/output", "bins": 6}
    res : pd.DataFrame | None = api.local_retrieve("angr_function_time_model",data_name)
    if res is None:
        df : pd.DataFrame | None = api.get_field("angr_function_time_analyzer", oid_list, "dataframe", opts)
        if df is None:
            return False
        else:
            api.local_store("angr_function_time_model",data_name,df)
            return df
    else:
        return res

def train(args : list[str], opts : Opts):
    """
    Train a linear regression model to predict time taken to run angr.
    Usage: train [--timeout=<int>] [--bins=<number of bins>] [--epochs=<int>] &<collection>
    """
    if "timeout" in opts:
        timeout = opts["timeout"]
    else:
        timeout = 600
    if "bins" in opts:
        bins = opts["bins"]
    else:
        bins = 6
    df = get_data(args, timeout, bins)
    if df is False:
        return False
    idp = df[[column for column in df.columns if column != "time"]]
    columns : list[str] = list(idp)
    #sort out our independent (stuff that time depends on) and dependent (time) variables
    dep: np.ndarray[tuple[int,int],np.dtype[np.float32]] = pd.DataFrame(df["time"]).to_numpy()
    indep : np.ndarray[tuple[int,int],np.dtype[np.float32]]= idp.to_numpy()
    deps = torch.from_numpy(dep).float()
    indeps = torch.from_numpy(indep).float()

    #weights and biases
    #indep.shape[1] is # of columns
    model = torch.nn.Linear(indep.shape[1],1)
    #samples and testing
    training_set = torch.utils.data.TensorDataset(indeps, deps)
    num_samples = int(len(training_set)*0.8)
    train_samples, test_samples = torch.utils.data.random_split(training_set, [num_samples,len(training_set)-num_samples])
    training_loader = torch.utils.data.DataLoader(train_samples, 16,shuffle=True)
    testing_loader = torch.utils.data.DataLoader(test_samples, 16, shuffle=False)
    #training epochs
    if "epochs" in opts:
        epochs = opts["epochs"]
    else:
        epochs = 1000
    opt = torch.optim.SGD(model.parameters(), lr=1e-5)
    #epochs
    for i in range(epochs):
        losss : float = 0.0
        #train w/ batches
        for xb, yb in training_loader:
            #calculate prediction and loss
            prediction = model(xb)
            loss = torch.nn.functional.mse_loss(prediction, yb)
            losss = loss.item()
            #backwards propagation
            loss.backward()
            #update gradients
            opt.step()
            opt.zero_grad()
        if i % 10 == 0:
            print(f"Epoch {i}/{epochs}, Loss: {losss}")
    api.local_store("angr_function_time_model","model",model)
    api.local_store("angr_function_time_model","testing_data",test_samples)
    api.local_store("angr_function_time_model","training_data",train_samples)
    api.local_store("angr_function_time_model", "dataframe_columns", columns)
    return True

Test_opts = TypedDict(
    "Test_opts",
    {
        "tests": int,
    }
)

def test(args : list[str], opts : Test_opts):
    """
    Test the model after training. Can provide a number of tests.
    
    Usage: test [--tests=<int>] &<collection> | show
    """
    res = api.local_retrieve("angr_function_time_model","model")
    if res is None: return False
    model : torch.nn.Linear = res
    res = api.local_retrieve("angr_function_time_model","testing_data")
    if res is None: return False
    test_samples : torch.utils.data.DataLoader[tuple[torch.Tensor, ...]] = res
    res = api.local_retrieve("angr_function_time_model","training_data")
    if res is None: return False
    train_samples : torch.utils.data.DataLoader[tuple[torch.Tensor, ...]] = res
    res = api.local_retrieve("angr_function_time_model","dataframe_columns")
    if res is None: return False
    columns : list[str] = res
    givens : dict[str, float] = {}
    if "tests" in opts:
        results = []
        for _ in range(opts["tests"]):
            test, truth = random.choice(test_samples)
            prediction : torch.Tensor = model(test)
            for i in range(len(columns)):
                givens[columns[i]] = test.tolist()[i]
            results.append({"prediction": prediction.tolist()[0], "reality": truth.tolist()[0], "givens": givens})
    else:
        test, truth = random.choice(test_samples)
        prediction : torch.Tensor = model(test)
        for i in range(len(columns)):
            givens[columns[i]] = test.tolist()[i]
        results = {"prediction": prediction.tolist()[0], "reality": truth.tolist()[0], "givens": givens}
    return results if "results" in locals() else False

def evaluate(args : list[str], opts : Opts):
    """
    Evaluate the angr function time analyzer model against a differnet collection that wasn't use to train the model.
    Not recommended to use against data used to train the model as this can result in training data being used in testing.

    Usage: evaluate [--timeout=<int>] [--bins=<number of bins>] &<collection>
    """
    res = api.local_retrieve("angr_function_time_model","model")
    if res is None: return False
    model : torch.nn.Linear = res
    if "timeout" in opts:
        timeout = opts["timeout"]
    else:
        timeout = 600
    if "bins" in opts:
        bins = opts["bins"]
    else:
        bins = 6
    df = get_data(args, timeout, bins)
    if df is False:
        return False
    dep: np.ndarray[tuple[int,int],np.dtype[np.float32]] =pd.DataFrame(df["time"]).to_numpy()
    indep : np.ndarray[tuple[int,int],np.dtype[np.float32]]=df[[column for column in df.columns if column != "time"]].to_numpy()
    deps = torch.from_numpy(dep).float()
    indeps = torch.from_numpy(indep).float()
    evaluating_set = torch.utils.data.TensorDataset(indeps, deps)
    evaluating_loader = torch.utils.data.DataLoader(evaluating_set, 16,shuffle=False)
    res = api.local_retrieve("angr_function_time_model","dataframe_columns")
    if res is None: return False
    columns : list[str] = res
    givens : dict[str, float] = {}
    test, truth = random.choice(evaluating_loader)
    prediction : torch.Tensor = model(test)
    for i in range(len(columns)):
        givens[columns[i]] = test.tolist()[i]
    results : dict[str, float | dict[str, float]] = {"prediction": prediction.tolist()[0], "reality": truth.tolist()[0], "givens": givens}
    return results if "results" in locals() else False

#plugin's exports to the shell (functions the shell can use)
exports = [train,test,evaluate]
