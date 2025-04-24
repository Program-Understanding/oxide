""" Plugin: linear regression model for angr function time data
should be used after running angr_function_time_analyzer on a collection
"""
NAME="angr_function_time_model"
AUTHOR="Kevan"

from oxide.core import api
import logging
logger = logging.getLogger(NAME)
import pandas as pd
import numpy as np
import torch
from typing import TypedDict, Literal
#from sklearn.metrics import mean_squared_error
import random

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
        "delete-cached": bool
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

def clear_data(data_name:str = "default") -> bool:
    return api.local_delete_data("angr_function_time_model",data_name)

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
        return False
    idp = df[[column for column in df.columns if column != "time" and column != "bin int"]]
    columns : list[str] = list(idp)
    #sort out our independent (stuff that time depends on) and dependent (time) variables
    dep: np.ndarray[tuple[int,int],np.dtype[np.float32]] = pd.DataFrame(df[["time", "bin int"]]).to_numpy()
    indep : np.ndarray[tuple[int,int],np.dtype[np.float32]]= idp.to_numpy()
    deps = torch.from_numpy(dep).float()
    indeps = torch.from_numpy(indep).float()

    #weights and biases
    #indep.shape[1] is # of columns
    model = torch.nn.Linear(indep.shape[1],dep.shape[1])
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
    # loss_list = []
    # for i in range(epochs):
    #     losss : float = 0.0
    #     #train w/ batches
    #     mse_list = []
    #     for xb, yb in training_loader:
    #         print(xb)
    #         model.train(True)
    #         #calculate prediction and loss
    #         prediction = model(xb)
    #         loss = torch.nn.functional.mse_loss(prediction, yb)
    #         losss = loss.item()
    #         mse_list.append(mean_squared_error(yb.detach().numpy(),prediction.detach().numpy()))
    #         #backwards propagation
    #         loss.backward()
    #         #update gradients
    #         opt.step()
    #         opt.zero_grad()
    #     if i % 10 == 0:
    #         print(f"Epoch {i}/{epochs}, Loss: {losss}, MSE: {sum(mse_list)/len(mse_list)}")
    # model.train(False)
    # Training loop
    criterion = torch.nn.MSELoss()
    for epoch in range(epochs):
        model.train()  # Set the model to training mode
        total_loss = 0.0

        for xb, yb in training_loader:
            opt.zero_grad()  # Zero the gradients
            predictions = model(xb)  # Forward pass
            loss = criterion(predictions.squeeze(), yb.float())  # Calculate loss
            loss.backward()  # Backward pass
            opt.step()  # Update weights
            total_loss += loss.item()  # Accumulate loss

            # Print loss every 100 epochs
        if epoch % 100 == 0:
            print(f"Epoch {epoch}/{epochs}, Loss: {total_loss / len(training_loader)}")
    api.local_store("angr_function_time_model","model",model)
    api.local_store("angr_function_time_model","testing_data",test_samples)
    api.local_store("angr_function_time_model","training_data",train_samples)
    api.local_store("angr_function_time_model", "dataframe_columns", columns)
    return True

def test(args : list[str], opts : dict[Literal["tests"],bool]):
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
    with torch.no_grad():
        if "tests" in opts:
            results = []
            for _ in range(opts["tests"]):
                givens = dict()
                rand_index = random.randint(0,len(test_samples)-1)
                test, truth = test_samples[rand_index]
                prediction : torch.Tensor = model(test)
                for i in range(len(columns)):
                    givens[columns[i]] = test.tolist()[i]
                results.append({"prediction": {"seconds": prediction.tolist()[0], "log. bin": prediction.tolist()[1]}, "reality": {"seconds": truth.tolist()[0], "log. bin": truth.tolist()[1]}, "givens": givens})
        else:
            rand_index = random.randint(0,len(test_samples)-1)
            test, truth = test_samples[rand_index]
            prediction : torch.Tensor = model(test)
            for i in range(len(columns)):
                givens[columns[i]] = test.tolist()[i]
            results = {"prediction": {"seconds": prediction.tolist()[0], "log. bin": prediction.tolist()[1]}, "reality": {"seconds": truth.tolist()[0], "log. bin": truth.tolist()[1]}, "givens": givens}
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
    with torch.no_grad():
        rand_index = random.randint(0,len(evaluating_loader)-1)
        test, truth = evaluating_loader[rand_index]
        for i in range(len(columns)):
            givens[columns[i]] = test.tolist()[i]
        results = {"prediction": {"seconds": prediction.tolist()[0], "log. bin": prediction.tolist()[1]}, "reality": {"seconds": truth.tolist()[0], "log. bin": truth.tolist()[1]}, "givens": givens}
    return results if "results" in locals() else False

def identify_outliers(args: list[str], opts: Outlier_opts):
    if "timeout" in opts:
        timeout = opts["timeout"]
    else:
        timeout = 600
    if "bins" in opts:
        bins = opts["bins"]
    else:
        bins = 6
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
        filtered_df = df[(df['time'] < 0.5) & (df.drop(columns='time').gt(10).any(axis=1))]
        with open("/home/kevan/outlier_dataframe.csv", "w") as f:
            f.write(filtered_df.to_csv())
        return {"outliers": len(filtered_df), "non-outliers": len(df)-len(filtered_df)}
    return True

#plugin's exports to the shell (functions the shell can use)
exports = [train,test,evaluate,identify_outliers]
