""" Plugin: 
"""
# Data processing
import pandas as pd
import numpy as np
from collections import Counter
# Visualization
import matplotlib.pyplot as plt
# Model and performance
from sklearn.svm import OneClassSVM
from sklearn.model_selection import train_test_split
from sklearn.metrics import classification_report
from joblib import dump, load
import itertools
import sys

import os
import json
from oxide.core import api
import tabulate
from pathlib import Path

# Work in progress - Nathan
def anomolies(args, opts):
    """

    """

    
    oid, invalid = api.valid_oids(args)
    output = api.retrieve("lb_feature_extraction", oid)
    results = {}
    df = pd.DataFrame(columns = ['ID', 'C', 'S', 'M1', 'S1', 'J'])

    for file in output:
        for function in output[file]:
            for trigger in output[file][function]:
                id = str(file) + ": " + str(trigger)
                results[id] =  output[file][function][trigger]

    for r in results:
        new_row = {'ID' : r, 
                   'C' : results[r]["Features"]['C'], 
                   'S' : results[r]["Features"]['S'],
                   'M1' : results[r]["Features"]['M1'],
                   'S1' : results[r]["Features"]['S1'],
                   'J' : results[r]["Features"]['J']}
        df.loc[len(df.index)] = new_row
        
    filepath = Path("/home/nathan/.local/share/oxide/datasets/features/out.csv")

    filepath.parent.mkdir(parents=True, exist_ok=True)

    # df.to_csv(filepath)
    print(df.to_markdown())

    # # Convert the data from numpy array to a pandas dataframe
    # df = pd.DataFrame({"Feature1": output[:0], "Feature2": output[:1]})

    # # Train test split
    # X_train, X_test, y_train, y_test = train_test_split(output, y, test_size=0.2, random_state=42)


    # # Train teh one class svm model
    # one_class_svm = OneClassSVM(nu=0.01, kernel = 'rbf', gamma="auto").fit(X_train)

    # # Predict the anomalies
    # prediction = one_class_svm.predict(X_test)

    # # Change the anomalies' value to make it consistant with the true values
    # prediction = [1 if i == -1 else 0 for i in prediction]

    # for file in output:
    #     for trigger in file:
    #         results[trigger] =  file[trigger]
    # return results


def train(args, opts):
    """

    """
    oid, invalid = api.valid_oids(args)
    output = api.retrieve("lb_feature_extraction", oid, oid)
    features = {}
    results = {}

    NAME = "test_model"
    
    # Model Path    
    MODEL_PATH  = "/home/nathan/.local/share/oxide/datasets/MODELS/"

    for file in output:
        for function in output[file]:
            for trigger in output[file][function]:
                id = str(file) + ": " + str(trigger)
                features[id] =  output[file][function][trigger]

    X = []

    for f in features:
        new_row = [features[f]['C'], 
                    features[f]['S'],
                    features[f]['M1'],
                    features[f]['S1'],
                    features[f]['J']]
        X.append(new_row)

    model = OneClassSVM(kernel='rbf',
                        gamma=0.001,
                        cache_size=100,
                        tol=0.0001,         # eps = tol  
                        nu=0.001,
                        shrinking = 1
                        ).fit(X)

    # Dump the model
    dump(model, MODEL_PATH + 'OCSVM_{}.joblib'.format(NAME))

    # Print statistics about training
    Y = model.predict(X)

    i = 0
    for f in features:
        results[f] = str(Y[i])
        i+= 1
    numOutliers = np.count_nonzero(Y == -1)

    print("TRIGGERS   : {}".format(len(Y)))
    print("OUTLIERS   : {} ({:.0%}) \n".format(numOutliers,numOutliers/len(Y)))

    return results


exports = [anomolies, train]
