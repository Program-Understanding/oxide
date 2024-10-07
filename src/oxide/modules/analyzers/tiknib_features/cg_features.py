
def get_cg_features(call_mapping):
    incalls = 0
    outcalls = 0
    callees = 0
    callers = 0
    for function in call_mapping:
        if len(call_mapping[function]["calls_from"]) > 0:
            incalls += len(call_mapping[function]["calls_from"])
            callees += 1
        if len(call_mapping[function]["calls_to"]) > 0:
            outcalls += len(call_mapping[function]["calls_to"])
            callers += 1

    features = {}
    features["cg_num_callers"] = callers
    features["cg_num_callees"] = callees
    features["cg_num_incalls"] = incalls
    features["cg_num_outcalls"] = outcalls

    return features