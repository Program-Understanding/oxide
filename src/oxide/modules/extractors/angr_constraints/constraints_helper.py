def count_classes(s, counts):
    #s is the constraint from the output of claripy/z3
    if type(s) is not str:
        s = str(s)
    #iterate finally through each result returned
    if "Bool" in s:
        if "Bool" not in counts:
            counts["Bool"] = 0
        counts["Bool"] += s.count("Bool")
    if "BitVec" in s:
        if "BitVec" not in counts:
            counts["BitVec"] = 0
        counts["BitVec"] += s.count("BitVec")
    if "BVV" in s:
        if "BVV" not in counts:
            counts["BVV"] = 0
        counts["BVV"] += s.count("BVV")
    if "BV" in s:
        if "BV" not in counts:
            counts["BV"] = 0
        counts["BV"] += s.count("BV")
    if "String" in s:
        if "String" not in counts:
            counts["String"] = 0
        counts["String"] += s.count("String")
    if "Bits" in s:
        if "Bits" not in counts:
            counts["Bits"] = 0
        counts["Bits"] += s.count("Bits")
    if "BVS" in s:
        if "BVS" not in counts:
            counts["BVS"] = 0
        counts["BVS"] += s.count("BVS")
    if "Int" in s:
        if "Int" not in counts:
            counts["Int"] = 0
        counts["Int"] += s.count("Int")
    if "FP" in s:
        if "FP" not in counts:
            counts["FP"] = 0
        counts["FP"] += s.count("FP")
    if "Array" in s:
        if "Array" not in counts:
            counts["Array"] = 0
        counts["Array"] += s.count("Array")
    if "Datatype" in s:
        if "Datatype" not in counts:
            counts["Datatype"] = 0
        counts["Datatype"] += s.count("Datatype")
    if "FP" in s:
        if "FP" not in counts:
            counts["FP"] = 0
        counts["FP"] += s.count("FP")
    if "Real" in s:
        if "Real" not in counts:
            counts["Real"] = 0
        counts["Real"] += s.count("Real")
    if "Rexexp" in s:
        if "Regexp" not in counts:
            counts["Regexp"] = 0
        counts["Regexp"] += s.count("Regexp")
    if "Set" in s:
        if "Set" not in counts:
            counts["Set"] = 0
        counts["Set"] += s.count("Set")
