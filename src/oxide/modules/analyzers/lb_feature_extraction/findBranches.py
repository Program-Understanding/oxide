



def computeBranch(block, bbs, functionBlocks):
    triggerBranches = [block]
    dests = bbs[block]["dests"]
    for branch in dests:
        dominators = []
        if branch not in functionBlocks or branch not in bbs:
            pass
        else:
            if len(bbs[branch]["dests"]) > 0:
                triggerBranches.extend([[branch,_computeSubBranch(branch, bbs, functionBlocks, dominators)]])
            elif bbs[branch]["dests"] == []:
                triggerBranches.extend([branch])
    return triggerBranches


def _computeSubBranch(block, bbs, functionBlocks, dominators):
    triggerBranches = []
    dests = bbs[block]["dests"]
    for branch in dests:
        if branch not in functionBlocks or branch not in bbs:
            pass
        elif branch in dominators:
            triggerBranches.extend(["LOOP -> " + str(branch)])
        else:
            dominators.extend([branch])
            if len(bbs[branch]["dests"]) > 0:
                triggerBranches.extend([branch,_computeSubBranch(branch, bbs, functionBlocks, dominators)])
            elif bbs[branch]["dests"] == []:
                triggerBranches.extend([branch])
    return triggerBranches



def compareBranches(triggerBranches, commonBlocks):
    branchMaps = []
    pathA = []
    pathB = []
    index = 1
    cb = None
    while True:
        branchMap = {}
        level = 0
        branchMap = _getBranchMap(branchMap, triggerBranches[index], level)
        branchMaps.extend([branchMap])
        if index == 2:
            break
        else:
            index += 1
    branchA = branchMaps[0]
    branchB = branchMaps[1]
    for cb in commonBlocks:
        if cb in branchA and cb in branchB:
            depthA = branchA[cb]
            depthB = branchB[cb]
            pathA = _getPath(depthA, branchA)
            pathB = _getPath(depthB, branchB)
            break
    return pathA, pathB


def _getBranchMap(branchMap, blocks, level):
    if isinstance(blocks, list):
        for b in blocks:
            if isinstance(b, list):
                branchMap = _getBranchMap(branchMap, b, level + 1)
            else:
                branchMap[b] = level + 1
    else:
        branchMap[blocks] = level
    return branchMap


def _getPath(depth, branch):
    path = []
    index = 0
    while index <= depth:
        for block in branch:
            if branch[block] < depth:
                if branch[block] == index:
                    path.extend([block])
        index += 1
    return path