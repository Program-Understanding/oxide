AUTHOR="KEVAN"
DESC="Analyze big O time complexity of a binary, useful to see if we may have path explosion"
NAME="path_complexity"

import logging
logger = logging.getLogger(NAME)

from core import api
import sympy
import numpy
from stopit import ThreadingTimeout
import subprocess, sys, os

opts_doc={}

def documentation():
    return {"description":DESC,
            "opts_doc": opts_doc,
            "private": False,
            "set": False,
            "atomic":True
            }

def calc_func_apc(adj_matrix,n):
    """given an adjacency matrix and the size of it,
    compute the asymptotic path complexity
    """
    #breaking up these variables for testing/debugging
    I = sympy.eye(n) #identity matrix
    z = sympy.symbols('z') #our symbolic variable 'z'
    z_T = z*adj_matrix
    I_z_T = sympy.Matrix(I-z_T)
    qz = sympy.expand(-1*I_z_T.det())
    logger.debug(f"denominator: {qz}")
    pz = (I[:n-1,1:]-(z*adj_matrix[:n-1,1:])).det()
    logger.debug(f"g(z) = {pz}/{qz}")
    degree=sympy.degree(qz,gen=z)
    #get base case using bfs down the paths
    end_index = n + degree
    depth = 1
    base_cases = [0]*end_index
    num_paths = {0:1}
    while depth<end_index:
        new_num_paths = {}
        for node, paths in num_paths.items():
            #for the node and paths that node has
            #check each destination node in its adjacency
            #matrix and add 1 if there's a path to the end
            for dnode in range(adj_matrix.row(node).cols): #for next_node in graph_adj[curr_node]
                if adj_matrix[node,dnode] == 1 and node!=dnode:
                    if not dnode in new_num_paths:
                        new_num_paths[dnode] = 0
                    new_num_paths[dnode] += paths
        base_cases[depth] = new_num_paths[n-1] if n-1 in new_num_paths else 0
        if depth > 0:
            base_cases[depth] += base_cases[depth-1]
        depth+=1
        num_paths = new_num_paths
    base_cases = base_cases[n:end_index]
    #get roots of polynomial using the rounded coefficients    
    rounded_coeffs = [round(-c,2) for c in qz.as_poly().all_coeffs()[::-1]]
    roots = sympy.Poly(rounded_coeffs,z).all_roots(multiple=True)
    #make an easier time of the roots by manipulating the data structure
    new_roots = {}
    for root in roots:
        if type(root) is sympy.CRootOf:
            #crootof is a sympy type that represents a complex root but doesn't actually display
            #the root because its too complex
            #https://docs.sympy.org/latest/guides/solving/find-roots-polynomial.html
            if not f"{root.eval_approx(2)}" in new_roots:
                new_roots[f"{root.eval_approx(2)}"] = {"root":root.eval_approx(2),"multiplicity":1}
            else:
                new_roots[f"{root.eval_approx(2)}"]["multiplicity"] +=1
            continue
        if not f"{root}" in new_roots:
            new_roots[f"{root}"] = {"root":root,"multiplicity":1}
        else:
            new_roots[f"{root}"]["multiplicity"] +=1
    roots = new_roots
    logger.debug(f"q(z) has {len(roots)} distinct roots:{roots}")
    #replacing complex roots
    simplified_solution = []
    solution = []
    for root in roots:
        for i in range(roots[root]['multiplicity']):
            if root == 1:
                term = z**i
                solution.append(term)
                simplified_solution.append(term)
            else:
                solution.append((z**i) * roots[root]['root']**n)
                abs_root = sympy.Abs(roots[root]['root'])
                if abs_root == 1:
                    simplified_solution.append(z**i)
                else:
                    simplified_solution.append((z**i)*abs_root**n)
    sol_matrix = []
    i = 0
    for val in range(n,n+degree):
        sol_matrix.append([])
        for factor in solution:
            sol_matrix[i].append(factor.replace(z,val))
        i+=1
    #solve the system of linear equations of Ax=b with solution matrix as A and the transposed base cases as b
    coeffs = numpy.linalg.lstsq(numpy.array(sol_matrix,dtype='complex'),numpy.array(base_cases,dtype='complex').transpose(),rcond=None)[0].transpose()
    logger.debug(f"coeffs: {coeffs}")
    bounded_solution_terms = coeffs.dot(simplified_solution)
    logger.debug(f"bound solution terms {bounded_solution_terms}")
    #ordered_terms = bounded_solution_terms.as_ordered_terms()
    try:
        logger.debug(f"big o: {bounded_solution_terms}, degree: {sympy.polys.polytools.degree(bounded_solution_terms)}")
        degree = sympy.polys.polytools.degree(bounded_solution_terms)
    except sympy.SympifyError as e:
        logger.debug(f"sympify error {e},type{type(bounded_solution_terms)}")
        logger.debug(f"error attributes {dir(e)}")
        degree = False
    except Exception as e:
        logger.info(f"other error {e}")
        logger.info(f"error attributes {dir(e)}")
        degree = False
    # if type(bounded_solution_terms) is sympy.polys.polytools.Poly or type(bounded_solution_terms) is type(sympy.core.add.Add):
    #     logger.info(f"degree: {sympy.degree(bounded_solution_terms)}")
    #     logger.info(f"bounded_solution_terms {bounded_solution_terms}")
    #     degree = sympy.degree(bounded_solution_terms)
    if type(degree) is sympy.core.numbers.NegativeInfinity:
        return False, bounded_solution_terms
    else:
        return degree, bounded_solution_terms

def process(oid, opts):
    """
    This will return the adjacency matrix and
    the estimated path complexity, and
    the results from the acfg module for the function.
    Results are returned on function by function basis.
    """
    results = {}
    from time import sleep
    fun_names = []
    fun_filenames = []
    #temp code just to keep track of the filename
    # data = api.get_field(api.source(oid), oid, "data", {})
    # f_name = api.get_field("file_meta", oid, "names").pop()
    # f_name = api.tmp_file(f_name, data)
    # logger.debug(f_name)        
    #use ghidra to get the adjacency matrix
    original_blocks = api.get_field("ghidra_disasm", oid, "original_blocks")
    if not original_blocks:
        return False
    funs = api.get_field("ghidra_disasm", oid, "functions")
    if not funs:
        return False
    for fun in funs:
        fun_name = funs[fun]["name"]
        fun_names.append(fun_names)
        if fun_name == "_start": continue
        results[fun_name] = None
        #fallback_end_node_candidates = []
        #go through every function to make function-level adjacency graph to
        #calculate the apc
        # fun_blocks = {}
        # for block in original_blocks.keys():
        #     if block in funs[fun]['blocks']:
        #         fun_blocks[block] = original_blocks[block]
        # n = len(funs[fun]['blocks'])
        #if we don't have any basic block members
        #or if we only have 1 basic block
        #we don't want to say for sure
        # if not fun_blocks:
        #     results[fun_name] = {"degree": False} #, "adjacency matrix": None, "solution terms": None}
        #     continue
        #this'll map out each of the blocks
        blocks = {}
        i = 0
        for block in funs[fun]["blocks"]:
            label = ""
            dest_blocks = original_blocks[block]["dests"][:]
            bdests = []
            if block == fun:
                label += "START "
            for b in original_blocks[block]["dests"]:
                if b in funs and b != fun and b in funs and b in dest_blocks:
                    label += f"CALLS {funs[b]['name']}"
                    dest_blocks.remove(b)
                elif b in funs and b != fun and b in dest_blocks:
                    #need to find the function name of the block being called
                    for f in funs:
                        if b in funs[f]["blocks"]:
                            label += f"CALLS {funs[f]['name']}"
                            dest_blocks.remove(b)
                            break
            #go through other blocks in the blocks dict, and
            #check if this block is in their destinations,
            #then add the index to that blocks destination
            for j in blocks:
                if j == i:
                    continue
                for dest in blocks[j]["dest_blocks"][:]:
                    if dest == block:
                        blocks[j]["dests"].append(i)
                        blocks[j]["dest_blocks"].remove(dest)
                if blocks[j]["offset"] in dest_blocks:                        
                    dest_blocks.remove(blocks[j]["offset"])
                    bdests.append(j)
            #make sure that we reference our own block if its in our dests
            for b in dest_blocks[:]:
                if b == block:
                    dest_blocks.remove(b)
                    bdests.append(i)
            # #check if this block has any previously used blocks in its destination
            # if not label and not dest_blocks and not bdests:
            #     fallback_end_node_candidates.append(i)
            blocks[i] = {"label": label,
                         "dest_blocks": dest_blocks,
                         "dests": bdests,
                         "offset": block}
            i+=1
        #comb through again just to double check we got all the dest_blocks cleared out
        for block in blocks:
            dests = blocks[block]["dest_blocks"][:]
            for dest in dests:
                for o_block in blocks:
                    if blocks[o_block]["offset"] == dest and o_block in funs:
                        blocks[block]["label"] += f"CALLS {funs[o_block]['name']}"
                        blocks[block]["dest_blocks"].remove(o_block)
                    elif blocks[o_block]["offset"] == dest:
                        for f in funs:
                            if o_block in funs[f]["blocks"]:
                                blocks[block]["label"] += f"CALLS {funs[f]['name']}"
                                blocks[block]["dest_blocks"].remove(o_block)
                                break
        #set the last block to be the destinations
        i-=1
        if i >0:
            blocks[i]["label"] = "EXIT " + blocks[i]["label"]
        #make sure we handle the case that the cfg look too small or something
        if len(blocks) < 2:
            blocks = {0: {"label": "START",
                          "dests": [1]},
                      1: {"label": "",
                          "dests": [2]},
                      2: {"label": "EXIT",
                          "dests": []}}
        simplified_blocks = {}
        for block in blocks:
            if "dest_blocks" in blocks[block] and blocks[block]["dest_blocks"] != []:
                logger.warning(f"Unfinished business with {blocks[block]}, oid {oid}")
                simplified_blocks[block] = {"label": blocks[block]["label"].strip(),
                                            "dests": blocks[block]["dests"],
                                            "dest_blocks": blocks[block]["dest_blocks"]}
                if "offset" in blocks[block]:
                    simplified_blocks[block]["offset"] = blocks[block]["offset"]
                continue
            simplified_blocks[block] = {"label": blocks[block]["label"].strip(),
                                        "dests": blocks[block]["dests"]}
            if "offset" in blocks[block]:
                simplified_blocks[block]["offset"] = blocks[block]["offset"]
        #results[fun_name] = simplified_blocks

        # WIP to redefine the end node if i need to
        # #need to go and check that we don't have an exit that's also a call
        # if "CALL" in simplified_blocks[list(simplified_blocks.keys())[-1]]["label"]:
        #     for block in fallback_end_node_candidates:
        #         block = simplified_blocks[block]["offset"]
        #         if original_blocks[block]
        #conver to file
        digraph = "digraph {\n"
        for block in simplified_blocks:            
            digraph += f"{block}"
            if simplified_blocks[block]["label"] != "":
                digraph += f' [label="{simplified_blocks[block]["label"]}"]'
            digraph+=";\n"
        for block in simplified_blocks:
            for dest in simplified_blocks[block]["dests"]:
                digraph+=f"{block} -> {dest};\n"
        digraph+="}"
        #need to create the files directory and put all the functions files in, then call apc w/ paths to all cfgs
        fun_filename = api.scratch_dir + "/"+str(oid)+"_."+fun_name+".dot"
        fun_filenames.append(fun_filename)
        with open(fun_filename,"w") as f:
            f.write(digraph)
        #finally, call the script to get the apc back

        # adj_matrix = sympy.zeros(n,n)
        # # #fill in the adjacency matrix
        # #first identify the function start
        # function_start=fun
        # function_end=fun
        # for block in fun_blocks:
        #     for bblock_id, bblock_dict in fun_blocks.items():
        #         #obviously we shouldn't see if the basic block calls itself, that's ok
        #         if bblock_id == block:
        #             continue
        #         #if another basic block in the function calls this one, this one can't be
        #         #the first basic block in the function
        #         if block in bblock_dict['dests']:
        #             continue
        #         function_end=bblock_id
        # #fill in the adj_matrix with the ending block at the end
        # #and the starting block at the origin
        # #to put starting block at origin and fill in the matrix in an order,
        # #we'll partially order the blocks to have function start at the start
        # partially_ordered_blocks = [function_start]
        # for block in fun_blocks:
        #     if block == function_end or block == function_start:
        #         continue
        #     partially_ordered_blocks.append(block)
        # if function_start != function_end:
        #     partially_ordered_blocks.append(function_end)
        # i = 0
        # for block in partially_ordered_blocks:
        #     j = 0
        #     for dblock in partially_ordered_blocks:
        #         if dblock in fun_blocks[block]['dests']:
        #             adj_matrix[i,j] = 1
        #         j += 1
        #     i+=1
        # #last element must be 1 to get determinant
        # adj_matrix[-1,-1] = 1
        # logger.debug(f"function {fun} adj_matrix = {adj_matrix}")
        # results[fun_name]['adjacency matrix'] = adj_matrix
        # with ThreadingTimeout(seconds=10):
        #     degree, solution_terms = calc_func_apc(adj_matrix,n)
        # results[fun_name]['degree'] = degree
        # results[fun_name]['solution terms'] = solution_terms
    command = f"python3 src/oxide/modules/extractors_dev/path_complexity/src/binary_run.py"
    for f_fname in fun_filenames:
        command += f" {f_fname}"
    pythonpath = ""
    for directory in sys.path:
        pythonpath = pythonpath + directory + ";"
    env = os.environ.copy()
    try:
        subproc_out = subprocess.check_output(command, universal_newlines=True, shell=True, stderr=subprocess.STDOUT,env=env)
    except subprocess.CalledProcessError as e:
        print(e.output)
        outstring = ""
        for f in fun_filenames:
            outstring += f'"{f}" '
        print(outstring.strip())
        return None
    subproc_out = subproc_out.split("\n")
    #we'll trim the junk before the function name off the output
    trim_len=len(str(oid)+"_.")
    for line in subproc_out[:-1]:
        line = line.split("|")
        fun_name = line[0][trim_len:]
        if len(line) < 2 or fun_name not in results: continue
        results[fun_name] = {"O":line[1]}
            
    #clean up the created files
    # for f_fname in fun_filenames:
    #     try:
    #         os.remove(f_fname)
    #     except:
    #         pass
    while not api.store(NAME,oid,results,opts):
        sleep(1)
        logger.info(f"trying to store to api")
    return results
