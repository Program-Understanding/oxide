AUTHOR="KEVAN"
DESC="Analyze path complexity of a binary to know if we gonna have path explosion"
NAME="path_complexity"

import logging
logger = logging.getLogger(NAME)

from core import api
import numpy
import sympy
import time

opts_doc={"timeout": {"type": int, "mangle": False, "default": 600, "description": "Time in seconds for angr before it times out, default is 5 minutes"},
          "use_angr": {"type": bool, "mangle": True, "default": False, "description": "Try to see how long angr will take on functions"}}

def documentation():
    return {"description":DESC,
            "opts_doc": opts_doc,
            "private": False,
            "set": False,
            "atomic":True
            }

import angr

def k_step_func(simmgr):
    global start_time
    global timeout
    if start_time is None:
        start_time = time.time()
    if time.time() - start_time > timeout: #checking timeout limit
        start_time = None
        simmgr.move(from_stash="active", to_stash="deadend")
    return simmgr

start_time = None
timeout = None

def calc_func_apc(adj_matrix,n):
    #breaking up these variables for testing/debugging
    I = sympy.eye(n) #identity matrix
    z = sympy.symbols('z') #our symbolic variable 'z'
    z_T = z*adj_matrix
    I_z_T = sympy.Matrix(I-adj_matrix*z)
    qz = sympy.expand(-I_z_T.det())
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
    ordered_terms = bounded_solution_terms.as_ordered_terms()
    logger.debug(f"big o: {ordered_terms[0]}")
    return ordered_terms[0]

def results(oid_list, opts):
    """
    This will return the adjacency matrix
    it will also return the estimated path complexity, and optionally return the time angr took to run the
    program fully via symbolic execution. angr's timeout can be set by passing in a timeout option
    """
    global start_time
    global timeout
    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        results[oid] = {}
        #temp code just to keep track of the filename
        data = api.get_field(api.source(oid), oid, "data", {})
        f_name = api.get_field("file_meta", oid, "names").pop()
        f_name = api.tmp_file(f_name, data)
        logger.debug(f_name)
        #quickly check if we should set up an angr project
        #for the file
        if opts['use_angr']:
            #set the timeout option for our step function
            timeout = opts['timeout']
            #find out how long it'll take angr to symbolically execute this
            #create temp file to work on
            data = api.get_field(api.source(oid), oid, "data", {})
            #make an angr project and get the CFG
            proj = angr.Project(f_name,load_options={"auto_load_libs":False})
            #silence the logger
            angr_logger = logging.getLogger("angr")
            angr_logger.setLevel(50)
            cfg = proj.analyses.CFGFast()
        
        #use ghidra to get the adjacency matrix
        original_blocks = api.get_field("ghidra_disasm", oid, "original_blocks")
        funs = api.retrieve("function_extract",oid)
        for fun in funs:
            results[oid][fun] = {'vaddr':funs[fun]['vaddr']}
            #go through every function to make function-level adjacency graph to
            #calculate the apc
            fun_blocks = {}
            for block in original_blocks.keys():
                if block in funs[fun]['blocks']:
                    fun_blocks[block] = original_blocks[block]
            n = len(funs[fun]['blocks'])
            #if we don't have any basic block members
            #or if we only have 1 basic block
            #we don't want to say for sure
            if n < 2:
                results[oid][fun]['apc']= "Unknown..."
                continue
            adj_matrix = sympy.zeros(n,n)
            #fill in the adjacency matrix
            #first identify the function start
            function_start=funs[fun]['start']
            function_end=funs[fun]['start']
            for block in fun_blocks:
                for bblock_id, bblock_dict in fun_blocks.items():
                    #obviously we shouldn't see if the basic block calls itself, that's ok
                    if bblock_id == block:
                        continue
                    #if another basic block in the function calls this one, this one can't be
                    #the first basic block in the function
                    if block in bblock_dict['dests']:
                        continue
                    function_end=bblock_id
            #fill in the adj_matrix with the ending block at the end
            #and the starting block at the origin
            #to put starting block at origin and fill in the matrix in an order,
            #we'll partially order the blocks to have function start at the start
            partially_ordered_blocks = [function_start]
            for block in fun_blocks:
                if block == function_end or block == function_start:
                    continue
                partially_ordered_blocks.append(block)
            if function_start != function_end:
                partially_ordered_blocks.append(function_end)
            i = 0
            for block in partially_ordered_blocks:
                j = 0
                for dblock in partially_ordered_blocks:
                    if dblock in fun_blocks[block]['dests']:
                        adj_matrix[i,j] = 1
                    j += 1
                i+=1
            logger.debug(f"function {fun} adj_matrix = {adj_matrix}")
            #last element must be 1 to get determinant
            adj_matrix[-1,-1] = 1
            results[oid][fun]['adjacency matrix'] = adj_matrix
            results[oid][fun]['apc'] = f"Big O({calc_func_apc(adj_matrix,n)})"
            #now we process angr
            if opts['use_angr']:
                #simply walk through all possible code paths
                fun_addr = proj.loader.min_addr + funs[fun]['start']
                state = proj.factory.blank_state(addr=fun_addr)
                simgr = proj.factory.simulation_manager(state)
                #step until we have no more active states
                start_time = time.time()
                while len(simgr.active):
                    simgr.step(step_func=k_step_func)
                results[oid][fun]['seconds angr took'] = time.time() - start_time
                results[oid][fun]['states angr made'] = sum([len(simgr.stashes[stash]) for stash in simgr.stashes])
                if fun_addr in cfg.kb.functions:
                    results[oid][fun]["angr's reported cyclomatic complexity"] = cfg.kb.functions[fun_addr].cyclomatic_complexity
                    #build an adjacency matrix using angr
                    #map from angr addr to index in p_o_b
                    #to use in the adj_matrix
                    map_to_pob = {}
                    for i in range(len(partially_ordered_blocks)):
                        map_to_pob[partially_ordered_blocks[i]+proj.loader.min_addr]=i
                    angr_adj_matrix = sympy.zeros(n,n)
                    for node, dest in proj.kb.functions[fun_addr].transition_graph.edges:
                        if node.addr in map_to_pob and dest.addr in map_to_pob:
                            angr_adj_matrix[map_to_pob[node.addr],map_to_pob[dest.addr]] = 1
                    angr_adj_matrix[-1,-1] = 1
                    results[oid][fun]["angr's adj matrix"] = angr_adj_matrix
                    results[oid][fun]["apc with angr's adj matrix"] = calc_func_apc(angr_adj_matrix,n)
        #api.store(NAME,oid,results,opts)
    return results
