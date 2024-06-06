AUTHOR="KEVAN"
DESC="Use this module to dump constraint information used by angr's backend Claripy and z3"
NAME="angr_constraint_count"

from core import api
import logging
import angr
import claripy
import z3

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

def documentation():
    return {"description":DESC,
            "opts_doc": opts_doc,
            "private": False,
            "set": False,
            "atomic":True
            }

def mapper(oid, opts,jobid=False):
    """Entry point for analyzers, these do not store in database
    these are meant to be very quickly computed things passed along
    into other modules

    This function will accept an and give back a dictionary
    which contains information gotten from angr regarding the constraints
    angr generated during its symbolic execution of the program.
    Constraints are returned both in angr's native claripy format and the z3
    format that claripy uses in the backend (it converts to z3 inherently
    due to its use of z3)

    Results are separated by deadended state, then z3 and claripy, then
    each scopes further respective to the backend.
    """
    output_dict = {}
    data = api.get_field(api.source(oid), oid, "data", {}) #get file data
    f_name = api.get_field("file_meta", oid, "names").pop()
    f_name = api.tmp_file(f_name, data) #make temp file for anger project

    #angr_proj = init_angr_project(f_name, header) #angr project seemingly not working right
    #logger stuff from init_angr_project() that seems useful
    cle_logger = logging.getLogger("cle")
    cle_logger.setLevel(50)
    angr_logger = logging.getLogger("angr")
    angr_logger.setLevel(50)
    claripy_logger = logging.getLogger("claripy")
    claripy_logger.setLevel(50)
    pyvex_logger = logging.getLogger("pyvex.lifting.libvex")
    pyvex_logger.setLevel(50)
    pyvex_logger = logging.getLogger("pyvex.lifting.util")
    pyvex_logger.setLevel(50)
    identifier_logger = logging.getLogger("angr.analyses.identifier.identify")
    identifier_logger.setLevel(50)
    proj = angr.Project(f_name)
    logger.debug(f"{oid} entry addr: "+hex(proj.entry))
    state = proj.factory.entry_state()
    state.options |= {angr.sim_options.CONSTRAINT_TRACKING_IN_SOLVER}
    state.options -= {angr.sim_options.COMPOSITE_SOLVER}
    # todo keep track of what the constraints are at the end
    # then categorize them and send them back to the user
    # maybe in a dictionary like {category : number}

    simgr = proj.factory.simulation_manager(state)
    simgr.explore()

    for s in range(len(simgr.deadended)): #s is state number
        state = simgr.deadended[s]
        output_dict['deadend ' + str(s)] = {}
        cons = []
        cl_cons = []
        for c in state.solver.constraints:
            cl_cons.append(c)
            cons.append(claripy.backends.z3.convert(c))
        con_trees = set() #getting unique entries
        cl_leafs = set() #because there are a lot of duplicates
        for co in cl_cons:
            if not co.concrete:
                #don't worry about concrete vars
                con_trees.add(c)
                for co_l in co.recursive_leaf_asts:
                    cl_leafs.add(c)
        cl_d = {}
        cl_d["trees"] = con_trees if len(con_trees) > 0 else "None"
        cl_d["leafs"] = cl_leafs if len(cl_leafs) > 0 else "None"
        output_dict['deadend ' + str(s)]["claripy"] = cl_d
        solver = z3.Solver()
        for c in cons:
            solver.add(c)
        if solver.check() == z3.sat:
            m = solver.model()
            if len(m)>0:
                z3d = {}
                z3d["sexpr"] = m.sexpr()
                z3d["model"] = m
                output_dict['deadend ' + str(s)]["z3"] = z3d
                continue
            output_dict['deadend ' + str(s)]["z3"] = "None"
    api.store(NAME,oid,output_dict,opts)
    return oid

def reducer(intermediate_out, opts, jobid):
    counts = {}
    for oid in intermediate_out:
        if oid:
            res = api.retrieve(NAME,oid,opts)
            for deadend in res: #iterate through each deadend state
                for backend in res[deadend]: #iterate z3 and claripy
                    if res[deadend][backend] == 'None':
                        continue #z3 might be none if there's nothing to show
                    for subtype in res[deadend][backend]:
                        #subtype is "trees", "leafs", "model", etc.
                        #couldn't think of a more applicable name sorry
                        s = str(res[deadend][backend][subtype])
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
    if counts == {}:
        counts = "No constraints"
    return counts
