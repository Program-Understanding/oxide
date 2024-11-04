AUTHOR="KEVAN"
NAME="angr_parameter_optimization.param_helper"
"""
This file hides some of the helper functions used in the angr_parameter_optimization module
"""
import logging
logger = logging.getLogger(NAME)
my_tactics = []
my_tactic = ""
def my_solver(self, timeout=None, max_memory=None):
    """ 
    This replaces the backend Z3 solver used by angr
    """
    global my_tactics
    global my_tactic
    from threading import current_thread, main_thread
    if not self.reuse_z3_solver or getattr(self._tls, "solver", None) is None:
        import z3
        if my_tactics:
            s = z3.Then(*(z3.Tactic(t,ctx=self._context) for t in my_tactics),ctx=self._context).solver()
        elif my_tactic:
            s = z3.Tactic(my_tactic,ctx=self._context).solver()
        else:
            s = z3.Solver()  # , logFile="claripy.smt2")
        if current_thread() != main_thread():
            s.set(ctrl_c=False)
        try:
            import __pypy__
            __pypy__.add_memory_pressure(1024 * 1024 * 10)
        except ImportError:
            _is_pypy = False
        if self.reuse_z3_solver:
            # Store the Z3 solver to a thread-local storage if the reuse-solver option is enabled
            self._tls.solver = s
    else:
        # Load the existing Z3 solver for this thread
        s = self._tls.solver
        s.reset()

    # Configure timeouts
    if timeout is not None:
        if "soft_timeout" in str(s.param_descrs()):
            s.set("soft_timeout", timeout)
            s.set("solver2_timeout", timeout)
        else:
            s.set("timeout", timeout)
    if max_memory is not None:
        s.set("max_memory", max_memory)
    return s

def set_simgr_techniques(explor, simgr):
    import angr
    supported_options = ["dfs","loops","unique"]
    simgr.use_technique(angr.exploration_techniques.DFS())
    if explor:
        for opt in explor.split(","):
            match opt:
                case "dfs":
                    simgr.use_technique(angr.exploration_techniques.DFS())
                case "loops":
                    simgr.use_technique(angr.exploration_techniques.LoopSeer())
                case "unique":
                    simgr.use_technique(angr.exploration_techniques.UniqueSearch())
                case "veritesting":
                    simgr.use_technique(angr.exploration_techniques.veritesting.Veritesting())
                case _:
                    logger.error(f"Unknown exploration option {explor}\
                    try from the following: {supported_options}")
                    return False
