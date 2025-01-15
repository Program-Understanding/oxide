AUTHOR="kevan"
DESC="Unfinished module to test out how angr's loop analysis thing works"
NAME="angr_loop_analysis"

from oxide.core import api
import logging

logger = logging.getLogger(NAME)
opts_doc = {}

def documentation():
    return {"description":DESC, "opts_doc": opts_doc, "private": False,"set":False, "atomic": True}

def process(oid, opts):
    from oxide.core.libraries.angr_utils2 import angrManager, angrTherapy,angrManagerProxy
    angrManager.register("angr_project",angrTherapy,angrManagerProxy)
    with angrManager() as angrmanager:
        angrproj = angrmanager.angr_project(oid)
        analysis = angrproj.loop_analyzer()
    print(analysis)
    return analysis
