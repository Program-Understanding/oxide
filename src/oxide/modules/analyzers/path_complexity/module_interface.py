AUTHOR="KEVAN"
DESC="Analyze path complexity of a binary to know if we gonna have path explosion"
NAME="path_complexity"

import logging
logger = logging.getLogger(NAME)

opts_doc={}

def documentation():
    return {"description":DESC,
            "opts_doc": opts_doc,
            "private": False,
            "set": False,
            "atomic":True
            }

def results(oid_list, opts):
    oid_list = api.expand_oids(oid_list)
    results = {}
    for oid in oid_list:
        #create temp file to work on
        data = api.get_field(api.source(oid), oid, "data", {})
        f_name = api.get_field("file_meta", oid, "names").pop()
        f_name = api.tmp_file(f_name, data)
    
