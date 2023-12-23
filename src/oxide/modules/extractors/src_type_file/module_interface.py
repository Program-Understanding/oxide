DESC = " This module attempts to determine the type of a file using `file`."
NAME = "src_type_file"
USG = "This analyzes a file and tells the user what type of file it is. module returns a dictionary with two key-value pairs source and \
type"

import subprocess
import logging

import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}

# Check if this is present on system
subprocess.run(['file', '--version'], stdout=subprocess.DEVNULL)


def documentation() -> None:
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage": USG}


def process(oid: str, opts: dict = {}) -> bool:
    """ Attempt to detect possible types of file.
    """
    logger.debug("process()")
    src = api.source(oid)
    src_type = {"source":src}
    #src_type = api.get_field("src_type", oid, "type")
    logger.debug("Processing file %s", str(oid))
    if src == "ocollections":
        src_type["type"] = "ocollection"
    else:
        data = api.get_field(src, oid, "data", {})
        if not data:
            logger.debug("Not able to process %s", oid)
            return False
        f_name = api.get_field("file_meta", oid, "names").pop()
        f_name = api.tmp_file(f_name, data)
    
        try:
            file_res = subprocess.check_output(['file', f_name])
        except subprocess.CalledProcessError:
            # could not run file on temporary file
            return False
        try:
            file_res = file_res[file_res.index(b': ')+2: file_res.index(b',')]  # Prune up to `:` and stop before `,`
        except ValueError:
            # Subsection not found, either , or :
            return False
        src_type["type"] = set(file_res)
        src_type["type"] += api.retreive("src_type", oid)

    src_type["original_file"] = api.get_field("file_meta", oid, "original_paths")
        

    api.store(NAME, oid, src_type, opts)
    return True
