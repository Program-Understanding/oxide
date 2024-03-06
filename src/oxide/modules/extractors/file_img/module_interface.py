DESC = " Makes a file into an image for analysis in machine learning"
NAME = "file_img"
USG = " This module takes a collection of binary files and extracts from \
ghidra_disasm the instructions. Opcode from each instruction is used for \
each channel in the image. It stores the image in a numpy array \
returned in a dictionary. The dictionary has the original and resized\
image, where user can set resized image's size"

import cv2
import numpy as np
import math
import logging
from oxide.core import api
logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {"size":{"type": int, "mangle":False,"default":1000,"description":"Size of the generated image. Interpreted as size x size, in order to keep uniformity for use with neural network"},"show":{"type":bool,"mangle":False,"default":False,"description":"Show the generated binary image"}}

def documentation():
    return {"description": DESC, "opts_doc": opts_doc, "set": False, "atomic": True, "usage":USG}

def process(oid, opts):
    names = api.get_field("file_meta", oid, "names")
    insns = api.get_field("disassembly",oid,oid)
    funs = api.get_field("ghidra_disasm", oid, "functions")
    bbs = api.get_field("ghidra_disasm", oid, "original_blocks")

    size = int(math.sqrt(len(insns['instructions'])))+1 if int(math.sqrt(len(insns['instructions'])))*int(math.sqrt(len(insns['instructions']))) < len(insns['instructions']) else int(math.sqrt(len(insns['instructions'])))

    if not 'instructions' in insns:
        logger.info(f"{oid} doesn't have instructions!")
        return False

    output_img = np.zeros((size,size,4),dtype=np.uint8)
    i = 0
    j = 0
    for ins in insns['instructions']:
        ins = insns['instructions'][ins]
        output_img[i,j] = (ins['opcode'][0],ins['opcode'][1],ins['opcode'][2],ins['opcode'][3])
        if i < size-1:
            i += 1
        else:
            i = 0
            j += 1

    resized_img = cv2.resize(output_img, dsize=(opts["size"], opts["size"]), interpolation=cv2.INTER_NEAREST)

    if opts["show"]:
        cv2.imshow(oid,resized_img)
        cv2.waitKey(0)
        cv2.destroyAllWindows()

    api.store(NAME,oid,{"original_image": output_img,"resized_image":resized_img},opts)
    return True
