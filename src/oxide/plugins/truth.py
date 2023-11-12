""" Plugin: Utility functions for managing truth files.
"""
import os
import json
import progress, api
import core.sys_utils

def read_truth(args, opts):
    """
        Sets the min and/or max truth file representing a correct disassembly for an oid.
        Syntax: set_truth <oid>
    """
    args, invalid = api.valid_oids(args)
    if not invalid:
        raise ShellSyntaxError("Must provide a path.")

    for path in invalid:
        if os.path.isfile(path): # read a single file
            read_truth_file(path)
        elif os.path.isdir(path): # read a directory
            print("Reading directory: %s" %(path))
            files_list = core.sys_utils.get_files_from_directory(path)
            p = progress.Progress(len(files_list))
            for file_location in files_list:
                if 'pointer_dev' in file_location:
                    continue
                print(file_location)
                read_truth_file(file_location)
                p.tick()
        else:
            raise ShellSyntaxError(" - %s is not a file or direcotry, skipping" % (path))
    return args


exports = [read_truth]

##################### UTILS ############################


def process_insn_truth(oid: str, data: dict, meta: dict):
    print("INFO:Truth: processing insn file {}".format(oid))
    data = data[1:]
    data_dict = {d[0]:d[1] for d in data}
    opts = {'type':meta['type']}
    # truth_store = api.retrieve("truth_store", oid)
    # if truth_store is None: truth_store = {}
    api.store('truth_store', oid, {'instructions':data_dict}, opts)


def process_block_truth(oid: str, data: dict, meta: dict):
    print("INFO:Truth: processing block file {}".format(oid))
    data = data[1:]
    data_dict = {}
    for d in data:
        data_dict[d[0]] = {'members': [[x, 'truth'] for x in d[1]], 'targets': d[2]}
    opts = {'type':meta['type']}
    # truth_store = api.retrieve("truth_store", oid)
    # if truth_store is None: truth_store = {}
    api.store('truth_store', oid, {'original_blocks':data_dict}, opts)
    print(data_dict)


def process_function_truth(oid: str, data: dict, meta: dict):
    print("INFO:Truth: processing function file {}".format(oid))
    data = data[1:]
    data_dict = {d[0]:{'name': d[1]} for d in data}
    opts = {'type':meta['type']}
    # truth_store = api.retrieve("truth_store", oid)
    # if truth_store is None: truth_store = {}
    api.store('truth_store', oid, {'functions':data_dict}, opts)


def read_truth_file(path):
    try:
        fname, fext = os.path.splitext(path)
        if fext == ".truth":
            with open(path, 'r') as f:
                data = json.load(f)
                print("file: ", path, " entries: ", len(data))
                meta = data[0]
                oid = meta['oid']
                name = ""
                if api.exists("file_meta", oid):
                    name = api.get_field("file_meta", oid, "names").pop()
                print("Matched: ", name)
                if meta['type'] == "disasm_min" or meta['type'] == "disasm_max":
                    process_insn_truth(oid, data, meta)
                elif meta['type'] == "block_min":
                    process_block_truth(oid, data, meta)
                elif meta['type'] == "functions":
                    process_function_truth(oid, data, meta)
                else:
                    print('Unhandled Truth format {}'.format(meta['type']))
    except IOError as err:
        ShellSyntaxError("IOError:" + str(err))
