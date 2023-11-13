"""
Copyright 2023 National Technology & Engineering Solutions
of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS,
the U.S. Government retains certain rights in this software.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
"""

""" Plugin: Utility functions for manipulating files and collections
"""
NAME = "default_plugin"

import random
import json
import pickle
import os
import zipfile
import tarfile
import gzip
import tempfile
import socket
import string
import logging
from oxide.modules.extractors.elf.interpret_elf import ElfRepr
from collections import defaultdict

from typing import List, Dict, Optional, Any, Union, Iterable

from oxide.core import progress, api

proxy = None
random.seed()

logger = logging.getLogger(NAME)
logger.debug("init")

def membership(args: List[str], opts: dict) -> Dict[str, List[str]]:
    """
        Prints the set of collections to which a file belongs.
                If a collection is passed its membership will not be printed
        Syntax: membership %<oid> ...
    """
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")

    exclude_cids = [oid for oid in valid if api.exists("collections", oid)]
    main_oids = set(api.expand_oids(valid))

    membership_cids = {}
    cids = [cid for cid in api.collection_cids() if cid not in exclude_cids]
    for cid in cids:
        this_oids = set(api.expand_oids(cid))
        this_intersection = list(main_oids.intersection(this_oids))
        if this_intersection:
            membership_cids[cid] = this_intersection

    if "noprint" not in opts:
        print_membership(membership_cids)

    return membership_cids


def summarize(args: List[str], opts: dict) -> None:
    """
        Gives a summary of a set of files, including types, extensions, etc.  If no argument
                is passed, gives a summary for the entire datastore (may be very slow).
        Syntax: summarize %<oid>
    """
    valid, invalid = api.valid_oids(args)
    valid = set(api.expand_oids(valid))
    types = defaultdict(int)
    extensions = defaultdict(int)
    sizes = [0,0,0,0,0,0]

    if not args:
        valid = set(api.retrieve_all_keys("file_meta"))

    for oid in valid:
        meta = api.retrieve("file_meta", oid)
        names = meta["names"]
        if names:
            for name in names:
                parts = name.split(".")
                if len(parts) > 1:
                    extensions[parts[-1]] += 1
                else:
                    extensions["None"] += 1
        t = api.get_field("src_type", oid, "type")
        if t: types[t.pop()] += 1
        size = meta["size"]
        if size < 1024: sizes[0] += 1
        elif size < 10*1024: sizes[1] += 1
        elif size < 100*1024: sizes[2] += 1
        elif size < 1024*1024: sizes[3] += 1
        elif size < 10*1024*1024: sizes[4] += 1
        else: sizes[5] += 1

    print("\nTotal files in set: ", len(valid))

    print("\nExtensions (files with multiple names counted more than once):")
    exts = list(extensions.keys())
    exts = sorted(exts, key=lambda val: extensions[val], reverse=True)
    for e in exts:
        print("  ", e, "   \t\t  :\t\t  ", extensions[e])
    print("\nTypes:")
    ts = list(types.keys())
    ts = sorted(ts, key=lambda val: types[val], reverse=True)
    for t in ts:
        print("  ", t, "   \t\t  :\t\t  ", types[t])

    print("\nSizes: ")
    print("   Under 1k   :", sizes[0])
    print("   1k - 10k   :", sizes[1])
    print("   10k - 100k :", sizes[2])
    print("   100k - 1MB :", sizes[3])
    print("   1MB - 10MB :", sizes[4])
    print("   over 10 MB :", sizes[5])

    return None


def intersection(args: List[str], opts: dict) -> List[str]:
    """
        Returns the intersection of the collections passed in, non-collection IDs will be ignored
        Syntax: intersection &col1 &col2 ...
    """
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")
    cids = [oid for oid in valid if api.exists("collections", oid)]
    if not cids:
        raise ShellSyntaxError("No valid collections found")
    oids = set(api.expand_oids(cids[0]))
    for c in cids[1:]:
        oids = oids.intersection(api.expand_oids(c))
    return oids


def file_io(args: List[str], opts: dict) -> Union[List[str], Any]:
    """ store or retrieve contents of a Python data structure
        Syntax:
            file_io <file_name> | show     # Retrieve from a file
            @<var> | file_io <file_name>   # Write to a file
    """
    if not args:
        raise ShellSyntaxError("File name not specified")

    fname = args[0]
    args = args[1:]
    if args: # Writing to a file

        if 'pickle' in opts:
            fd = open(fname, 'wb')
            pickle.dump(args, fd)
            fd.close()
        else:
            fd = open(fname, 'w')
            logger.info('Note: All sets in results are converted to lists. This is unique behavior when compared to pickle export.')
            json.dump(_sets_to_lists(args), fd)
            fd.close()

        return args

    else: # Reading from a file
        if not os.path.isfile(fname):
            raise ShellSyntaxError("File %s not found." % fname)
        with open(fname, 'rb') as fd:

            err = False
            if 'pickle' in opts:
                try:
                    p = pickle.load(fd)
                except pickle.UnpicklingError:
                    # tried pickle, but not pickle, syntax error
                    err = True
            else:
                # json mode
                try:
                    p = json.load(fd)
                except UnicodeDecodeError:
                    # wasn't json, try pickle?
                    try:
                        fd.seek(0)  # reset file pointer
                        p = pickle.load(fd)
                    except EOFError:
                        # one clue pickle was bad
                        print('wut')
                        err = True
                except NotImplementedError:
                    print('huh')
                    err = True
            if err:
                raise ShellSyntaxError(f'Import file was not a valid ({"pickle" if "pickle" in opts else "json"}) file. Did you need to include `--pickle`')

        return p


def clean(args: List[str], opts: dict) -> List[str]:
    """
        Passes a list where empty dict keys are removed
        Syntax: <some_command> | clean | ...
    """
    out = []
    for a in args:
        if not a:
            continue
        if isinstance(a, dict):
            bad_keys = []
            for k in a:
                if not a[k]:
                    bad_keys.append(k)
            for k in bad_keys:
                del a[k]
            out.append(a)
        else:
            out.append(a)
    return out


def expand(args: List[str], opts: dict) -> List[str]:
    """
        Passes a list where any cids passed are expanded to the oids in that collection
        Syntax: &<my_collection> | expand | ...
    """
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")
    return api.expand_oids(valid)


def random_sample(args: List[str], opts: dict):
    """
        Given a list of oids passes a random subset of them
        syntax: random_sample <oid1> <oid2> ... <oidn> [--n=<size> | --p=<percent>]
                (default is 10%)
    """
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")
    args = api.expand_oids(valid)
    if not args:
        return []

    nargs = len(args)
    n = int( round( nargs / float(10) ) )

    if "n" in opts:
        try:
            n = int(opts["n"])
            if n < 0: raise ValueError
            if n > nargs: n = nargs
        except ValueError:
            raise ShellSyntaxError("Invalid integer value for n: %s" % opts["n"])
    elif "p" in opts:
        try:
            p = float(opts["p"])
            if p <= 0 or p > 100: raise ValueError
        except ValueError:
            raise ShellSyntaxError("Invalid float value for p: %s" % opts["p"])
        n = int( round( len(args) / (100/p) ) )

    if n == 0: n = 1
    return random.sample(args, n)


def random_shuffle(args: List[str], opts: dict) -> List[str]:
    """
        Passes a randomized list of oids
        syntax: random_shuffle <oid1> <oid2> ... <oidn>
    """
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")
    args = api.expand_oids(valid)
    random.shuffle(args)
    return args


def top_n(args: List[Union[Iterable, Any]], opts: dict):
    """
        Passes up to the top n (default is 10) items passed. (e.g. histogram)
        Syntax: <some_command | top_n [--n=<int>] | ...
    """
    if not args:
        return []
    n = 10
    if "n" in opts:
        n = opts["n"]

    if isinstance(args[0], (dict, defaultdict)):
        keys = list(args[0].keys())
        key_len = len(keys)
        keys.sort(reverse=True, key=args[0].__getitem__)
        out = {}
        for i in keys[: min(n, key_len)]:
           out[i] = args[0][i]
        return [out]

    else:
        key_len = len(args)
        args.sort()

    return args[: min(n, key_len)]


def count(args: List[str], opts: dict) -> List[str]:
    """
        Prints the number of items passed. Passes whatever was passed.
        Syntax: <some_command> | count
    """
    print(" - Received: ", len(args), " args.")
    return args


def select(args: List[str], opts: dict) -> List[str]:
    """
        If passed a list of dictionaries, selects out the field indicated
        Syntax: select --field=field_name
    """
    if not args or not opts:
        return []
    if "field" in opts:
        field = opts["field"]
    else:
        return []
    new_args = []
    for a in args:
        if field in a and a[field]:
            new_args.append(a[field])
    return new_args


def extract_field(args: List[str], opts: dict):
    """
        Parses results of an analysis and extracts the given field for each file.
        Syntax: <some_command> | extract_field field_name
    """
    if len(args) <= 1:
        raise ShellSyntaxError("Pass in a fieldname as a string, followed by data.")
    field = args[0]
    new_args = {}
    results = args[1]
    if not isinstance(results, (dict, defaultdict)): return []
    for a in results:
        if not isinstance(results[a], (dict, defaultdict)): continue
        if field in results[a]:
            new_args[a] = results[a][field]
        else:
            for k in results[a]:
                if not isinstance(results[a][k], (dict, defaultdict)): continue
                if field in results[a][k]:
                    new_args[a] = results[a][k][field]
                else:
                    for j in results[a][k]:
                        if not isinstance(results[a][k][j], (dict, defaultdict)): continue
                        if field in results[a][k][j]:
                            new_args[a] = results[a][k][j][field]
    return new_args


def export_file(args, opts, directory = None):
    """
        Given a list of oid's exports the files. If tar or zip option used with
                multiple input files a single file will be exported.
        Syntax: export_file <oid1> <oid2> ... <oidn> [--zip | --tar [--bz2 | --gz] --name=<export_name> ]
    """
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")
    oids = api.expand_oids(valid)

    #Prompts the user for the directory
    directory = input("Enter what directory you want to export the file to: ")

    if "zip" in opts:
        export_tar_zip(oids, opts, type="zip", directory = directory)
    elif "tar" in opts:
        export_tar_zip(oids, opts, type="tar", directory = directory)
    else:
        export_files(oids, opts, directory = directory)


def cat(args: List[str], opts: dict) -> None:
    """
        Given an oid, displays the text of the file.  Should only be run on plain-text
                files.  Will give an error if file appears to not be plain-text.  Override with --force.
        Syntax: cat <oid>
    """
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")
    oids = api.expand_oids(valid)

    for o in oids:
        data = api.get_field("files", o, "data")

    printable = set(data).issubset(set(string.printable))
    if not printable and not "force" in opts:
        raise ShellSyntaxError("File contains non-printable characters.  Use --force to override.")
    else:
        print(data)


def size_filter(args: List[str], opts: dict) -> List[str]:
    """
        Filter files by size in bytes
        Syntax: size_filter %<oid> --min=<size> --max=<size>
    """
    if not args:
        raise ShellSyntaxError("File name not specified")

    min_size = int(opts["min"]) if ("min" in opts) else 0
    max_size = int(opts["max"]) if ("max" in opts) else None

    valid, invalid = api.valid_oids(args)
    oids = api.expand_oids(valid)
    filtered_oids = []
    for oid in oids:
        meta = api.retrieve("file_meta", oid)
        size = meta["size"]
        if size > min_size and ((not max_size) or size < max_size):
            filtered_oids.append(oid)

    return filtered_oids


def name_filter(args: List[str], opts: dict) -> List[str]:
    """
        Use without args to find files with that name, use with args to filter
        Syntax: name_filter %<oid> --name=<file_name>
    """
    if not "name" in opts:
        raise ShellSyntaxError("name_filter requires a --name=<file_name> option")

    oids = []
    valid, invalid = api.valid_oids(args)
    valid = api.expand_oids(valid)
    name = opts["name"]
    terms = name.split("*")

    if not args:
        if len(terms) == 1:
            return list(api.get_oids_with_name(opts["name"]).keys())
        else:
            valid = api.retrieve_all_keys("file_meta")

    if len(terms) == 1:
        for oid in valid:
            names = api.get_field("file_meta", oid, "names")
            if names and opts["name"] in names:
                oids.append(oid)
    else:
        for oid in valid:
            names = api.get_field("file_meta", oid, "names")
            if names:
                for name in names:
                    if name.startswith(terms[0]) and name.endswith(terms[1]):
                        oids.append(oid)
    return oids


def byte_filter(args: List[str], opts: dict) -> List[str]:
    """
        Use without args to find files with that byte_string, use with args to filter
        Syntax: byte_filter %<oid> --bytes=<byte_string>
    """
    if not "bytes" in opts:
        raise ShellSyntaxError("byte_filter requires a --bytes=<byte_string> option")

    oids = []
    valid, invalid = api.valid_oids(args)
    valid = api.expand_oids(valid)
    bytes = str(opts["bytes"]).encode()

    if not args:
        valid = api.retrieve_all_keys("files")

    for o in valid:
        data = api.get_field("files", o, "data")
        if data.find(bytes) != -1:
            oids.append(o)
    return oids


def type_filter(args: List[str], opts: dict) -> List[str]:
    """
        Use without args to find all files with that type, use with args to filter
        Syntax: type_filter %<oid> --type=[ PE | ELF | DEBUG | PDF | etc...]

        Note: DEBUG cannot be used for type, as DEBUG is processed as logging level
    """
    if not "type" in opts:
        raise ShellSyntaxError("type_filter requires a --type=[ PE | ELF | DBG | PDF | RTTI | etc...] option")

    oids = []
    valid, invalid = api.valid_oids(args)
    valid = api.expand_oids(valid)

    if not args:
        valid = api.retrieve_all_keys("files")

    for oid in valid:
        data_type = api.get_field("src_type", oid, "type")
        if data_type and any(item.lower() in opts["type"].lower() for item in data_type):
            oids.append(oid)
        elif (data_type and opts["type"].lower() == "exe" and
             (any(item.lower() in ['pe', 'elf', 'macho', 'osx universal binary'] for item in data_type))):
            # quick filter using executable to filter linux AND windows binaries
            oids.append(oid)
        elif (data_type and opts["type"].lower() == "dbg" and
             any(item.lower() == 'elf' for item in data_type)):
            # TODO:: expand further for other non-stripped formats
            header = api.get_field("object_header", oid, oid)
            if header:
                sections = header.section_info
                if sections:
                    if any(dwarf_name in sections.keys()
                           for dwarf_name in ['.debug_info', '.zdebug_info']):
                        # omit .eh_frame
                        oids.append(oid)
        elif (data_type and opts["type"].lower() == "rtti"):
            has_rtti = api.get_field("detect_rtti", oid, oid)
            if has_rtti:
                oids.append(oid)
    return oids

def symbol_filter(args: List[str], opts: dict) -> List[str]:
    """
        Use without args to find all files with symbols and filter by symbol type: linker symbols, stripped, or debug
        Syntax: symbol_filter %<oid> --type=[ linker | stripped | dbg ]

    """
    if not "type" in opts:
        raise ShellSyntaxError("symbol_filter requires a --type=[ linker | stripped | dbg ] option")

    #categorized_files = {
        #"linker": [],
        #"stripped": [],
        #"dbg": []
    #}

    oids = []

    valid, invalid = api.valid_oids(args)
    valid = api.expand_oids(valid)

    if not args:
        valid = api.retrieve_all_keys("files")

    for oid in valid:
        data_type = api.get_field("src_type", oid, "type")
        if (data_type and (opts["type"].lower() == "linker") and
             (any(item.lower() in ['pe', 'elf', 'macho', 'osx universal binary'] for item in data_type))):
                header = api.get_field("object_header", oid, oid)
                sections = header.section_info
                if sections:
                    if any(string_table in sections.keys()
                        for string_table in ['.strtab']):
                            #categorized_files["linker"].append(oid)
                            oids.append(oid)
        elif (data_type and (opts["type"].lower() == "stripped") and
               (any(item.lower() in ['pe', 'elf', 'macho', 'osx universal binary'] for item in data_type))):
                    header = api.get_field("object_header", oid, oid)
                    sections = header.section_info
                    if sections:
                        if not any(string_table in sections.keys()
                            for string_table in ['.strtab']):
                                #categorized_files["stripped"].append(oid)
                                oids.append(oid)

        elif (data_type and opts["type"].lower() == "dbg" and
             (any(item.lower() in ['pe', 'elf', 'macho', 'osx universal binary'] for item in data_type))):
            header = api.get_field("object_header", oid, oid)
            if header:
                sections = header.section_info
                if sections:
                    if any(dwarf_name in sections.keys()
                        for dwarf_name in ['.debug_info', '.zdebug_info']):
                            #categorized_files["dbg"].append(oid)
                            oids.append(oid)
    #filtered_categorized_files = {category: categoryOid for category, categoryOid in categorized_files.items() if categoryOid}
    #return filtered_categorized_files
    return oids


def key_filter(args: List[str], opts: dict) -> List[str]:
    """
        Use to match the results of a module (module name required). Specify key and optionally value.
        Syntax: key_filter %<oid> --module=<mod_name> --key=<key> [--value=<value>]
    """
    if not "module" in opts or not "key" in opts:
        raise ShellSyntaxError("key_filter requires a --module=<mod_name> and a --key=<key> option")
    oids = []
    valid, invalid = api.valid_oids(args)
    valid = api.expand_oids(valid)

    if not args:
        valid = api.retrieve_all_keys("files")

    if "key" in opts and "value" in opts:
        oids = api.retrieve("substring_search", valid,
            {"mod":opts["module"], "key":opts["key"], "value":opts["value"]})
    elif "key" in opts:
        oids = api.retrieve("key_search", valid,
            {"mod":opts["module"], "key":opts["key"]})
    return oids


def extension_filter(args, opts):
    """
        Use without args to find files with that extension, use with args to filter
        Syntax: extension_filter %<oid> --ext=<extension>
    """
    if not "ext" in opts:
        raise ShellSyntaxError("extension_filter requires a --ext=<extension> option")

    oids = set()
    valid, invalid = api.valid_oids(args)
    valid = api.expand_oids(valid)
    ext = opts["ext"]

    if not args:
        valid = api.retrieve_all_keys("file_meta")

    for oid in valid:
        names = api.get_field("file_meta", oid, "names")
        if names:
            for name in names:
                parts = name.split(".")
                if len(parts) > 1 and parts[-1].lower() == ext.lower():
                    oids.add(oid)
    return list(oids)


exports = [random_sample, random_shuffle, top_n, count, expand, clean, file_io, membership, select,
           extract_field, export_file, intersection, cat, summarize, size_filter, name_filter,
           byte_filter, type_filter, key_filter, extension_filter, symbol_filter]


# ---------------------------- UTILS -------------------------------------------------------------
def export_tar_zip(oids, opts, type, directory = None):
    name = "export"
    if "name" in opts:
        name = opts["name"] and opts["name"]

    if type == "tar" and not name.endswith(".tar"):
        name += ".tar"

    if type == "zip" and not name.endswith(".zip"):
        name += ".zip"

    mode = "w"
    if "bz2" in opts:
        mode += ":bz2"
        name += ".bz2"
    elif "gz" in opts:
        mode += ":gz"
        name += ".gz"

    if directory:
        name = os.path.join(directory, name)

    fname = unique_scratch_file(name)
    xo = None
    if type == "tar":
        xo = tarfile.open(fname, mode=mode)
    if type == "zip":
        xo = zipfile.ZipFile(fname, mode=mode)

    tmp_files = []
    names = []
    for oid in oids:
        data = api.get_field("files", oid, "data")
        if not data:
            logger.info("Not able to process %s" % oid)
            continue

        name = api.get_field("file_meta", oid, "names").pop()
        names.append(name)
        t = tmp_file(name, data)
        tmp_files.append(t)
        if type == "tar":
            xo.add(t)
        if type == "zip":
            xo.write(t)

    xo.close()
    logger.info(" - File(s) %s exported to %s" % (", ".join(names), fname))

    for f in tmp_files:
        os.remove(f)


def export_files(oids, opts, directory = None):
    base_name = "export"
    if "name" in opts and opts["name"]:
        base_name = opts["name"]

    for oid in oids:
        data = api.get_field("files", oid, "data")
        if not data:
            logger.info("Not able to process %s" % oid)
            continue
        name = api.get_field("file_meta", oid, "names").pop()
        name = base_name + "_" + name

        if directory:
            name = os.path.join(directory, name)

        write_file(name, data, directory)


def unique_scratch_file(name):
    base_name = os.path.basename(name)
    name = os.path.join(api.scratch_dir, base_name)
    if os.path.exists(name):
        name = tempfile.mktemp(suffix="_"+base_name, dir=api.scratch_dir)
    return name


def write_file(name, data, directory = None):
    if directory:
        os.makedirs(directory, exist_ok = True)
        name = os.path.join(directory, name)

    #name = unique_scratch_file(name)
    with open(name, "wb") as fd:
        fd.write(data)

    logger.info(" - File %s exported" % (name))


def print_membership(membership_cids: List[str]) -> None:
    logger.info("  --- Membership: ---")
    if not membership_cids:
        logger.info("   <EMPTY>")
    else:
        for cid in membership_cids:
            name = api.get_colname_from_oid(cid)
            logger.info("  - %s: ", name)
            for oid in membership_cids[cid]:
                names = ", ".join(list(api.get_names_from_oid(oid)))
                logger.info("    - %s : %s", oid, names)


def tmp_file(name, data):
    tmp = unique_scratch_file(name)
    fd = open(tmp, 'wb')
    fd.write(data)
    fd.close()
    return tmp

def _sets_to_lists(obj):
    if isinstance(obj, set):
        return list(obj)
    elif isinstance(obj, dict):
        return {k: _sets_to_lists(v) for k, v in obj.items()}
    elif isinstance(obj, list):
        return [_sets_to_lists(e) for e in obj]
    else:
        return obj
