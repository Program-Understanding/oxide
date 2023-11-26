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

"""
Options expert - provides API for dealing with options, to include specific
functionality that is useful only to filesystem storage backend.

This is a separate module because two inter-dependent modules (oxide and
datastore_filesystem) need the functions here.
"""

import logging

from oxide.core import api, otypes

from typing import List, Any, Dict, Tuple


NAME = 'options'
logger = logging.getLogger(NAME)

"""
    -------------------------- OPTION-HANDLING FUNCTIONS --------------------------

 Delimiter between option values (keys are not included in suffix). This is
 a value that is not likely to appear in an option value. If it does, then
 it could break the scheme used here.
"""

SUFFIX_DELIM = '='


def normalize_mangled_options(mod_name: str, opts: Dict[str, Any]) -> List[Tuple[str, Any]]:
    mfields = mangle_fields(mod_name)
    if mfields:
        norm_options = sorted(opts.items())
    else:
        norm_options = list()

    return norm_options


def mangle_fields(mod_name: str) -> List[str]:
    """ Returns the keys of the mangled options for the given module. The
        returned keys are sorted.

        Exported function
    """
    doc = api.documentation(mod_name)
    if not doc: return []
    all_opts = doc["opts_doc"]

    mangles = list()
    for field in all_opts:
        try:
            if all_opts[field]["mangle"]:
                mangles.append(field)
        except KeyError:
            raise otypes.OxideError("{} Module writer left out the mangle field in options.".format(mod_name))
    mangles.sort()
    return mangles


def mangle_options(mod_name: str, opts: Dict[str, Any]) -> Dict[str, Any]:
    """ Return subset of module's options dictionary 'opts'; only mangle options
        will be in returned dictionary.
    """
    mangle_keys = mangle_fields(mod_name)

    mangle_dict = dict([(k, v) for (k, v) in opts.items() if k in mangle_keys])
    return mangle_dict


def build_suffix(mod_name: str, opts: Dict[str, Any]) -> str:
    """ Support specifically for filesystem storage backend. The suffix will look
        like this: val1=val2=val3, where the values are in the order of their
        respective keys. Only mangle options are included in the suffix.
    """

    suffix = ""  # default val
    mfields = mangle_fields(mod_name)
    if len(mfields) > 0:
        # doc = api.documentation(mod_name) # DELETEME:: unused
        slist = [str((opts[field])) for field in mfields]
        suffix = SUFFIX_DELIM.join(slist)
    return suffix


def parse_suffix(mod_name: str, suffix: str) -> Dict[str, Any]:
    """ Given module and suffix, return dictionary of mangle options with fields
        filled in from the suffix.
    """

    # doc = api.documentation(mod_name) DELETEME::unused
    # all_opts = doc["opts_doc"] DELETEME::unused

    # returns field names, sorted (same order as their vals appear in suffix)
    mangles = mangle_fields(mod_name)
    vals = [otypes.cast_string(s) for s in suffix.split(SUFFIX_DELIM)]

    if len(mangles) != len(vals):
        raise otypes.OxideError("suffix must contain as many values as there are mangle options")

    # build the key->val pairs from the suffix
    mangle_dict = dict(list(zip(mangles, vals)))

    return mangle_dict


def validate_opts(mod_name: str, opts: Dict[str, Any], only_mangle: bool = False) -> bool:
    """ Validate opts checks for option correctness and fills in
        defaults.

        TODO: can oshell._validate_opts() use this function instead?
    """
    doc = api.documentation(mod_name)
    if not doc: return False
    opts_doc = doc["opts_doc"]
    mangled_fields = mangle_fields(mod_name)
    for k in opts_doc:
        if not only_mangle or k in mangled_fields:
            # No option provided for this key
            if k not in opts:
                # Set value of key to default provided if present
                if "default" in opts_doc[k]:
                    logger.debug("%s option '%s' not provided. Setting to default value.", mod_name, k)
                    if opts_doc[k]["default"] is None:
                        logger.error("Module %s has no default for required key %s", mod_name, k)
                        return False
                    opts[k] = opts_doc[k]["default"]
                else:
                    logger.error("Module %s has no default for required key %s", mod_name, k)
                    return False

            # FIXME:: incomplete logic, possibly commented out close to correct logic
            try:
                tmp = opts_doc[k]["type"](opts[k])
            except (ValueError, TypeError):
                # if not isinstance(opts[k], opts_doc[k]["type"]): # Wrong option type provided
                logger.error("%s option '%s' type mismatch.", mod_name, k)
                return False
    return True
