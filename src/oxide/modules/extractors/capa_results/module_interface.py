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

DESC = "Runs Capa and collects to results"
NAME = "capa_results"

# imports
import logging

from typing import Dict, Any, List

from pathlib import *

from oxide.core import api

from typing import Any
from typing import *
from oxide.core import api
import capa.main
import capa.rules
import capa.engine
import capa.features
import capa.render.json
import capa.render.utils as rutils
import capa.render.default
import capa.render.result_document as rd
import capa.render.verbose
import capa.render.vverbose
import capa.features.freeze.features as frzf
import capa.loader
from pathlib import *
from capa.features.common import OS_AUTO, OS_LINUX, FORMAT_AUTO, FORMAT_ELF, FORMAT_SC64
import capa.features.freeze as frz

logging.basicConfig(level=logging.WARNING)
logging.getLogger().setLevel(logging.WARNING)

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    """Documentation for this module
    private - Whether module shows up in help
    set - Whether this module accepts collections
    atomic - TBD
    """
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }


def process(oid: str, opts: dict) -> Dict[str, dict]:
    """Entry point for analyzers, these do not store in database
    these are meant to be very quickly computed things passed along
    into other modules
    """
    logger.debug("process()")
    paths = api.get_field("file_meta", oid, "original_paths")
    file_path = Path(next(iter(paths)))
    rules_path = "/home/nathan/.local/share/oxide/datasets/capa-rules"
    result = {}

    result[oid] = {"filepath": file_path, "capa_capabilities": {}}
    try:
        capa_dict = run_capa(file_path, rules_path)
    except:
        capa_dict = {}
        print("error running capa")

    for capa_entry in capa_dict:
        result[oid]["capa_capabilities"][capa_entry] = []
        for match in capa_dict[capa_entry]["matches"]:
            result[oid]["capa_capabilities"][capa_entry].append(match)

    if result is None: return False

    api.store(NAME, oid, result, opts)

    return True

    paths = api.get_field("file_meta", oid, "original_paths")
    file_path = Path(next(iter(paths)))
    rules_path = "/home/nathan/.local/share/oxide/datasets/capa-rules"
    result = {}

    result[oid] = {"filepath": file_path, "capa_capabilities": {}}
    try:
        capa_dict = run_capa(file_path, rules_path)
    except:
        capa_dict = {}
        print("error running capa")

    for capa_entry in capa_dict:
        result[oid]["capa_capabilities"][capa_entry] = []
        for match in capa_dict[capa_entry]["matches"]:
            result[oid]["capa_capabilities"][capa_entry].append(match)

    if result is None: return False

    api.store(NAME, oid, result, opts)

    return True


def render_rules(doc: rd.ResultDocument):
    result = {}
    base_addr = doc.meta.analysis.base_address.value

    for rule in rutils.capability_rules(doc):
        capability = rule.meta.name

        result[capability] = {}

        ns = rule.meta.namespace
        if ns:
            result[capability]["namespace"] = ns

        desc = rule.meta.description
        if desc:
            result[capability]["description"] = desc

        if doc.meta.flavor == rd.Flavor.STATIC:
            scope = rule.meta.scopes.static
        elif doc.meta.flavor == rd.Flavor.DYNAMIC:
            scope = rule.meta.scopes.dynamic
        else:
            raise ValueError("invalid meta analysis")
        if scope:
            result[capability]["scope"] = scope.value

        lines = []
        if capa.rules.Scope.FILE not in rule.meta.scopes:
            locations = [m[0] for m in doc.rules[rule.meta.name].matches]

            if doc.meta.flavor == rd.Flavor.STATIC:
                lines = [capa.render.verbose.format_address(loc) for loc in locations]
            elif doc.meta.flavor == rd.Flavor.DYNAMIC:
                assert rule.meta.scopes.dynamic is not None
                assert isinstance(doc.meta.analysis.layout, rd.DynamicLayout)

                if rule.meta.scopes.dynamic == capa.rules.Scope.PROCESS:
                    lines = [
                        capa.render.verbose.render_process(
                            doc.meta.analysis.layout, loc
                        )
                        for loc in locations
                    ]
                elif rule.meta.scopes.dynamic == capa.rules.Scope.THREAD:
                    lines = [
                        capa.render.verbose.render_thread(doc.meta.analysis.layout, loc)
                        for loc in locations
                    ]
                elif rule.meta.scopes.dynamic == capa.rules.Scope.CALL:
                    # because we're only in verbose mode, we won't show the full call details (name, args, retval)
                    # we'll only show the details of the thread in which the calls are found.
                    # so select the thread locations and render those.
                    # because we're only in verbose mode, we won't show the full call details (name, args, retval)
                    # we'll only show the details of the thread in which the calls are found.
                    # so select the thread locations and render those.
                    thread_locations = set()
                    for loc in locations:
                        cloc = loc.to_capa()
                        assert isinstance(
                            cloc, capa.features.address.DynamicCallAddress
                        )
                        thread_locations.add(frz.Address.from_capa(cloc.thread))

                    lines = [
                        capa.render.verbose.render_thread(doc.meta.analysis.layout, loc)
                        for loc in thread_locations
                    ]
                else:
                    capa.helpers.assert_never(rule.meta.scopes.dynamic)
            else:
                capa.helpers.assert_never(doc.meta.flavor)

        result[capability]["matches"] = lines

    result = convert_addrs(result, base_addr)

    return result


def convert_addrs(results, base_addr):
    for capability in results:
        new_addrs = []
        new_addr = None
        matches = results[capability]["matches"]
        for m in matches:
            new_addr = int(m, 16) - base_addr
            new_addrs.extend([new_addr])
        results[capability]["matches"] = new_addrs
    return results


# ==== render dictionary helpers
def capa_details(rules_path: Path, file_path: Path):
    # load rules from disk
    rules = capa.rules.get_rules([rules_path])

    try:
        # extract features and find capabilities
        extractor = capa.loader.get_extractor(
            file_path,
            FORMAT_AUTO,
            OS_AUTO,
            capa.main.BACKEND_VIV,
            [],
            False,
            disable_progress=True,
        )
        capabilities, counts = capa.main.find_capabilities(
            rules, extractor, disable_progress=True
        )

        # collect metadata (used only to make rendering more complete)
        meta = capa.loader.collect_metadata(
            [], file_path, FORMAT_AUTO, OS_AUTO, [rules_path], extractor, counts
        )

        meta.analysis.feature_counts = counts["feature_counts"]
        meta.analysis.library_functions = counts["library_functions"]
        meta.analysis.layout = capa.loader.compute_layout(rules, extractor, capabilities)

        doc = rd.ResultDocument.from_capa(meta, rules, capabilities)
        capa_output = render_rules(doc)
    except:
        # extract features and find capabilities
        extractor = capa.loader.get_extractor(
            file_path,
            FORMAT_SC64,
            OS_AUTO,
            capa.main.BACKEND_VIV,
            [],
            False,
            disable_progress=True,
        )
        capabilities, counts = capa.main.find_capabilities(
            rules, extractor, disable_progress=True
        )

        # collect metadata (used only to make rendering more complete)
        meta = capa.loader.collect_metadata(
            [], file_path, FORMAT_SC64, OS_AUTO, [rules_path], extractor, counts
        )

        meta.analysis.feature_counts = counts["feature_counts"]
        meta.analysis.library_functions = counts["library_functions"]
        meta.analysis.layout = capa.loader.compute_layout(rules, extractor, capabilities)

        doc = rd.ResultDocument.from_capa(meta, rules, capabilities)
        capa_output = render_rules(doc)

        
    return capa_output



def run_capa(file, rules):
    results = capa_details(Path(rules), Path(file))
    return results
