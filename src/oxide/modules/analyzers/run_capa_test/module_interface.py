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
NAME = "run_capa_test"

# imports
import logging

from typing import Dict, Any, List

from pathlib import *

from oxide.core import api

import collections
import json
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
import capa.features.freeze.features as frzf
from pathlib import *
from capa.features.common import OS_AUTO, FORMAT_AUTO

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {}


def documentation() -> Dict[str, Any]:
    """ Documentation for this module
        private - Whether module shows up in help
        set - Whether this module accepts collections
        atomic - TBD
    """
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True}


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    """ Entry point for analyzers, these do not store in database
        these are meant to be very quickly computed things passed along
        into other modules
    """
    logger.debug("process()")

    oid_list = api.expand_oids(oid_list)
    results = {}

    result = {}
    for oid in oid_list:
        paths = api.get_field("file_meta", oid, "original_paths")
        file_path = Path(next(iter(paths)))
        rules_path = "/home/nathan/.local/share/oxide/datasets/capa-rules"
        try:
            capa_dict = run_capa(file_path, rules_path)
        except:
            continue
        result[oid] = {"filepath": file_path,
                       "capa_capabilities": [],
                       "oxide_capabilities": []}
        for capa_category in capa_dict['CAPABILITY']:
            for capa_entry in capa_dict['CAPABILITY'][capa_category]:
                result[oid]["capa_capabilities"].append(capa_entry)
    return results

# == Render dictionary helpers
def render_meta(doc: rd.ResultDocument, result):
    result["md5"] = doc.meta.sample.md5
    result["sha1"] = doc.meta.sample.sha1
    result["sha256"] = doc.meta.sample.sha256
    result["path"] = doc.meta.sample.path


def find_subrule_matches(doc: rd.ResultDocument) -> Set[str]:
    """
    collect the rule names that have been matched as a subrule match.
    this way we can avoid displaying entries for things that are too specific.
    """
    matches = set()

    def rec(node: rd.Match):
        if not node.success:
            # there's probably a bug here for rules that do `not: match: ...`
            # but we don't have any examples of this yet
            return

        elif isinstance(node.node, rd.StatementNode):
            for child in node.children:
                rec(child)

        elif isinstance(node.node, rd.FeatureNode):
            if isinstance(node.node.feature, frzf.MatchFeature):
                matches.add(node.node.feature.match)

    for rule in rutils.capability_rules(doc):
        for _, node in rule.matches:
            rec(node)

    return matches


def render_capabilities(doc: rd.ResultDocument, result):
    """
    example::
        {'CAPABILITY': {'accept command line arguments': 'host-interaction/cli',
                'allocate thread local storage (2 matches)': 'host-interaction/process',
                'check for time delay via GetTickCount': 'anti-analysis/anti-debugging/debugger-detection',
                'check if process is running under wine': 'anti-analysis/anti-emulation/wine',
                'contain a resource (.rsrc) section': 'executable/pe/section/rsrc',
                'write file (3 matches)': 'host-interaction/file-system/write'}
        }
    """
    subrule_matches = find_subrule_matches(doc)

    result["CAPABILITY"] = {}
    for rule in rutils.capability_rules(doc):
        if rule.meta.name in subrule_matches:
            # rules that are also matched by other rules should not get rendered by default.
            # this cuts down on the amount of output while giving approx the same detail.
            # see #224
            continue

        count = len(rule.matches)
        if count == 1:
            capability = rule.meta.name
        else:
            capability = f"{rule.meta.name} ({count} matches)"

        result["CAPABILITY"].setdefault(rule.meta.namespace, [])
        result["CAPABILITY"][rule.meta.namespace].append(capability)


def render_attack(doc, result):
    """
    example::
        {'ATT&CK': {'COLLECTION': ['Input Capture::Keylogging [T1056.001]'],
            'DEFENSE EVASION': ['Obfuscated Files or Information [T1027]',
                                'Virtualization/Sandbox Evasion::System Checks '
                                '[T1497.001]'],
            'DISCOVERY': ['File and Directory Discovery [T1083]',
                          'Query Registry [T1012]',
                          'System Information Discovery [T1082]'],
            'EXECUTION': ['Shared Modules [T1129]']}
        }
    """
    result["ATTCK"] = {}
    tactics = collections.defaultdict(set)
    for rule in rutils.capability_rules(doc):
        if not rule.meta.attack:
            continue
        for attack in rule.meta.attack:
            tactics[attack.tactic].add((attack.technique, attack.subtechnique, attack.id))

    for tactic, techniques in sorted(tactics.items()):
        inner_rows = []
        for technique, subtechnique, id in sorted(techniques):
            if subtechnique is None:
                inner_rows.append(f"{technique} {id}")
            else:
                inner_rows.append(f"{technique}::{subtechnique} {id}")
        result["ATTCK"].setdefault(tactic.upper(), inner_rows)


def render_mbc(doc, result):
    """
    example::
        {'MBC': {'ANTI-BEHAVIORAL ANALYSIS': ['Debugger Detection::Timing/Delay Check '
                                      'GetTickCount [B0001.032]',
                                      'Emulator Detection [B0004]',
                                      'Virtual Machine Detection::Instruction '
                                      'Testing [B0009.029]',
                                      'Virtual Machine Detection [B0009]'],
         'COLLECTION': ['Keylogging::Polling [F0002.002]'],
         'CRYPTOGRAPHY': ['Encrypt Data::RC4 [C0027.009]',
                          'Generate Pseudo-random Sequence::RC4 PRGA '
                          '[C0021.004]']}
        }
    """
    result["MBC"] = {}
    objectives = collections.defaultdict(set)
    for rule in rutils.capability_rules(doc):
        if not rule.meta.mbc:
            continue

        for mbc in rule.meta.mbc:
            objectives[mbc.objective].add((mbc.behavior, mbc.method, mbc.id))

    for objective, behaviors in sorted(objectives.items()):
        inner_rows = []
        for behavior, method, id in sorted(behaviors):
            if method is None:
                inner_rows.append(f"{behavior} [{id}]")
            else:
                inner_rows.append(f"{behavior}::{method} [{id}]")
        result["MBC"].setdefault(objective.upper(), inner_rows)


def render_dictionary(doc: rd.ResultDocument) -> Dict[str, Any]:
    result: Dict[str, Any] = {}
    render_meta(doc, result)
    render_attack(doc, result)
    render_mbc(doc, result)
    render_capabilities(doc, result)

    return result


# ==== render dictionary helpers
def capa_details(rules_path: Path, file_path: Path, output_format="dictionary"):
    # load rules from disk
    rules = capa.main.get_rules([rules_path])

    # extract features and find capabilities
    extractor = capa.main.get_extractor(
        file_path, FORMAT_AUTO, OS_AUTO, capa.main.BACKEND_VIV, [], False, disable_progress=True
    )
    capabilities, counts = capa.main.find_capabilities(rules, extractor, disable_progress=True)

    # collect metadata (used only to make rendering more complete)
    meta = capa.main.collect_metadata([], file_path, FORMAT_AUTO, OS_AUTO, [rules_path], extractor)

    meta.analysis.feature_counts = counts["feature_counts"]
    meta.analysis.library_functions = counts["library_functions"]
    meta.analysis.layout = capa.main.compute_layout(rules, extractor, capabilities)

    capa_output: Any = False

    if output_format == "dictionary":
        # ...as python dictionary, simplified as textable but in dictionary
        doc = rd.ResultDocument.from_capa(meta, rules, capabilities)
        capa_output = render_dictionary(doc)
    elif output_format == "json":
        # render results
        # ...as json
        capa_output = json.loads(capa.render.json.render(meta, rules, capabilities))
    elif output_format == "texttable":
        # ...as human readable text table
        capa_output = capa.render.default.render(meta, rules, capabilities)

    return capa_output


def run_capa(file, rules):
    results = capa_details(Path(rules), Path(file))
    return results
