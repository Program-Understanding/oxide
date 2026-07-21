DESC = "Structured collection comparison analyzer extracted from the drift prototype."

import logging

from typing import Any, Dict, List

from oxide.modules.analyzers.drift.constants import NAME
from oxide.modules.analyzers.drift.filters import get_filter_rules, normalize_filter_name
from oxide.modules.analyzers.drift.raw_comparison import build_raw_comparison, resolve_collection_pair
from oxide.modules.analyzers.drift.summary import summarize_file_classifications, summarize_function_classifications

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {
    "view": {"type": str, "mangle": True, "default": ""},
    "filter": {"type": str, "mangle": True, "default": ""},
}


def documentation() -> Dict[str, Any]:
    """ Documentation for this module
        private - Whether module shows up in help
        set - Whether this module accepts collections
        atomic - TBD
    """
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False,
            "atomic": True}


def results(oid_list: List[str], opts: dict) -> Dict[str, Any]:
    """ Compare two collections, returning file and function classifications.
        oid_list must be [target_oid, baseline_oid].
    """
    logger.debug("process()")

    target_oid, baseline_oid = resolve_collection_pair(list(oid_list))
    raw = build_raw_comparison(target_oid, baseline_oid)

    filter_name = normalize_filter_name(opts.get("filter"))
    filter_rules = get_filter_rules(filter_name)

    file_classification = summarize_file_classifications(raw["PAIR_FILES_RESULTS"])
    per_file_fc, total_fc = summarize_function_classifications(
        raw["FUNCTION_DIFFS"],
        filter_rules=filter_rules,
        filter_name=filter_name,
    )

    output = {
        **raw,
        "FILE_CLASSIFICATIONS": file_classification,
        "FUNCTION_CLASSIFICATION": {
            "PER_FILE": per_file_fc,
            "TOTAL": total_fc,
        },
    }

    view = opts.get("view")
    if view:
        return output.get(view, {})
    return output
