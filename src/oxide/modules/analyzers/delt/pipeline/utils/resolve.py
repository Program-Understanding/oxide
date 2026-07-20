import os
from typing import Any, Dict, Iterable, Tuple

from oxide.core import api, config

from oxide.modules.analyzers.delt.config import NAME
from oxide.modules.analyzers.delt.pipeline.utils.text_utils import comparison_dir_name


def resolve_collection_pair(oid_list: Iterable[str]) -> Tuple[str, str]:
    pair = list(oid_list)
    if len(pair) < 2:
        raise ValueError("delt requires two collection OIDs: [target_oid, baseline_oid]")

    valid, invalid = api.valid_oids(pair[:2])
    if len(valid) < 2:
        raise ValueError(f"Invalid collections: {invalid}")
    return valid[0], valid[1]


def resolve_artifact_root(target: str, baseline: str, opts: Dict[str, Any]) -> str:
    """ If opts["outdir"] is given, use it as-is. Otherwise derive a persistent
        (never auto-deleted) default root under config.dir_scratch, namespaced by
        analyzer + comparison, so calls without an explicit outdir still keep
        their human-readable artifacts and get real caching benefit across calls
        instead of using a tempdir that's deleted after every invocation.
    """
    outdir = str(opts.get("outdir") or "").strip()
    if outdir:
        return outdir

    target_name = api.get_colname_from_oid(target) or target
    baseline_name = api.get_colname_from_oid(baseline) or baseline
    return os.path.join(config.dir_scratch, NAME, comparison_dir_name(str(target_name), str(baseline_name)))
