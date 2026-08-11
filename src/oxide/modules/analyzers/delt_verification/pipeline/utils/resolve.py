import os
from typing import Any, Dict, Iterable, Tuple

from oxide.core import api, config

from oxide.modules.analyzers.delt_verification.config import NAME
from oxide.modules.analyzers.delt_verification.pipeline.utils.text_utils import comparison_dir_name


def resolve_mcp_server_path() -> str:
    """Absolute path to oxide_mcp_server.py, the stdio server backing Verification's tools.

    Resolved by walking up from this file to the repository root rather than from
    the caller's working directory, so Verification works the same under rshell, the
    experiment plugin, and a bare python -c.
    """
    here = os.path.dirname(os.path.abspath(__file__))
    while True:
        candidate = os.path.join(here, "oxide_mcp_server.py")
        if os.path.isfile(candidate):
            return candidate
        parent = os.path.dirname(here)
        if parent == here:
            return os.path.join(os.getcwd(), "oxide_mcp_server.py")
        here = parent


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
