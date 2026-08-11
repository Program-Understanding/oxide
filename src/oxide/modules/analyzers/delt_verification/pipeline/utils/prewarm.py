"""Build the expensive MCP-backed artifacts before the agents can ask for them.

Two of the tools the Verification agents call are bimodal: instant on a cache hit, minutes on
a miss, because a miss runs Ghidra or BinDiff inside the agent's run budget.
``get_control_flow_graph`` retrieves ``mcp_control_flow_graph`` for one binary, and
``get_matched_function`` retrieves ``function_mapping`` for one ordered binary pair. A
cold call to either has been measured stalling past 400s, which is the whole budget.

Nothing here changes an agent's answer -- it only moves the cost outside the budget, so
it runs unconditionally and a failure is logged rather than raised: a binary whose CFG
cannot be built should still be investigated with the rest of the tool surface.
"""

import logging
import time
from typing import Any, Dict, List, Optional, Tuple

from oxide.core import api

from oxide.modules.analyzers.delt_verification.config import NAME
from oxide.modules.analyzers.delt_verification.pipeline.utils.text_utils import _coerce_str

logger = logging.getLogger(NAME)


def _prewarm_control_flow_graphs(oids: List[str]) -> List[Dict[str, Any]]:
    """ Back get_control_flow_graph. Per binary, and process() rather than retrieve() so a
        whole binary's CFGs are built and stored without materializing them here.
    """
    out = []
    for oid in oids:
        t0 = time.perf_counter()
        try:
            ok = bool(api.process("mcp_control_flow_graph", [oid]))
            err = None
        except Exception as exc:  # noqa: BLE001
            ok, err = False, repr(exc)
        out.append({
            "artifact": "mcp_control_flow_graph",
            "oid": oid,
            "ok": ok,
            "elapsed_s": time.perf_counter() - t0,
            "error": err,
        })
    return out


def _prewarm_function_mappings(pairs: List[Tuple[str, str]]) -> List[Dict[str, Any]]:
    """ Back get_matched_function. The mapping is directional and the tool tries the
        reverse direction when the direct one misses, so both orderings are warmed.
    """
    out = []
    for target_oid, baseline_oid in pairs:
        t0 = time.perf_counter()
        try:
            # An analyzer that stores its own result, so retrieve is what populates it.
            ok = api.retrieve("function_mapping", [target_oid, baseline_oid]) is not None
            err = None
        except Exception as exc:  # noqa: BLE001
            ok, err = False, repr(exc)
        out.append({
            "artifact": "function_mapping",
            "oid": target_oid,
            "baseline_oid": baseline_oid,
            "ok": ok,
            "elapsed_s": time.perf_counter() - t0,
            "error": err,
        })
    return out


def prewarm_filepair_artifacts(
    *, baseline_oid: Any, target_oid: Any, label: Optional[str] = None
) -> Dict[str, Any]:
    """ Build both agents' cold-miss artifacts for one file pair.

        Returns a summary suitable for writing beside the pair's other stage artifacts:
        {"elapsed_s", "warmed", "failed", "items"}.
    """
    baseline = _coerce_str(baseline_oid)
    target = _coerce_str(target_oid)

    # The binary-context agent is scoped to the baseline; the verification agent addresses
    # both sides of the pair.
    oids = [o for o in dict.fromkeys([baseline, target]) if o]
    pairs = [(t, b) for t, b in ((target, baseline), (baseline, target)) if t and b and t != b]

    t0 = time.perf_counter()
    items = _prewarm_control_flow_graphs(oids) + _prewarm_function_mappings(pairs)
    elapsed = time.perf_counter() - t0

    failed = [i for i in items if not i["ok"]]
    summary = {
        "elapsed_s": elapsed,
        "warmed": len(items) - len(failed),
        "failed": len(failed),
        "items": items,
    }
    where = f" [{label}]" if label else ""
    logger.info(
        "prewarm%s: %d/%d artifacts in %.1fs", where, summary["warmed"], len(items), elapsed
    )
    for item in failed:
        logger.warning(
            "prewarm%s: %s failed for %s: %s",
            where, item["artifact"], item["oid"], item["error"] or "no result",
        )
    return summary
