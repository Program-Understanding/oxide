DESC = "Multi-agent (deepagents) reverse-engineering analyzer: recovers per-variable C types via a " \
       "coordinator + worker + verifier over the Oxide MCP tools, with deterministic oracle certification."
NAME = "agentic_re"

import logging
from typing import Dict, Any, List

from oxide.core import api

logger = logging.getLogger(NAME)
logger.debug("init")

opts_doc = {
    "question":        {"type": str, "mangle": True,  "default": ""},   # the NL type-recovery task (required)
    "model":           {"type": str, "mangle": True,  "default": ""},   # one model for all roles (else env/config)
    "worker_model":    {"type": str, "mangle": True,  "default": ""},   # optional per-role override
    "verifier_model":  {"type": str, "mangle": True,  "default": ""},
    "endpoint":        {"type": str, "mangle": False, "default": ""},   # OpenAI-compatible server (else env/config)
    "domain_oracles":  {"type": str, "mangle": True,
                        "default": "callee_signature,decompiler_pointer,interprocedural_param_usage,spilled_param"},
    "mcp_server_path": {"type": str, "mangle": False, "default": ""},   # path to oxide/mcp_server.py (auto if empty)
    "oxidepath":       {"type": str, "mangle": False, "default": ""},   # oxide repo root (auto if empty)
    "max_iter":        {"type": int, "mangle": False, "default": 40},
    "seed":            {"type": int, "mangle": True,  "default": 1234},
}


def documentation() -> Dict[str, Any]:
    return {"description": DESC, "opts_doc": opts_doc, "private": False, "set": False, "atomic": True}


def results(oid_list: List[str], opts: dict) -> Dict[str, dict]:
    """Run the deepagents multi-agent RE pipeline per oid; returns {oid: final_answer_string}. The
    heavy lifting lives in the core library so the module stays a thin, auto-discovered entry point."""
    from oxide.core.libraries.agentic import deepagent as D
    question = opts.get("question") or ""
    if not question:
        logger.error("agentic_re requires a 'question' opt (the type-recovery task)")
        return {}
    out: Dict[str, dict] = {}
    for oid in api.expand_oids(oid_list):
        try:
            out[oid] = D.run_sync(oid, question, opts)
        except Exception as e:  # noqa: BLE001
            logger.error("agentic_re failed on %s: %s", oid, e)
            out[oid] = f"ERROR: {e}"
    return out
