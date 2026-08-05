from typing import Any, Dict, List

from oxide.core import api
from oxide.modules.analyzers.query_function import clap, search_functions
from oxide.modules.analyzers.query_function.common import expand_oids_best_effort
from oxide.modules.analyzers.query_function.config import DESC, NAME

opts_doc = {
    "query": {"type": str, "mangle": True, "default": ""},
    "query_path": {"type": str, "mangle": True, "default": ""},
    "prompts": {"type": str, "mangle": True, "default": ""},
    "prompts_path": {"type": str, "mangle": True, "default": ""},
    "backend": {"type": str, "mangle": True, "default": "search_functions"},
    "top_k": {"type": int, "mangle": False, "default": 10},
    "limit": {"type": int, "mangle": False, "default": 0},
    "offset": {"type": int, "mangle": False, "default": 0},
    "search_mode": {"type": str, "mangle": False, "default": "semantic"},
    "include_full_code": {"type": bool, "mangle": False, "default": True},
    "preview_length": {"type": int, "mangle": False, "default": 500},
    "similarity_threshold": {"type": float, "mangle": False, "default": 0.0},
    "max_chars": {"type": int, "mangle": True, "default": 20000},
    "max_instructions": {"type": int, "mangle": True, "default": 512},
    "batch_size": {"type": int, "mangle": False, "default": 64},
    "use_cache": {"type": bool, "mangle": False, "default": True},
    "rebuild": {"type": bool, "mangle": False, "default": False},
    "model_id": {"type": str, "mangle": True, "default": "sentence-transformers/all-MiniLM-L6-v2"},
    "asm_model_id": {"type": str, "mangle": True, "default": "hustcw/clap-asm"},
    "text_model_id": {"type": str, "mangle": True, "default": "hustcw/clap-text"},
    "device": {"type": str, "mangle": False, "default": "auto"},
    "temperature": {"type": float, "mangle": False, "default": 0.07},
    "normalize_embeddings": {"type": bool, "mangle": True, "default": False},
    "timing": {"type": bool, "mangle": False, "default": True},
    "timing_topn": {"type": int, "mangle": False, "default": 5},
    "progress": {"type": bool, "mangle": False, "default": True},
    "progress_every": {"type": int, "mangle": False, "default": 50},
    "return_file_embeddings": {"type": bool, "mangle": False, "default": False},
    "file_agg": {"type": str, "mangle": False, "default": "attn"},
    "attn_tau": {"type": float, "mangle": False, "default": 0.07},
}

BACKENDS = {
    "search_functions": search_functions,
    "clap": clap,
}


def documentation() -> Dict[str, Any]:
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
    }


def results(oid_list: List[str], opts: dict) -> Dict[str, Any]:
    backend = (opts.get("backend") or "search_functions").strip().lower()
    if backend not in BACKENDS:
        return {
            "error": f"Unsupported backend: {backend}",
            "supported_backends": sorted(BACKENDS),
        }
    return BACKENDS[backend].results(expand_oids_best_effort(oid_list), opts)
