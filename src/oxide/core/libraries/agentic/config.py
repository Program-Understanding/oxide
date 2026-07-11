"""Config resolution for the native Oxide agentic RE feature.

Extracted from ``llm.py`` so the tool layer (``tools/registry.py``) and the deepagents driver can
resolve settings without importing the (retired) custom litellm loop. Nothing here depends on
litellm — only ``os`` and, lazily, Oxide's config file.

Resolution order for every setting: opts -> environment (AGENTIC_<KEY>) -> the [agentic] section of
~/.config/oxide/.config.txt. There are NO built-in default values for REQUIRED settings — a missing
one raises a clear error telling you what to add, rather than silently guessing.
"""
from __future__ import annotations

import os


def _seed() -> int:
    """Sampling seed sent to the server (greedy+seed => deterministic replays). Override with
    AGENTIC_SEED to draw independent trajectories for variance measurement; default 1234."""
    try:
        return int(os.environ.get("AGENTIC_SEED", "1234"))
    except (ValueError, TypeError):
        return 1234


# module-level accumulator, kept for compatibility with callers that read token usage
USAGE = {"prompt": 0, "completion": 0, "calls": 0}


def _from_oxide_config(key: str):
    """Read an `[agentic]` key from Oxide's config file (~/.config/oxide/.config.txt), if present.
    Uses the raw config parser directly — the typed `get_value` only knows sections REGISTERED in
    Oxide's defaults, and `[agentic]` is a user-added one — so a missing section/key returns None
    and the caller falls through to env/defaults."""
    try:
        from oxide.core import config as _cfg  # type: ignore
        return _cfg.rcp.get("agentic", key)
    except Exception:  # noqa: BLE001  # NoSection/NoOption/etc. -> simply not configured
        return None


def _opt(opts, key):
    # treat "" like absent: Oxide fills module opts with the opts_doc default (often "") which would
    # otherwise SHADOW the env/config fallbacks, so fall through on empty strings too.
    v = opts.get(key)
    if v in (None, ""):
        v = os.environ.get(f"AGENTIC_{key.upper()}")
    if v in (None, ""):
        v = _from_oxide_config(key)
    return v if v not in (None, "") else None


def cfg_get(key: str, default=None):
    """Resolve a module-level agentic tunable: env AGENTIC_<KEY> -> [agentic] config <key> ->
    default. Same precedence as _opt but with no opts dict — so the tuning knobs (max_tokens,
    nothink, timeouts, caps) can all live in ~/.config/oxide/.config.txt, not just env."""
    v = os.environ.get(f"AGENTIC_{key.upper()}")
    if v in (None, ""):
        v = _from_oxide_config(key)
    return v if v not in (None, "") else default


def cfg_int(key: str, default: int) -> int:
    """An OPTIONAL integer knob whose default is supplied by the caller (e.g. a per-run cap)."""
    try:
        return int(cfg_get(key) or default)
    except (ValueError, TypeError):
        return default


def cfg_bool(key: str) -> bool:
    return str(cfg_get(key, "")).strip().lower() in ("1", "true", "yes", "on")


def _missing(key: str):
    raise RuntimeError(
        f"agentic: required setting '{key}' is not configured. Add it under [agentic] in "
        f"~/.config/oxide/.config.txt (or set env AGENTIC_{key.split(' ')[0].upper()}).")


def cfg_required(key: str) -> str:
    """A REQUIRED setting (env AGENTIC_<KEY> or [agentic] config <key>) — raises a clear error if
    absent. Used for the LLM connection + sizing knobs, which have no safe built-in default."""
    v = cfg_get(key)
    if v is None:
        _missing(key)
    return v


def resolve_config(opts: dict | None = None) -> dict:
    """Build the effective LLM config from opts -> env -> [agentic] config. No built-in defaults:
    a required setting absent from all three raises a clear error.

    The LLM is always reached as an OpenAI-compatible server at `endpoint`. Convenience: `model`
    sets ALL roles (planner/worker/verifier) at once; otherwise each *_model must be configured."""
    opts = opts or {}
    endpoint = _opt(opts, "endpoint") or _missing("endpoint")
    cfg = {"endpoint": endpoint}
    one = _opt(opts, "model")                 # one model for every role (convenience)
    for role in ("planner_model", "worker_model", "verifier_model"):
        v = one or _opt(opts, role)
        if v is None:
            _missing(f"{role} (or 'model')")
        cfg[role] = v
    return cfg


# --- sizing knobs (required; no safe default) -----------------------------------------------------
def ctx_chars() -> int:
    """Total input-context budget in CHARS (~4 chars/token). REQUIRED via AGENTIC_CTX_CHARS."""
    return int(cfg_required("ctx_chars"))


def req_timeout() -> float:
    """Per-request timeout in seconds. REQUIRED via AGENTIC_REQ_TIMEOUT."""
    return float(cfg_required("req_timeout"))


def max_tokens() -> int:
    """Max OUTPUT tokens per completion. REQUIRED via AGENTIC_MAX_TOKENS."""
    return int(cfg_required("max_tokens"))


def out_cap() -> int:
    """Per-tool-output char cap. REQUIRED via AGENTIC_OUT_CAP / [agentic] out_cap; 0 = unlimited."""
    return int(cfg_required("out_cap"))
