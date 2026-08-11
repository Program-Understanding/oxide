import os
from functools import lru_cache
from typing import Dict

try:
    import yaml
except ImportError as exc:  # pragma: no cover
    yaml = None
    _yaml_import_error = exc
else:
    _yaml_import_error = None


def _prompt_dir() -> str:
    # prompts/ lives at pipeline/prompts/, alongside utils/ under pipeline/.
    pipeline_root = os.path.dirname(os.path.dirname(__file__))
    return os.path.join(pipeline_root, "prompts")


def load_prompt_file(filename: str) -> Dict:
    if yaml is None:  # pragma: no cover
        raise RuntimeError(f"PyYAML is required to load prompt file {filename}: {_yaml_import_error}")

    path = os.path.join(_prompt_dir(), filename)
    with open(path, "r", encoding="utf-8") as handle:
        data = yaml.safe_load(handle) or {}

    if not isinstance(data, dict):
        raise ValueError(f"Prompt file {path} must load to a mapping.")
    if not data.get("system"):
        raise ValueError(f"Prompt file {path} is missing required field 'system'.")
    return data


@lru_cache(maxsize=None)
def _load_prompt_bundle_cached(
    triage_file: str, triage_with_callees_file: str, binary_context_file: str, verification_file: str
) -> Dict[str, Dict]:
    return {
        "triage": load_prompt_file(triage_file),
        "triage_with_callees": load_prompt_file(triage_with_callees_file),
        "binary_context": load_prompt_file(binary_context_file),
        "verification": load_prompt_file(verification_file),
    }


def load_prompt_bundle(opts: Dict | None = None) -> Dict[str, Dict]:
    resolved_opts = dict(opts or {})
    triage_file = str(resolved_opts.get("triage_prompt_file") or "triage.yaml")
    triage_with_callees_file = str(
        resolved_opts.get("triage_with_callees_prompt_file") or "triage_with_callees.yaml"
    )
    binary_context_file = str(
        resolved_opts.get("binary_context_prompt_file") or "binary_context.yaml"
    )
    verification_file = str(
        resolved_opts.get("verification_prompt_file") or "verification_agent.yaml"
    )
    return _load_prompt_bundle_cached(
        triage_file, triage_with_callees_file, binary_context_file, verification_file
    )
