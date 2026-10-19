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
    bounded_file: str,
    bounded_with_callees_file: str,
    unbounded_file: str,
    unbounded_no_report_file: str,
) -> Dict[str, Dict]:
    return {
        "bounded": load_prompt_file(bounded_file),
        "bounded_with_callees": load_prompt_file(bounded_with_callees_file),
        "unbounded": load_prompt_file(unbounded_file),
        "unbounded_no_report": load_prompt_file(unbounded_no_report_file),
    }


def load_prompt_bundle(opts: Dict | None = None) -> Dict[str, Dict]:
    resolved_opts = dict(opts or {})
    return _load_prompt_bundle_cached(
        str(resolved_opts.get("bounded_prompt_file") or "bounded.yaml"),
        str(
            resolved_opts.get("bounded_with_callees_prompt_file")
            or "bounded_with_callees.yaml"
        ),
        str(resolved_opts.get("unbounded_prompt_file") or "unbounded_agent.yaml"),
        str(
            resolved_opts.get("unbounded_no_report_prompt_file")
            or "unbounded_no_report.yaml"
        ),
    )
