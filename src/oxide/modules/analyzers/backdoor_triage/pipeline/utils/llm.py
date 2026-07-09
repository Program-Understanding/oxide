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
    stage1_file: str,
    stage2_file: str,
    stage2_callee_file: str,
    stage3_file: str,
) -> Dict[str, Dict]:
    return {
        "stage1": load_prompt_file(stage1_file),
        "stage2": load_prompt_file(stage2_file),
        "stage2_callee": load_prompt_file(stage2_callee_file),
        "stage3": load_prompt_file(stage3_file),
    }


def load_prompt_bundle(opts: Dict | None = None) -> Dict[str, Dict]:
    resolved_opts = dict(opts or {})
    stage1_file = str(resolved_opts.get("stage1_prompt_file") or "stage1.yaml")
    stage2_file = str(resolved_opts.get("stage2_prompt_file") or "stage2.yaml")
    stage2_callee_file = str(
        resolved_opts.get("stage2_callee_prompt_file") or "stage2_with_callees.yaml"
    )
    stage3_file = str(resolved_opts.get("stage3_prompt_file") or "stage3.yaml")
    return _load_prompt_bundle_cached(stage1_file, stage2_file, stage2_callee_file, stage3_file)
