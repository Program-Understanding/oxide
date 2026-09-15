import os
from typing import Any, Dict

from oxide.modules.analyzers.delt_verification.pipeline.utils.text_utils import (
    _coerce_str,
    write_json,
    write_text,
)


def restore_cached_bounded_artifacts(stage_dir: str, cached: Dict[str, Any]) -> None:
    os.makedirs(stage_dir, exist_ok=True)
    write_text(os.path.join(stage_dir, "diff.txt"), _coerce_str(cached.get("bounded_diff_text")))
    write_json(os.path.join(stage_dir, "diff_meta.json"), cached.get("bounded_diff_meta") or {})
    final_md = _coerce_str(cached.get("bounded_final_md"))
    if final_md.strip():
        write_text(os.path.join(stage_dir, "final.md"), final_md)


def restore_cached_unbounded_artifacts(stage_dir: str, cached: Dict[str, Any]) -> None:
    os.makedirs(stage_dir, exist_ok=True)
    final_md = _coerce_str(cached.get("final_md"))
    if final_md.strip():
        write_text(os.path.join(stage_dir, "final.md"), final_md)
    write_json(os.path.join(stage_dir, "result.json"), cached)


