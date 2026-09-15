import os
from typing import Any, Dict, List

from oxide.modules.analyzers.delt_verification.pipeline.utils.text_utils import (
    write_json,
)


def write_comparison_outputs(
    *,
    outdir: str,
    per_function_results: List[Dict[str, Any]],
    unbounded_results: List[Dict[str, Any]],
    stage_metrics: Dict[str, Any],
    stats: Dict[str, Any],
) -> None:
    write_json(os.path.join(outdir, "per_function_results.json"), per_function_results)
    write_json(os.path.join(outdir, "unbounded_results.json"), unbounded_results)
    write_json(os.path.join(outdir, "stage_metrics.json"), stage_metrics)
    write_json(os.path.join(outdir, "stats.json"), stats)


def build_analyzer_result(
    *,
    target: str,
    baseline: str,
    stats: Dict[str, Any],
    stage_metrics: Dict[str, Any],
    per_function_results: List[Dict[str, Any]],
    unbounded_results: List[Dict[str, Any]],
    file_pairs: List[Dict[str, Any]],
) -> Dict[str, Any]:
    return {
        "target": target,
        "baseline": baseline,
        "stats": stats,
        "stage_metrics": stage_metrics,
        "per_function_results": per_function_results,
        "unbounded_results": unbounded_results,
        "file_pairs": file_pairs,
    }
