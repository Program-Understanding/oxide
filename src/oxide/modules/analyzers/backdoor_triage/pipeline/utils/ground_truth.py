import json
import logging
from typing import Any, Dict, List, Optional, Set, Tuple

from oxide.modules.analyzers.backdoor_triage.config import NAME
from oxide.modules.analyzers.backdoor_triage.pipeline.utils.text_utils import ensure_decimal_str

logger = logging.getLogger(NAME)


def load_ground_truth_file(path: Optional[str]) -> Dict[str, Any]:
    if not path:
        return {}
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception as exc:
        logger.error("Failed to load ground truth file '%s': %s", path, exc)
        return {}


def get_ground_truth_for_target(gt: Dict[str, Any], target_name: str) -> Optional[Dict[str, Any]]:
    if not isinstance(gt, dict) or not target_name:
        return None

    samples = gt.get("samples")
    if not isinstance(samples, dict):
        return None

    entry = samples.get(target_name)
    if not isinstance(entry, dict):
        return None

    backdoor = entry.get("backdoor")
    if not isinstance(backdoor, dict):
        return None

    targets_raw = backdoor.get("targets")
    if not isinstance(targets_raw, list) or not targets_raw:
        return None

    targets: List[Dict[str, Any]] = []
    addr_set: Set[str] = set()
    addr_oid_set: Set[Tuple[str, Optional[str]]] = set()

    for target in targets_raw:
        if not isinstance(target, dict):
            continue
        addr = target.get("target_addr")
        if addr is None:
            continue

        addr_norm = ensure_decimal_str(addr)
        oid = target.get("target_oid", None)
        oid_norm = str(oid) if oid is not None else None

        targets.append({"target_addr": addr_norm, "target_oid": oid_norm})
        addr_set.add(addr_norm)
        addr_oid_set.add((addr_norm, oid_norm))

    if not targets:
        return None

    return {"targets": targets, "addr_set": addr_set, "addr_oid_set": addr_oid_set}


def gt_row_matches_any(row: Dict[str, Any], gt_norm: Dict[str, Any]) -> bool:
    if not gt_norm:
        return False

    row_addr = ensure_decimal_str(row.get("target_addr"))
    if row_addr not in gt_norm["addr_set"]:
        return False

    row_oid = row.get("target_oid", None)
    row_oid_norm = str(row_oid) if row_oid is not None else None

    if (row_addr, row_oid_norm) in gt_norm["addr_oid_set"]:
        return True
    if (row_addr, None) in gt_norm["addr_oid_set"]:
        return True
    return False
