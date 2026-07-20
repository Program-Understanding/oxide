import json
import logging
import os
from typing import Any, Dict, List, Optional, Set, Tuple

from oxide.modules.analyzers.delt.config import NAME
from oxide.modules.analyzers.delt.pipeline.utils.text_utils import ensure_decimal_str

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


def _sample_entry_to_gt_norm(sample_key: str, entry: Dict[str, Any]) -> Optional[Dict[str, Any]]:
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

    return {
        "sample_key": sample_key,
        "targets": targets,
        "addr_set": addr_set,
        "addr_oid_set": addr_oid_set,
    }


def _sample_key_from_pair_dir(pair_dir: Optional[str]) -> Optional[str]:
    if not pair_dir:
        return None
    pair_name = os.path.basename(str(pair_dir).rstrip(os.sep))
    if not pair_name:
        return None
    if "_to_" in pair_name:
        return pair_name.split("_to_", 1)[0]
    return pair_name


def get_ground_truth_for_target(
    gt: Dict[str, Any],
    target_name: Optional[str] = None,
    *,
    pair_dir: Optional[str] = None,
    target_oid: Optional[str] = None,
) -> Optional[Dict[str, Any]]:
    if not isinstance(gt, dict):
        return None

    samples = gt.get("samples")
    if not isinstance(samples, dict):
        return None

    candidate_keys: List[str] = []
    pair_key = _sample_key_from_pair_dir(pair_dir)
    if pair_key:
        candidate_keys.append(pair_key)
    if isinstance(target_name, str) and target_name:
        candidate_keys.append(target_name)

    seen_keys: Set[str] = set()
    for key in candidate_keys:
        if key in seen_keys:
            continue
        seen_keys.add(key)
        entry = samples.get(key)
        gt_norm = _sample_entry_to_gt_norm(key, entry) if isinstance(entry, dict) else None
        if gt_norm:
            return gt_norm

    target_oid_norm = str(target_oid) if target_oid is not None else None
    if not target_oid_norm:
        return None

    oid_matches: List[Dict[str, Any]] = []
    for sample_key, entry in samples.items():
        gt_norm = _sample_entry_to_gt_norm(str(sample_key), entry) if isinstance(entry, dict) else None
        if not gt_norm:
            continue
        if any(t.get("target_oid") == target_oid_norm for t in gt_norm.get("targets", [])):
            oid_matches.append(gt_norm)

    if len(oid_matches) > 1:
        logger.warning(
            "Ground truth target_oid %s matched multiple samples; using first match %s",
            target_oid_norm,
            oid_matches[0].get("sample_key"),
        )
    return oid_matches[0] if oid_matches else None


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
