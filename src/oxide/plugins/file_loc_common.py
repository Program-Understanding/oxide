from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence

from oxide.core import api


DEFAULT_COMP_PATH = "fuse-dataset/openwrt-dataset/fuse_ground_truth.json"
DEFAULT_PROMPT_PATH = "fuse-dataset/descriptions/component_descriptions.json"
DEFAULT_VARIANTS_PATH = "fuse-dataset/descriptions/variant-descriptions.json"


def write_json_artifact(outdir: str, filename: str, payload: Dict[str, Any]) -> Optional[str]:
    outdir = str(outdir or "").strip()
    if not outdir:
        return None
    target_dir = Path(outdir).expanduser()
    target_dir.mkdir(parents=True, exist_ok=True)
    target = target_dir / filename
    target.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    return str(target)


def load_json_object(path: str | Path) -> Dict[str, Any]:
    src = Path(path).expanduser()
    try:
        obj = json.loads(src.read_text(encoding="utf-8"))
    except Exception as err:
        raise ValueError(f"failed to parse JSON '{src}': {err}") from err
    if not isinstance(obj, dict):
        raise ValueError(f"JSON root is not an object: {src}")
    return obj


def parse_csv_set(value: Any) -> List[str]:
    if value is None:
        return []
    if isinstance(value, (list, tuple, set)):
        items = [str(x).strip() for x in value if str(x).strip()]
    else:
        items = [x.strip() for x in str(value).split(",") if x.strip()]
    return list(dict.fromkeys(items))


def filter_executables(oids: Sequence[str]) -> List[str]:
    out: List[str] = []
    for oid in oids:
        cat = api.get_field("categorize", oid, oid)
        if cat != "executable":
            continue
        names = list(api.get_names_from_oid(oid))
        if any((".so" in n) or (".ko" in n) for n in names):
            continue
        out.append(str(oid))
    return out


def _build_ground_truth_for_collection(exes: Sequence[str], basename_map: Dict[str, List[str]]) -> Dict[str, str]:
    base_to_oid: Dict[str, str] = {}
    for oid in exes:
        for name in api.get_names_from_oid(oid):
            base = Path(str(name)).name.strip()
            if base and base not in base_to_oid:
                base_to_oid[base] = str(oid)

    col_gt: Dict[str, str] = {}
    for component, basenames in basename_map.items():
        for base in basenames:
            oid = base_to_oid.get(base)
            if oid:
                col_gt[component] = oid
                break
    return col_gt


def create_ground_truth(comp_path: str) -> Dict[str, Dict[str, str]]:
    data = json.loads(Path(comp_path).read_text(encoding="utf-8"))
    out: Dict[str, Dict[str, str]] = {}

    for cid in api.collection_cids() or []:
        colname = api.get_colname_from_oid(cid)
        if colname not in data:
            continue
        raw = data[colname]
        if not isinstance(raw, dict):
            continue

        basename_map: Dict[str, List[str]] = {}
        for component, paths in raw.items():
            if not isinstance(component, str):
                continue
            vals = paths if isinstance(paths, list) else [paths]
            ordered: List[str] = []
            seen = set()
            for path in vals:
                base = Path(str(path)).name.strip()
                if not base or base in seen:
                    continue
                seen.add(base)
                ordered.append(base)
            if ordered:
                basename_map[component] = ordered

        exes = filter_executables(list(api.expand_oids(cid) or []))
        gt_col = _build_ground_truth_for_collection(exes, basename_map)
        if gt_col:
            out[str(cid)] = gt_col

    return out


def load_prompt_map(prompt_path: str) -> Dict[str, Any]:
    raw = json.loads(Path(prompt_path).read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        return {}
    out: Dict[str, Any] = {}
    for key, value in raw.items():
        if not isinstance(key, str):
            continue
        if isinstance(value, str) and value.strip():
            out[key] = value.strip()
        elif isinstance(value, list):
            prompts = [str(p).strip() for p in value if isinstance(p, str) and str(p).strip()]
            if prompts:
                out[key] = prompts
    return out


def build_eval_tasks(ground_truth: Dict[str, Dict[str, str]], prompt_map: Dict[str, Any]) -> List[Dict[str, Any]]:
    tasks: List[Dict[str, Any]] = []
    for cid in sorted(ground_truth.keys(), key=lambda c: str(api.get_colname_from_oid(c) or c)):
        colname = api.get_colname_from_oid(cid)
        for component, gold_oid in sorted(ground_truth[cid].items(), key=lambda kv: kv[0]):
            prompt_val = prompt_map.get(component)
            if not prompt_val:
                continue
            prompts: List[str] = prompt_val if isinstance(prompt_val, list) else [str(prompt_val)]
            for idx, prompt in enumerate(prompts):
                variant_suffix = f":v{idx}" if isinstance(prompt_val, list) else ""
                tasks.append(
                    {
                        "task_id": f"{cid}:{component}{variant_suffix}",
                        "cid": str(cid),
                        "collection": str(colname or cid),
                        "component": component,
                        "prompt": prompt,
                        "gold_oid": str(gold_oid),
                    }
                )
    return tasks


def apply_task_filters(
    tasks: Sequence[Dict[str, Any]],
    *,
    components: Sequence[str],
    collections: Sequence[str],
) -> List[Dict[str, Any]]:
    comp_set = {str(x).strip().lower() for x in components if str(x).strip()}
    col_set = {str(x).strip().lower() for x in collections if str(x).strip()}
    if not comp_set and not col_set:
        return list(tasks)

    out: List[Dict[str, Any]] = []
    for task in tasks:
        comp = str(task.get("component") or "").strip().lower()
        col = str(task.get("collection") or "").strip().lower()
        if comp_set and comp not in comp_set:
            continue
        if col_set and col not in col_set:
            continue
        out.append(task)
    return out
