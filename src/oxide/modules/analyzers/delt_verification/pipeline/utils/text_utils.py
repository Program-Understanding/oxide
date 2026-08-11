import json
import unicodedata
from typing import Any, Dict, Optional

_ASCII_MAP = {
    ord("–"): "-",
    ord("—"): "-",
    ord("…"): "...",
    ord("“"): '"',
    ord("”"): '"',
    ord("‘"): "'",
    ord("’"): "'",
    ord(" "): 32,
    ord(" "): 32,
}

_EMPTY_DECOMP_FAILURE_MESSAGES: Dict[str, Dict[str, str]] = {
    "empty_baseline_decomp": {
        "observation": "baseline decompilation was empty. Triage skipped and recorded as failed.",
        "final_why": "The baseline decompilation was empty, so the system could not compute a two-sided function diff. The function was recorded as failed because triage did not run, not because the agent identified a trigger.",
    },
    "empty_target_decomp": {
        "observation": "target decompilation was empty. Triage skipped and recorded as failed.",
        "final_why": "The target decompilation was empty, so the system could not compute a two-sided function diff. The function was recorded as failed because triage did not run, not because the agent identified a trigger.",
    },
    "empty_both_decomp": {
        "observation": "baseline and target decompilations were empty. Triage skipped and recorded as failed.",
        "final_why": "Both baseline and target decompilations were empty, so the system could not compute a two-sided function diff. The function was recorded as failed because triage did not run, not because the agent identified a trigger.",
    },
}


def ascii_sanitize(text: str) -> str:
    return unicodedata.normalize("NFKC", text).translate(_ASCII_MAP)


def _coerce_str(value: Any) -> str:
    if value is None:
        return ""
    try:
        return str(value).strip()
    except Exception:
        return ""


def _coerce_label(value: Any) -> str:
    return _coerce_str(value).lower().replace("-", "_")


def _coerce_result_label(label: Any, failure_reason: Any = None) -> str:
    failure_reason_str = _coerce_str(failure_reason)
    if failure_reason_str and failure_reason_str in _EMPTY_DECOMP_FAILURE_MESSAGES:
        return "skipped"
    if failure_reason_str:
        return "failed"
    label_norm = _coerce_label(label)
    if label_norm == "error":
        return "failed"
    if label_norm in {"safe", "not_safe", "failed"}:
        return label_norm
    return "failed"


def ensure_decimal_str(addr: Any) -> Optional[str]:
    """ Normalize an address to a decimal string. Accepts hex ("0x10"), octal, or
        binary-prefixed input as well as plain decimal; returns None for missing
        or empty input.
    """
    if addr is None:
        return None
    text = str(addr).strip()
    if not text:
        return None
    try:
        return str(int(text, 0))
    except Exception:
        return text


def _extract_first_balanced_json_object(text: str) -> Optional[dict]:
    start = text.find("{")
    if start == -1:
        return None
    depth = 0
    for index in range(start, len(text)):
        char = text[index]
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                blob = text[start : index + 1]
                try:
                    return json.loads(blob)
                except Exception:
                    return None
    return None


def parse_llm_json(text: str) -> Any:
    text = text.strip()
    for fence in ("```json", "```"):
        if text.startswith(fence):
            text = text[len(fence):].lstrip()
            if text.endswith("```"):
                text = text[:-3].rstrip()
    try:
        return json.loads(text)
    except Exception:
        return _extract_first_balanced_json_object(text)


def coerce_json_like(value: Any) -> Optional[dict]:
    if isinstance(value, dict):
        return value
    if isinstance(value, str):
        try:
            return json.loads(value)
        except Exception:
            return _extract_first_balanced_json_object(value)
    return None


def normalize_filter_value(value: Any) -> Optional[str]:
    """ Map "and"/"or" shorthand to the drift analyzer's actual filter card names. """
    if value is None:
        return None

    value_str = _coerce_str(value)
    if not value_str:
        return None
    value_lower = value_str.lower()
    if value_lower in {"none", "null"}:
        return None
    if value_lower == "and":
        return "Control_Call_Modified"
    if value_lower == "or":
        return "Call_OR_Control_Modified"
    return value_str


def preview_text(value: Any, limit: int = 160) -> str:
    text = _coerce_str(value).replace("\n", " ").strip()
    if len(text) <= limit:
        return text
    return text[: max(0, limit - 3)] + "..."


def comparison_dir_name(target_name: str, baseline_name: str) -> str:
    import os

    pair_dir_name = f"{target_name}_to_{baseline_name}"
    pair_dir_name = pair_dir_name.replace(os.sep, "_")
    if os.altsep:
        pair_dir_name = pair_dir_name.replace(os.altsep, "_")
    return pair_dir_name


def read_json(path: str) -> Any:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def write_json(path: str, data: Any) -> None:
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False, default=str)


def write_text(path: str, text: str) -> None:
    with open(path, "w", encoding="utf-8") as f:
        f.write(text if text is not None else "")
