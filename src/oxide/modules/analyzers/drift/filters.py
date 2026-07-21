import os
from functools import lru_cache
from typing import Any, Dict, Optional

import yaml


def _filter_cards_dir() -> str:
    return os.path.join(os.path.dirname(__file__), "filter_cards")


def normalize_filter_name(value: Any) -> Optional[str]:
    if value is None:
        return None
    text = str(value).strip()
    if not text:
        return None
    if text.lower() in {"none", "null", "false"}:
        return None
    return text


@lru_cache(maxsize=None)
def get_filter_rules(filter_name: Optional[str]) -> Optional[Dict[str, Any]]:
    """ Load a filter card by name, e.g. "Call_Modified" -> filter_cards/Call_Modified.yaml.
        New filter cards can be added by dropping a new yaml file in filter_cards/,
        no code change required.
    """
    if not filter_name:
        return None
    card_path = os.path.join(_filter_cards_dir(), f"{filter_name}.yaml")
    if not os.path.isfile(card_path):
        return None
    with open(card_path, "r", encoding="utf-8") as handle:
        return yaml.safe_load(handle)
