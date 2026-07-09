"""Shared LLM token-usage accounting, used by all three stages."""

from typing import Any, Dict


def extract_usage_counts_from_message(message: Any) -> Dict[str, int]:
    input_tokens = 0
    output_tokens = 0
    total_tokens = 0

    usage = getattr(message, "usage_metadata", None)
    if isinstance(usage, dict):
        input_tokens = max(0, int(usage.get("input_tokens") or 0))
        output_tokens = max(0, int(usage.get("output_tokens") or 0))
        total_tokens = max(0, int(usage.get("total_tokens") or 0))

    response_metadata = getattr(message, "response_metadata", None)
    if isinstance(response_metadata, dict):
        if input_tokens <= 0:
            input_tokens = max(0, int(response_metadata.get("prompt_eval_count") or 0))
        if output_tokens <= 0:
            output_tokens = max(0, int(response_metadata.get("eval_count") or 0))

    if total_tokens <= 0:
        total_tokens = input_tokens + output_tokens
    return {
        "input_tokens": input_tokens,
        "output_tokens": output_tokens,
        "total_tokens": total_tokens,
    }


def zero_usage_counts() -> Dict[str, int]:
    return {"input_tokens": 0, "output_tokens": 0, "total_tokens": 0}


def collect_llm_usage_counts(messages: Any) -> Dict[str, int]:
    counts = zero_usage_counts()
    if not isinstance(messages, list):
        return counts
    for message in messages:
        usage = extract_usage_counts_from_message(message)
        counts["input_tokens"] += usage.get("input_tokens", 0)
        counts["output_tokens"] += usage.get("output_tokens", 0)
        counts["total_tokens"] += usage.get("total_tokens", 0)
    return counts
