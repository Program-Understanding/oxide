import logging
from typing import Any, Dict, Optional, List
import json

import networkx as nx
from llm_service import runner

from oxide.core import api, progress
import textwrap

logger = logging.getLogger(__name__)

# Module metadata
DESC = """Uses an LLM to generate high‑level tags for a file by analysing its
call‑graph and summarising the *influential* functions only."""
NAME = "tag_file"
CATEGORY = ""

# Options documentation
opts_doc: Dict[str, Dict[str, str]] = {}


def documentation() -> Dict[str, Any]:
    """Return module documentation understood by the Oxide plug‑in loader."""
    return {
        "description": DESC,
        "opts_doc": opts_doc,
        "private": False,
        "set": False,
        "atomic": True,
        "category": CATEGORY,
    }


# ────────────────────────────────────────────────────────────────────────────
# Main entry‑point
# ────────────────────────────────────────────────────────────────────────────

def process(oid: str, opts: Dict[str, Any]) -> bool:
    """Populate *only* the **influential functions** for *oid* and store it."""
    logger.debug("Starting tag‑file process for %s", oid)

    call_graph: nx.DiGraph = api.get_field("call_graph", oid, oid)
    if call_graph.number_of_nodes() == 0:
        results = "FAILED"
        api.store(NAME, oid, results, opts)
        return False

    # We now keep *one* output bucket only
    results: Dict[str, Dict[str, Any]] = {}

    # Ensure decompilation is available before we begin
    decmap = api.retrieve("ghidra_decmap", [oid], {"org_by_func": True})
    if decmap is None:
        results = "FAILED"
        api.store(NAME, oid, results, opts)
        return False

    influential_tags = api.retrieve("tag_influential_functions", oid)
    influential_tags = influential_tags.values()

    # Generate a file summary via LLM
    if influential_tags:
        results["file overview"] = tag_file_summary(influential_tags)

    api.store(NAME, oid, results, opts)
    logger.debug("Finished tag‑file process for %s", oid)
    return True

def tag_file_summary(file_tags: List[str], temperature: float = 0.15, max_new_tokens: int = 1000) -> dict:
    """
    Prompt LLM with file tags; generate structured buckets and summary.
    """
    tag_block = "\n".join(sorted(file_tags)) or "<no exclusive descendants>"
    prompt = textwrap.dedent(f"""
    FUNCTION TAGS:
    {tag_block}

    ─────────────────────────────────────────────────────────
    TASK:
    1. Group tags into highly specific buckets capturing firmware capabilities.
        • Avoid broad, generic labels (e.g., \"General\", \"Miscellaneous\").
        • Aim for granular buckets that are as specific as possible, focusing on distinct firmware tasks or functionality.
        • Preserve each tag exactly as provided; do not extract or abbreviate tags.
        • Sort each full tag verbatim into the appropriate bucket.
    2. For each bucket:
       a. Provide a precise, action-oriented title (2-6 words, Title Case).
       b. List all member tags exactly as provided.
       c. Write a concise, detailed rationale (≤ 15 words) clearly explaining the commonality among tags.
    3. After the buckets, provide a one-sentence, detailed summary explicitly stating the firmware's main role based on the identified bucket functionalities.

    ─────────────────────────────────────────────────────────
    OUTPUT FORMAT:
    Respond ONLY with valid JSON matching this schema:

    {
      "buckets": [
        {
          "name": "Specific Bucket 1 Title",
          "tags": ["tag1", "tag2"],
          "rationale": "Detailed sentence."
        },
        {
          "name": "Specific Bucket n Title",
          "tags": ["tag3", "tag4"],
          "rationale": "Detailed sentence."
        }
      ],
      "file_summary": "Detailed one-sentence summary."
    }

    Ensure the JSON is complete and valid.
    """).strip()

    response = runner.generate(
        user_input=prompt,
        temperature=temperature,
        max_new_tokens=max_new_tokens
    )

    # Parse response into a dictionary
    try:
        parsed_response = json.loads(response)
    except json.JSONDecodeError as e:
        raise ValueError(f"Invalid JSON received: {e}\nResponse: {response}")

    return parsed_response