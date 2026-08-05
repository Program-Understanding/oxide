"""flow_recorder demo 2 of 3 — a different domain, customised with Style.

Nothing here is about binaries. A literature-review pipeline delegates to `searcher` and `critic`,
argues about claim ids like Q3, and calls web tools. The point is that only `Style` changes: the
lifelines are discovered from the run, so new agent names need no code.

    python3 demo_generic.py        # writes generic_run_turns.png

See FLOW_RECORDER.md for the full API. Companion demos:
    demo.py                 multi-agent with deterministic facts and a score overlay
    demo_agent_compare.py   a single-agent driver that never sees a callback
"""
import flow_recorder as FR

rec = FR.FlowRecorder()

rec.on_tool_start({"name": "task"},
                  {"description": "gather sources for Q3 Q4", "subagent_type": "searcher"}, run_id=1)
rec.on_tool_start({"name": "web_search"}, {"query": "battery degradation 2026"}, run_id=2)
rec.on_tool_end("12 results; top: Nature Energy 2026", run_id=2)
rec.on_tool_end("Q3: 8 sources\nQ4: 5 sources", run_id=1)

rec.on_tool_start({"name": "task"},
                  {"description": "fact-check Q3 Q4", "subagent_type": "critic"}, run_id=3)
rec.on_tool_start({"name": "fetch_page"}, {"url": "nature.com/..."}, run_id=4)
rec.on_tool_end("abstract: cycle life improved 22%", run_id=4)
rec.on_tool_end("Q3: supported\nQ4: weak", run_id=3)

# Everything domain-specific lives here; the recorder above is unchanged from demo 1.
style = FR.Style(
    root="Lead",                  # who orchestrates
    tools="Web",                  # where tool calls go
    agent_suffix="",              # "searcher", not "searcher agent"
    roles={"searcher": "gather evidence for", "critic": "fact-check"},
    entity_re=r"Q\d+",            # claim ids, so a delegation summarises as "Q3-Q4"
    item_noun="claims",           # what the input panel counts
    icon_for={"lead": "\U0001f9e0", "search": "\U0001f50e",
              "critic": "⚖️", "web": "\U0001f310"},
)

print("emit ->", FR.emit(
    rec, "generic_run",
    title="literature review: solid-state batteries",
    inventory=[("Q3", "cycle-life claim", ""), ("Q4", "cost claim", "")],
    answer="Q3: supported\nQ4: weak",
    style=style,          # no facts/consulted: this pipeline has no deterministic checks,
))                        # so no facts lifeline is drawn
