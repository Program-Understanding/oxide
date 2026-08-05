# flow_recorder — sequence diagrams of what your agent actually did

A single file you can copy into any project that drives a tool-calling agent. It attaches to a
LangChain / deepagents run, records what happened, and draws a turn-by-turn **sequence diagram**:
every delegation, every tool call and the result it returned, the model's reasoning between calls,
and the final answer.

It is for the question *"what did the agent actually do, and was that reasonable?"* — the one that
logs answer badly and traces answer at the wrong altitude.

```
pip install pillow                       # optional: input/output panels
npm i -g @mermaid-js/mermaid-cli         # optional: PNG/SVG output
```

Nothing is required. Without Pillow you get the diagram without panels; without the Mermaid CLI you
get `.mmd` source that renders in any Mermaid viewer, including GitHub.

## Quick start

```python
from flow_recorder import FlowRecorder, emit

rec = FlowRecorder()
result = agent.invoke(inputs, config={"callbacks": [rec]})

emit(rec, "out/run", title="my run", answer=result["messages"][-1].content)
# -> out/run_turns.mmd, out/run_turns.svg, out/run_turns.png
```

That is the whole minimum. Everything else is optional refinement.

## Getting the events in: three ways

Pick whichever matches how your driver runs the agent. All three produce the same events, so every
view works identically afterwards.

**1. Callbacks** — when you control `invoke` or `astream`:

```python
rec = FlowRecorder()
agent.invoke(inputs, config={"callbacks": [rec]})
# works with astream too:
async for mode, data in agent.astream(inputs, stream_mode=["updates"], config={"callbacks": [rec]}):
    ...
```

**2. A finished message list** — when the driver streams updates, or you only have the transcript
afterwards. No callback wiring at all:

```python
rec = FlowRecorder.from_messages(result["messages"])
```

It understands the standard shapes: an assistant message carrying `.tool_calls`, and a tool message
carrying `.tool_call_id` / `.name` / `.content`. Plain dicts with those keys work too.

**3. Manual recording** — for a framework with no callbacks, a custom transcript, or a test:

```python
rec = FlowRecorder()
rec.record_reasoning("popen is suspicious; disassemble its caller")
rec.record_tool_call("disassemble", {"addr": "0x4011a0"}, result="call popen ; test eax,eax")
rec.record_delegation("critic", brief="fact-check Q3 Q4", result="Q3: supported")
```

Replaying a transcript you already collect is usually a handful of lines. For example, oxide's
`agent_compare` plugin drives deepagents with `astream` and appends entries shaped
`{node, content, tool_calls, tool_name, tool_call_id}`; feeding those in is:

```python
rec = FlowRecorder()
for e in transcript:
    if e["node"] == "model":
        rec.record_reasoning(e["content"])
    elif e["node"] == "tools":
        args = lookup_args_by_id(transcript, e["tool_call_id"])
        rec.record_tool_call(e["tool_name"], args, e["content"])
```

Single-agent pipelines need no delegations: with none recorded, the tool calls are drawn straight
from the root lifeline and no sub-agent is invented.

## The public names

### `FlowRecorder()`
A `BaseCallbackHandler` that also exposes `record_tool_call`, `record_delegation`,
`record_reasoning` and the `from_messages` constructor described above. Reuse one per run.

### `emit(recorder, out_base, **kwargs) -> {view: path}`

| argument | meaning |
|---|---|
| `title` | free text for the input panel |
| `inventory` | `[(id, description, size)]` rows for the input panel; `size` may be `""` |
| `answer` | the run's final text; `id: value` lines fill the output panel |
| `facts` | `{id: (value, source, mode)}` deterministic facts, drawn as their own lifeline |
| `consulted` | names of fact producers that ran, so ones that abstained are shown |
| `applied_in_code` | `True` if a post-pass applied `facts`; `False` if the agent fetched them itself |
| `scoring` | `{"score": float, "ground_truth": {...}, "per_var": {...}}` overlay |
| `views` | any of `"sequence"` (default), `"flowchart"`, `"markdown"` |
| `style` | a `Style` (below) |

### `rescore(score=..., ground_truth=..., per_var=...)`
Redraw the last emitted run with a result overlay. Useful when the score is only known after
something downstream grades the answer.

## Customising with `Style`

Participants are **discovered from the run** — every distinct delegation target becomes a lifeline,
in first-appearance order — so a pipeline with agents named `searcher` and `critic` just works.
`Style` controls the rest:

```python
from flow_recorder import Style, emit

style = Style(
    root="Lead",                      # the orchestrating agent's label
    tools="Web",                      # label for the tool lifeline
    agent_suffix="",                  # "searcher" instead of "searcher agent"
    roles={"searcher": "gather evidence for", "critic": "fact-check"},
    entity_re=r"Q\d+",                # what an item id looks like; None to disable
    item_noun="claims",               # what the input panel counts
    icon_for={"lead": "🧠", "search": "🔎", "critic": "⚖️", "web": "🌐"},
    icons=True,                       # False for plain ASCII
    max_tools=40,                     # tool calls drawn per phase before summarising
    max_reason=180,                   # characters of a reasoning note
    show_reasoning=True,
    show_plan=True,
)
emit(rec, "out/run", style=style, ...)
```

`fact_tools` is the one remaining domain hint: name the tools whose output is a list of per-item
facts and their results render as `id=value` pairs instead of a truncated prefix.

## What the diagram shows

- **Plan rows** above the first delegation. If the agent never called a planning tool, the plan is
  synthesized from the delegations that actually happened — which is more faithful than the
  declared plan, since it shows what it did rather than what it said it would do.
- **One phase per delegation**: the task arrow, that phase's tool calls with their returns, a
  reasoning note, and the result the sub-agent returned.
- **A facts lifeline**, only when `applied_in_code=True`. When the agent fetches the facts itself
  they are ordinary tool calls already drawn on the tools lifeline, and a second actor would imply
  two appliers where there is one.
- **Input and output panels** stacked around the diagram, with a ground-truth column when
  `scoring` supplies one.

## Notes

- Everything is best-effort: a rendering failure prints a line and returns; it never raises into
  the caller's run.
- Phases are segmented by delegation rather than by reconstructing the run-id tree, which matches
  a serial parent→child flow. Concurrent sub-agents would interleave.
- Long tool outputs are truncated for display; `fact_tools` are kept whole because a prefix would
  hide all but the first fact.
- `AGENTIC_FLOW_SCALE` (default 3) and `AGENTIC_FLOW_WIDTH` (default 1600) tune the PNG.

## Worked examples

`demo.py` and `demo_generic.py` in the same directory drive the recorder with synthetic events, no
agent required — one for a binary-analysis pipeline, one for a literature-review pipeline. They are
the fastest way to see the output and to check the tool still works after a change.
