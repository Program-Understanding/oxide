"""flow_recorder demo 1 of 3 — a multi-agent run with deterministic facts and a score overlay.

Shows: sub-agents discovered from the run itself, a facts lifeline for checks a post-pass applied
after the agents, and `rescore` adding a ground-truth column once something has graded the answer.

No agent and no network needed — the callbacks are driven by hand with the arguments LangChain
would pass. Run it, then open demo_run_turns.png.

    python3 demo.py

See FLOW_RECORDER.md for the full API. Companion demos:
    demo_generic.py         a different domain, customised with Style
    demo_agent_compare.py   a single-agent driver that never sees a callback
"""
import flow_recorder as FR

rec = FR.FlowRecorder()

# --- what LangChain reports for a coordinator -> worker -> verifier run ------------------------
rec.on_tool_start({"name": "task"},
                  {"description": "recover types for V1 V6", "subagent_type": "type_worker"},
                  run_id=1)
rec.on_tool_start({"name": "disassemble"}, {"addr": "0x102f27"}, run_id=2)
rec.on_tool_end("mov [rbp-0x48],rdi ; cmp [rbp-0x28],-0x1", run_id=2)
rec.on_tool_end("V1: FILE *\nV6: int", run_id=1)

rec.on_tool_start({"name": "task"},
                  {"description": "adjudicate V1 V6", "subagent_type": "verifier"}, run_id=3)
rec.on_tool_start({"name": "decompile"}, {"addr": "0x102f27"}, run_id=4)
rec.on_tool_end("void FUN_00102f27(FILE *param_1)", run_id=4)
rec.on_tool_end("V1: FILE *\nV6: uint", run_id=3)

# --- draw it ----------------------------------------------------------------------------------
path = FR.emit(
    rec, "demo_run",
    title="cut/cut_fields @0x102f27",
    inventory=[("V1", "register 0x38", 8), ("V6", "stack -0x30", 4)],
    answer='V1: FILE *\nV6: uint\n{"V1": "FILE *", "V6": "uint"}',
    # Facts a deterministic pass applied AFTER the agents, so they get their own lifeline. Had the
    # verifier fetched them itself they would already be tool calls, and applied_in_code=False
    # would leave that lifeline out rather than imply two appliers.
    facts={"V1": ("FILE *", "decompiler_pointer", "exact")},
    consulted=["decompiler_pointer", "signedness"],   # signedness abstained; the figure says so
    applied_in_code=True,
)
print("emit ->", path)

# --- later, once something has graded the answer -----------------------------------------------
print("rescore ->", FR.rescore(score=86.11, ground_truth={"V1": "FILE *", "V6": "int"}))
