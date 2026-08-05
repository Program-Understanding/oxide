"""Third integration shape: oxide's agent_compare plugin.

It drives deepagents with `astream(stream_mode=["updates"])` and collects its own transcript, so it
never sees a callback. Both paths below work without touching the plugin's control flow.
"""
import flow_recorder as FR

# ---- PATH A: replay the transcript the plugin already builds ---------------------------------
transcript = [                      # exactly the entry shape agent_compare appends
  {"elapsed": 1.2, "node": "model",  "content": "I should look for suspicious imports first.",
   "tool_calls": [{"name": "get_imports", "args": {"oid": "abc123"}, "id": "c1"}]},
  {"elapsed": 3.4, "node": "tools",  "content": "system, popen, dlopen", "tool_name": "get_imports",
   "tool_call_id": "c1"},
  {"elapsed": 5.0, "node": "model",  "content": "popen is suspicious; disassemble its caller.",
   "tool_calls": [{"name": "disassemble", "args": {"addr": "0x4011a0"}, "id": "c2"}]},
  {"elapsed": 7.1, "node": "tools",  "content": "call popen ; test eax,eax ; je 0x4011f0",
   "tool_name": "disassemble", "tool_call_id": "c2"},
]
rec = FR.FlowRecorder()
for e in transcript:
    if e["node"] == "model":
        rec.record_reasoning(e["content"])
    elif e["node"] == "tools":
        args = next((tc["args"] for x in transcript for tc in (x.get("tool_calls") or [])
                     if tc["id"] == e["tool_call_id"]), {})
        rec.record_tool_call(e["tool_name"], args, e["content"])

style = FR.Style(root="Analyst", tools="Oxide MCP", entity_re=None, item_noun="binaries",
                 icon_for={"analyst": "\U0001f575️", "oxide": "\U0001f527"})
print("A:", FR.emit(rec, "compare_run", title="backdoor triage: sudo-1.9.5p2",
                    answer="verdict: backdoor present\nfunction: check_auth",
                    style=style))

# ---- PATH B: no manual loop at all, straight from a LangChain message list --------------------
class Msg:                                    # stand-in for AIMessage / ToolMessage
    def __init__(self, **kw): self.__dict__.update(kw)
msgs = [Msg(content="checking imports", tool_calls=[{"name": "get_imports", "args": {}, "id": "t1"}]),
        Msg(content="system, popen", tool_call_id="t1", name="get_imports")]
rec2 = FR.FlowRecorder.from_messages(msgs)
print("B:", FR.emit(rec2, "compare_msgs", title="from_messages path", style=style))
