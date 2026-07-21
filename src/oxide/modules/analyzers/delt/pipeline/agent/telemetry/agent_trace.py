"""Isolated stream-chunk normalization and agent_trace.log/trace_view.txt rendering.

Validated against: deepagents==0.6.10, langgraph==1.2.5. If a future release
renames stream event shapes or node names again (this file already carries one
such compatibility shim -- "model" vs "model_request" node naming), this is the
only file that needs a new branch added; triage.py/analyze.py never parse raw
stream chunks themselves.
"""

import logging
import os
import re
import textwrap
from typing import Any, Dict, List, Optional, Tuple

from oxide.modules.analyzers.delt.config import NAME
from oxide.modules.analyzers.delt.pipeline.utils.text_utils import preview_text, write_text

logger = logging.getLogger(NAME)


def append_trace_line(path: Optional[str], line: str, *, truncate: bool = False) -> None:
    if not path:
        return
    try:
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
        mode = "w" if truncate else "a"
        with open(path, mode, encoding="utf-8") as f:
            f.write(line.rstrip() + "\n")
    except Exception:
        return


def _trace_source(ns: Any) -> str:
    if not isinstance(ns, tuple) or not ns:
        return "agent"
    if any(isinstance(segment, str) and segment.startswith("tools:") for segment in ns):
        return "subagent"
    return "agent"


def _extract_token_text(content: Any) -> str:
    """Extract raw text from a streaming token content without stripping whitespace."""
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        parts = []
        for block in content:
            if isinstance(block, dict) and block.get("type") == "text":
                parts.append(block.get("text", ""))
        return "".join(parts)
    return ""


def normalize_stream_item(item: Any) -> Dict[str, Any]:
    namespace: Tuple[str, ...] = ()
    mode = "values"
    data = item

    if isinstance(item, dict) and {"type", "data"} <= set(item.keys()):
        namespace = tuple(item.get("ns") or ())
        mode = str(item.get("type") or "values")
        data = item.get("data")
    elif isinstance(item, tuple):
        if len(item) == 3:
            namespace = tuple(item[0] or ())
            mode = str(item[1] or "values")
            data = item[2]
        elif len(item) == 2:
            if isinstance(item[0], tuple):
                namespace = tuple(item[0] or ())
                data = item[1]
            else:
                mode = str(item[0] or "values")
                data = item[1]

    return {
        "ns": namespace,
        "type": mode,
        "data": data,
    }


class TraceLogger:
    """Accumulates per-chunk trace text and flushes it to trace_path as the agent streams."""

    def __init__(self, trace_path: Optional[str]) -> None:
        self.trace_path = trace_path
        self.text_buffers: Dict[str, str] = {"agent": "", "subagent": ""}

    def _flush_source(self, source: str, elapsed_s: float, *, force: bool = False) -> None:
        text = self.text_buffers.get(source, "")
        if not text:
            return
        if not force and len(text) < 120 and "\n" not in text:
            return
        line = text.replace("\n", " ").strip()
        if line:
            append_trace_line(self.trace_path, f"[{elapsed_s:7.2f}s] [{source}] text: {line}")
        self.text_buffers[source] = ""

    def flush(self, elapsed_s: float) -> None:
        self._flush_source("agent", elapsed_s, force=True)
        self._flush_source("subagent", elapsed_s, force=True)

    def on_chunk(self, chunk: Dict[str, Any], elapsed_s: float) -> None:
        chunk_type = str(chunk.get("type") or "")
        source = _trace_source(chunk.get("ns"))
        data = chunk.get("data")

        if chunk_type == "updates" and isinstance(data, dict):
            self._flush_source(source, elapsed_s, force=True)
            for node_name in data:
                # langchain >= 1.x names the model node "model"; older deepagents docs
                # call it "model_request". Accept both so model steps are traced.
                if node_name in {"model", "model_request", "tools"}:
                    append_trace_line(self.trace_path, f"[{elapsed_s:7.2f}s] [{source}] step: {node_name}")
            return

        if chunk_type == "tasks":
            self._flush_source(source, elapsed_s, force=True)
            append_trace_line(self.trace_path, f"[{elapsed_s:7.2f}s] [{source}] task event: {preview_text(data)}")
            return

        if chunk_type == "messages" and isinstance(data, tuple) and len(data) == 2:
            token, _metadata = data
            tool_call_chunks = getattr(token, "tool_call_chunks", None) or []
            for tool_call in tool_call_chunks:
                name = tool_call.get("name")
                if not name:
                    continue
                self._flush_source(source, elapsed_s, force=True)
                if source == "agent" and name == "task":
                    append_trace_line(self.trace_path, f"[{elapsed_s:7.2f}s] [agent] subagent call: task")
                else:
                    append_trace_line(self.trace_path, f"[{elapsed_s:7.2f}s] [{source}] tool call: {name}")
            content = getattr(token, "content", "")
            if getattr(token, "type", "") != "tool" and content and not tool_call_chunks:
                self.text_buffers[source] = self.text_buffers.get(source, "") + _extract_token_text(content)
                self._flush_source(source, elapsed_s)
            if getattr(token, "type", "") == "tool":
                tool_name = getattr(token, "name", "tool")
                self._flush_source(source, elapsed_s, force=True)
                if source == "agent" and tool_name == "task":
                    result_preview = preview_text(getattr(token, "content", ""), limit=300)
                    append_trace_line(self.trace_path, f"[{elapsed_s:7.2f}s] [subagent] result: {result_preview}")
                else:
                    result_preview = preview_text(getattr(token, "content", ""), limit=200)
                    append_trace_line(
                        self.trace_path,
                        f"[{elapsed_s:7.2f}s] [{source}] tool result [{tool_name}]: {result_preview}",
                    )


def write_trace_view(trace_path: str, out_path: str) -> None:
    """Write a clean human-readable summary of an agent_trace.log to out_path."""
    TS_RE = re.compile(r'^\[\s*([\d.]+)s\] \[agent\] (.+)$')
    RES_RE = re.compile(r'^tool result \[([^\]]+)\]: (.*)$', re.DOTALL)
    FIN_RE = re.compile(r"label=([A-Za-z_]+)")
    WF_RE = re.compile(r'Updated file (/\S+)')

    def trunc(s: str, n: int = 300) -> str:
        s = s.strip()
        return s[:n] + "…" if len(s) > n else s

    def fmt_result(name: str, content: str) -> str:
        if name == "write_file":
            m = WF_RE.search(content)
            return f"  → wrote {m.group(1) if m else '?'}"
        if name == "write_todos":
            items = re.findall(r"'content': '([^']+)', 'status': '([^']+)'", content)
            parts = [f"[{'x' if s=='completed' else '·' if s=='in_progress' else ' '}] {t}" for t, s in items]
            return "  " + "  ".join(parts)
        if name == "FinalDecisionSchema":
            return ""
        return "  " + trunc(content)

    if not os.path.exists(trace_path):
        return

    raw: List[Tuple[float, str]] = []
    for line in open(trace_path).read().splitlines():
        m = TS_RE.match(line)
        if m:
            raw.append((float(m.group(1)), m.group(2)))

    events: List[Tuple[float, str, Any]] = []
    text_buf: List[str] = []
    text_ts: Optional[float] = None

    def flush_text() -> None:
        nonlocal text_buf, text_ts
        if text_buf:
            events.append((text_ts, "TEXT", "".join(text_buf).strip()))  # type: ignore[arg-type]
            text_buf[:] = []
            text_ts = None

    for ts, body in raw:
        if body.startswith("text: "):
            if text_ts is None:
                text_ts = ts
            text_buf.append(body[6:])
            continue
        flush_text()
        if body.startswith("tool call: "):
            events.append((ts, "CALL", body[11:]))
        elif body.startswith("tool result ["):
            m2 = RES_RE.match(body)
            if m2:
                events.append((ts, "RESULT", (m2.group(1), m2.group(2))))
        elif body.startswith("start "):
            events.append((ts, "START", body[6:]))
        elif body.startswith("final: "):
            events.append((ts, "FINAL", body[7:]))
        elif body.startswith("subagent call: "):
            events.append((ts, "SUB_CALL", body[15:]))
        elif body.startswith("subagent result: "):
            events.append((ts, "SUB_DONE", body[17:]))
        elif any(w in body.lower() for w in ("error", "timeout", "failed")):
            events.append((ts, "ERROR", body))
    flush_text()

    ind = " " * 17
    lines_out: List[str] = []
    for ts, kind, data in events:
        ts_str = f"[{ts:7.2f}s]"
        if kind == "START":
            lines_out.append(f"{ts_str}  START     {data}")
        elif kind == "CALL":
            lines_out.append(f"\n{ts_str}  CALL      {data}")
        elif kind == "RESULT":
            name, content = data
            out = fmt_result(name, content)
            if out:
                lines_out.append(f"{ts_str}           {out}")
        elif kind == "TEXT":
            wrapped = textwrap.fill(trunc(data, 800), width=100, subsequent_indent=ind + "  ")
            lines_out.append(f"\n{ts_str}  THINK     {wrapped}")
        elif kind == "SUB_CALL":
            lines_out.append(f"\n{ts_str}  SUBAGENT  {trunc(data, 200)}")
        elif kind == "SUB_DONE":
            lines_out.append(f"{ts_str}  SUB_DONE  {trunc(data, 200)}")
        elif kind == "FINAL":
            m3 = FIN_RE.search(data)
            lines_out.append("")
            if m3:
                lines_out.append(f"{ts_str}  FINAL     label={m3.group(1)}")
            else:
                lines_out.append(f"{ts_str}  FINAL     {data}")
        elif kind == "ERROR":
            lines_out.append(f"\n{ts_str}  ERROR     {data}")

    write_text(out_path, "\n".join(lines_out) + "\n")
