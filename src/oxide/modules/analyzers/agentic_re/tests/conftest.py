"""Shared fixtures for the offline agentic_re test suite.

Everything here runs WITHOUT Oxide, Ghidra, or an LLM server. The real code is exercised against:
  * FakeApi        -- a canned stand-in for Oxide's api (get_field/retrieve), driving the REAL
                      OxideContext and the real tool backends (ghidra.py / elf.py);
  * synthetic decompilations / disassembly strings for the oracles;
  * lightweight message stubs for the deepagent salvage/claims layers.

Environment set here, BEFORE any agentic import (both are read at import/dispatch time):
  * AGENTIC_LIBC=1     -- populates _LIBC_SIG so libc-dependent oracle logic is testable; the
                          default-off behaviour is tested by temporarily emptying the shared dict.
  * AGENTIC_OUT_CAP=0  -- registry._stringify calls the REQUIRED out_cap() on every dispatch.
"""
from __future__ import annotations

import os
import sys

os.environ.setdefault("AGENTIC_LIBC", "1")
os.environ.setdefault("AGENTIC_OUT_CAP", "0")

_HERE = os.path.dirname(os.path.abspath(__file__))
_PKG = os.path.dirname(_HERE)                      # .../agentic_re  (holds the `agentic` package)
if _PKG not in sys.path:
    sys.path.insert(0, _PKG)

import types                                        # noqa: E402
import pytest                                       # noqa: E402


# ------------------------------------------------------------------ synthetic binary layout
# One ELF-ish address space: section .text at file offset 0x1000, link vaddr 0x1000, size 0x2000.
# Ghidra rebases by +0x100000 (gdelta), i.e. file offset 0x1000 <-> agent vaddr 0x101000.
#
# funcA @0x101000 (off 4096): prologue spill of rdi/esi, a load+deref of the rdi home slot, a
#   forward of it to funcB, stride arithmetic on the slot, and a movzx of the esi slot.
# funcB @0x101100 (off 4352): trivial callee (call target resolution).
# funcC @0x102000 (off 8192): the null-check CFG-join idiom register_usage must survive.
FUNC_A = {
    "4096": "push rbp",
    "4097": "mov rbp,rsp",
    "4100": "mov qword ptr [rbp + -0x18],rdi",
    "4104": "mov dword ptr [rbp + -0x1c],esi",
    "4108": "mov rax,qword ptr [rbp + -0x18]",
    "4112": "mov rdx,qword ptr [rax]",
    "4116": "mov rdi,rax",
    "4120": "call 0x101100",
    "4125": "add qword ptr [rbp + -0x18],0x5",
    "4130": "movzx eax, byte ptr [rbp + -0x1c]",
    "4134": "mov eax,0x0",
    "4139": "pop rbp",
    "4140": "ret",
}
FUNC_C = {
    "8192": "push rbp",
    "8193": "mov rbp,rsp",
    "8196": "mov qword ptr [rbp + -0x10],rdi",
    "8200": "mov rax,qword ptr [rbp + -0x10]",
    "8204": "cmp rax,0x0",
    "8207": "jz 0x102018",
    "8209": "lea rax,[0x102000]",
    "8216": "mov rdx,qword ptr [rax]",
    "8220": "ret",
}
DECMAP_A = {
    "decompile": {
        "funcA": {"0": {"line": [
            "1: 1: undefined8 funcA(char *param_1,char *param_2)",
            "2: 2: {",
            "3: 3:   long lVar1;",
            "4: 4:   lVar1 = *param_1;",
            "5: 5:   funcB(param_1);",
            "6: 6:   return 0;",
            "7: 7: }",
        ]}},
    }
}


class FakeApi:
    """Duck-typed oxide api: canned tables, real access paths."""

    def __init__(self, tables=None):
        self.tables = {
            ("field", "ghidra_disasm", "functions"): {"4096": {"vaddr": "0x101000"}},
            "function_extract": {
                "funcA": {"vaddr": "0x101000", "instructions": dict(FUNC_A)},
                "funcB": {"vaddr": "0x101100", "instructions": {"4352": "ret"}},
                "funcC": {"vaddr": "0x102000", "instructions": dict(FUNC_C)},
            },
            "elf": {
                "elf_header": {"machine": "EM_X86_64", "class": 64, "data": "LSB", "type": "shared"},
                "section_table": {".text": {"offset": 0x1000, "size": 0x2000, "addr": 0x1000}},
                "dyn_symbols": {"strlen": {"shndx": 0}},
            },
            "ghidra_decmap": dict(DECMAP_A),
            "mcp_control_flow_graph": {
                "0": {"name": "funcC",
                      "nodes": {"8192": {k: FUNC_C[k] for k in
                                         ("8192", "8193", "8196", "8200", "8204", "8207")},
                                "8209": {"8209": FUNC_C["8209"]},
                                "8216": {"8216": FUNC_C["8216"], "8220": FUNC_C["8220"]}},
                      "edges": {"8192": ["8209", "8216"], "8209": ["8216"]}},
            },
            ("field", "files", "data"): bytes(range(256)) * 64,   # 16 KiB of patterned bytes
        }
        if tables:
            self.tables.update(tables)

    def get_field(self, module, oid, field):
        return self.tables.get(("field", module, field))

    def retrieve(self, module, oids=None, opts=None):
        return self.tables.get(module)

    def source(self, oid):
        return "files"


@pytest.fixture
def fake_api():
    return FakeApi()


@pytest.fixture
def ctx(fake_api):
    from agentic.tools.context import OxideContext
    return OxideContext(fake_api, "testoid")


@pytest.fixture
def call_tool(fake_api):
    """A REAL registry dispatcher bound to the fake api (memoize off, full outputs)."""
    from agentic import tools as T
    _schemas, ct = T.build_tools(fake_api, "testoid", memoize=False)
    return ct


@pytest.fixture
def oxide_stub(fake_api, monkeypatch):
    """Inject stub `oxide.core.oxide.api` modules so certify._collect_oracle_facts imports work."""
    ox = types.ModuleType("oxide")
    core = types.ModuleType("oxide.core")
    oxo = types.ModuleType("oxide.core.oxide")
    oxo.api = fake_api
    core.oxide = oxo
    ox.core = core
    monkeypatch.setitem(sys.modules, "oxide", ox)
    monkeypatch.setitem(sys.modules, "oxide.core", core)
    monkeypatch.setitem(sys.modules, "oxide.core.oxide", oxo)
    return fake_api


@pytest.fixture
def empty_libc():
    """Temporarily empty the SHARED _LIBC_SIG dict in place (the AGENTIC_LIBC=0 production
    default). In-place because libc_abi/interproc hold references to the same object."""
    from agentic.tasks.type_recovery import common as C
    saved = dict(C._LIBC_SIG)
    C._LIBC_SIG.clear()
    yield
    C._LIBC_SIG.update(saved)


class Msg:
    """Minimal langchain-message stand-in for claims/deepagent helpers (attribute access only)."""

    def __init__(self, type=None, content="", tool_calls=None, tool_call_id=None,
                 invalid_tool_calls=None):
        self.type = type
        self.content = content
        self.tool_calls = tool_calls or []
        self.tool_call_id = tool_call_id
        self.invalid_tool_calls = invalid_tool_calls or []


@pytest.fixture
def msg():
    return Msg


# Canonical question fragments used across oracle tests (tabs = harness form, spaces = tool form).
Q_HEADER = "Recover the C type of each variable in the function at vaddr 0x101000.\n"
Q_TABS = Q_HEADER + "V1\tregister 0x38\t8\nV2\tregister 0x30\t4\nV3\tstack -0x20\t8\nV4\tstack -0x24\t4\n"
Q_SPACES = Q_HEADER + "V1  register 0x38  8\nV2  register 0x30  4\nV3  stack -0x20  8\nV4  stack -0x24  4\n"


@pytest.fixture
def q_tabs():
    return Q_TABS


@pytest.fixture
def q_spaces():
    return Q_SPACES
