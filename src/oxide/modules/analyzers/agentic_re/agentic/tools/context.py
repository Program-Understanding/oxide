"""
OxideContext — shared infrastructure for the agentic tools.
"""
from __future__ import annotations

import ast as _ast
import operator as _op
import re
import struct as _struct

try:
    import networkx as nx
except Exception:  # noqa: BLE001
    nx = None

LINENO_PREFIX = re.compile(r"^\d+:\s")

_VAL_FMT = {("int8", True): "b", ("int8", False): "B",
            ("int16", True): "h", ("int16", False): "H",
            ("int32", True): "i", ("int32", False): "I",
            ("int64", True): "q", ("int64", False): "Q"}

# ---- safe arithmetic (for the compute tool) ----
_ALLOWED_BINOP = (_ast.Add, _ast.Sub, _ast.Mult, _ast.Div, _ast.FloorDiv, _ast.Mod,
                  _ast.Pow, _ast.BitXor, _ast.BitAnd, _ast.BitOr, _ast.LShift, _ast.RShift)
_ALLOWED_UNARY = (_ast.UAdd, _ast.USub, _ast.Invert)
_OPS = {_ast.Add: _op.add, _ast.Sub: _op.sub, _ast.Mult: _op.mul, _ast.Div: _op.truediv,
        _ast.FloorDiv: _op.floordiv, _ast.Mod: _op.mod, _ast.Pow: _op.pow,
        _ast.BitXor: _op.xor, _ast.BitAnd: _op.and_, _ast.BitOr: _op.or_,
        _ast.LShift: _op.lshift, _ast.RShift: _op.rshift,
        _ast.UAdd: _op.pos, _ast.USub: _op.neg, _ast.Invert: _op.invert}


def safe_eval(node):
    if isinstance(node, _ast.Expression):
        return safe_eval(node.body)
    if isinstance(node, _ast.Constant) and isinstance(node.value, (int, float)):
        return node.value
    if isinstance(node, _ast.BinOp) and isinstance(node.op, _ALLOWED_BINOP):
        return _OPS[type(node.op)](safe_eval(node.left), safe_eval(node.right))
    if isinstance(node, _ast.UnaryOp) and isinstance(node.op, _ALLOWED_UNARY):
        return _OPS[type(node.op)](safe_eval(node.operand))
    raise ValueError("only integer arithmetic/bitwise expressions are allowed")


def addr_list(x) -> list:
    """Parse one address or many (comma/space separated, or a list) into ints."""
    items = [str(i) for i in x] if isinstance(x, (list, tuple)) else re.split(r"[\s,]+", str(x).strip())
    out = []
    for it in items:
        if not it:
            continue
        try:
            out.append(int(it, 0))
        except ValueError:
            pass
    return out


class OxideContext:
    def __init__(self, api, oid: str):
        self.api = api
        self.oid = oid
        self._cache: dict = {}

    # ---- cached Oxide retrievals ----
    def _funcs(self) -> dict:
        if "funcs" not in self._cache:
            self._cache["funcs"] = self.api.get_field("ghidra_disasm", self.oid, "functions") or {}
        return self._cache["funcs"]

    def _fext(self) -> dict:
        if "fext" not in self._cache:
            self._cache["fext"] = self.api.retrieve("function_extract", [self.oid]) or {}
        return self._cache["fext"]

    def _elf(self) -> dict:
        if "elf" not in self._cache:
            r = self.api.retrieve("elf", [self.oid]) or {}
            self._cache["elf"] = (r.get(self.oid) if isinstance(r, dict) and self.oid in r else r) or {}
        return self._cache["elf"]

    def _sections(self) -> dict:
        return self._elf().get("section_table", {}) or {}

    def fmt(self) -> str:
        """Detected container format: 'elf' | 'unknown' (this agent is ELF-only)."""
        if "fmt" in self._cache:
            return self._cache["fmt"]
        f = "unknown"
        try:
            if self._elf().get("elf_header") or self._elf().get("section_table"):
                f = "elf"
        except Exception:  # noqa: BLE001
            pass
        self._cache["fmt"] = f
        return f

    def retrieve_oid(self, module: str, opts: dict = None):
        """Thin api.retrieve unwrapped for this oid (used by simple group tools)."""
        try:
            r = self.api.retrieve(module, [self.oid], opts or {}) or {}
            return r.get(self.oid, r) if isinstance(r, dict) and self.oid in r else r
        except Exception:  # noqa: BLE001
            return None

    def _data(self) -> bytes:
        if "data" not in self._cache:
            try:
                self._cache["data"] = self.api.get_field(self.api.source(self.oid), self.oid, "data") or b""
            except Exception:  # noqa: BLE001
                self._cache["data"] = b""
        return self._cache["data"]

    def _func_summary(self) -> dict:
        if "fsum" not in self._cache:
            self._cache["fsum"] = self.retrieve_oid("function_summary") or {}
        return self._cache["fsum"]

    def _call_mapping(self) -> dict:
        if "cmap" not in self._cache:
            self._cache["cmap"] = self.retrieve_oid("call_mapping") or {}
        return self._cache["cmap"]

    def _ghidra_data(self) -> dict:
        if "gdata" not in self._cache:
            self._cache["gdata"] = self.retrieve_oid("ghidra_data") or {}
        return self._cache["gdata"]

    def _callgraph(self):
        if "cg" not in self._cache:
            try:
                r = self.api.retrieve("call_graph", [self.oid]) or {}
                self._cache["cg"] = r.get(self.oid) if isinstance(r, dict) else r
            except Exception:  # noqa: BLE001
                self._cache["cg"] = None
        return self._cache["cg"]

    # ---- coordinate conversion (ELF section table + Ghidra rebase) ----
    def _gdelta(self) -> int:
        if "gdelta" in self._cache:
            return self._cache["gdelta"]
        delta = 0
        for off, info in (self._funcs() or {}).items():
            if off == "meta" or not isinstance(info, dict):
                continue
            try:
                gv = int(str(info.get("vaddr", "0")), 16)
                ev = self._elf_off_to_vaddr(int(off))
            except (ValueError, TypeError):
                continue
            if ev is not None:
                delta = gv - ev
                break
        self._cache["gdelta"] = delta
        return delta

    def _secmap(self):
        """ELF (file_offset_base, size, link_vaddr) segments from the section table, so the
        offset<->vaddr coordinate conversion works. Cached."""
        if "secmap" in self._cache:
            return self._cache["secmap"]
        m = []
        for s in self._sections().values():
            if isinstance(s, dict) and s.get("addr"):
                m.append((s.get("offset", 0), s.get("size", 0), s.get("addr")))
        self._cache["secmap"] = m
        return m

    def _elf_off_to_vaddr(self, off: int):
        for base, sz, va in self._secmap():
            if va and base <= off < base + sz:
                return off - base + va
        return None

    def _elf_vaddr_to_off(self, va: int):
        for base, sz, sva in self._secmap():
            if sva and sva <= va < sva + sz:
                return va - sva + base
        return None

    def off_to_vaddr(self, off: int):
        ev = self._elf_off_to_vaddr(off)
        return None if ev is None else ev + self._gdelta()

    def vaddr_to_off(self, va: int):
        return self._elf_vaddr_to_off(va - self._gdelta())

    # ---- function name resolution ----
    def _name_maps(self):
        if "nmaps" in self._cache:
            return self._cache["nmaps"]
        fext = self._fext()
        vaddr_by_name, start_by_name, range_by_name = {}, {}, {}
        for name, info in fext.items():
            if not isinstance(info, dict):
                continue
            try:
                vaddr_by_name[name] = int(str(info.get("vaddr", "0")), 16)
            except ValueError:
                pass
            offs = [int(o) for o in (info.get("instructions") or {}).keys()]
            if offs:
                range_by_name[name] = (min(offs), max(offs))
                start_by_name[name] = min(offs)
        self._cache["nmaps"] = (vaddr_by_name, start_by_name, range_by_name)
        return self._cache["nmaps"]

    def resolve_func(self, addr) -> str:
        s = str(addr).strip()
        fext = self._fext()
        if s in fext:
            return s
        for pre in ("sym.imp.", "sym.func.", "sym.", "fcn.", "loc."):
            if s.startswith(pre) and s[len(pre):] in fext:
                return s[len(pre):]
        bare = s.split(".")[-1]
        if bare in fext:
            return bare
        try:
            val = int(s, 0)
        except ValueError:
            return s
        vaddr_by_name, _, range_by_name = self._name_maps()
        for name, va in vaddr_by_name.items():
            if va == val:
                return name
        for cand in (val, self.vaddr_to_off(val)):
            if cand is None:
                continue
            for name, (lo, hi) in range_by_name.items():
                if lo <= cand <= hi:
                    return name
        return s

    # ---- dynamic-import resolution (so xrefs of an imported libc function work) ----
    def is_import(self, name) -> bool:
        """True if `name` is an UNDEFINED dynamic symbol (i.e. an imported function)."""
        info = (self._elf().get("dyn_symbols", {}) or {}).get(str(name))
        return isinstance(info, dict) and info.get("shndx") in (0, "UND", "UNDEF", "SHN_UNDEF")

    def _dynsym_index(self) -> dict:
        """dynamic-symbol NAME -> its index in .dynsym (needed to read .rela.plt). Cached."""
        if "dynidx" in self._cache:
            return self._cache["dynidx"]
        out = {}
        try:
            st = self._elf().get("section_table", {}) or {}
            data = self._data()
            ds, dstr = st.get(".dynsym"), st.get(".dynstr")
            if ds and dstr:
                so, ss, stro = ds["offset"], ds["size"], dstr["offset"]
                for k, i in enumerate(range(0, ss, 24)):
                    nameoff = _struct.unpack_from("<I", data, so + i)[0]
                    end = data.index(b"\0", stro + nameoff)
                    nm = data[stro + nameoff:end].decode("latin1", "replace")
                    if nm and nm not in out:
                        out[nm] = k
        except Exception:  # noqa: BLE001
            pass
        self._cache["dynidx"] = out
        return out

    def _plt_got_to_stub(self) -> dict:
        """elf GOT-slot vaddr -> PLT stub agent-vaddr, by scanning .plt* for `ff 25` (jmp
        qword [rip+GOT]). x86-64 ELF. Cached."""
        if "pltmap" in self._cache:
            return self._cache["pltmap"]
        m = {}
        try:
            st = self._elf().get("section_table", {}) or {}
            data = self._data()
            for nm, s in st.items():
                if not str(nm).startswith(".plt") or not isinstance(s, dict):
                    continue
                base, off, size = s.get("addr", 0), s.get("offset", 0), s.get("size", 0)
                for j in range(0, max(0, size - 5)):
                    if data[off + j] == 0xFF and data[off + j + 1] == 0x25:
                        disp = _struct.unpack_from("<i", data, off + j + 2)[0]
                        got = base + j + 6 + disp
                        sa = self.off_to_vaddr(self._elf_vaddr_to_off(base + (j & ~0xF)))
                        if sa is not None:
                            m[got] = sa
        except Exception:  # noqa: BLE001
            pass
        self._cache["pltmap"] = m
        return m

    def import_plt_stub(self, name):
        """Imported function NAME -> its PLT stub agent-vaddr (call sites `call <stub>`), or None."""
        idx = self._dynsym_index().get(str(name))
        if idx is None:
            return None
        try:
            rp = (self._elf().get("relocations", {}) or {}).get(".rela.plt")
            if not rp or not rp.get("data"):
                return None
            d = rp["data"]
            for i in range(0, len(d) - 23, (rp.get("entsize") or 24)):
                r_off, r_info, _ = _struct.unpack_from("<QQq", d, i)
                if (r_info >> 32) == idx:
                    return self._plt_got_to_stub().get(r_off)
        except Exception:  # noqa: BLE001
            pass
        return None

    def code_refs_to(self, target_vaddr: int, limit: int = 256) -> list:
        """Every instruction that references the given agent-vaddr (scans all functions' disasm
        operands). Generic: works for a string/global OR a PLT stub (import call sites)."""
        out = []
        for name, info in (self._fext() or {}).items():
            insns = info.get("instructions") if isinstance(info, dict) else None
            if not insns:
                continue
            for off, text in insns.items():
                if any(int(h, 16) == target_vaddr for h in re.findall(r"0x[0-9a-fA-F]+", str(text))):
                    va = self.off_to_vaddr(int(off))
                    out.append({"from": hex(va) if va is not None else str(off),
                                "fcn": name, "insn": str(text)})
                    if len(out) >= limit:
                        return out
        return out

    @staticmethod
    def clean_name(n: str) -> str:
        """'<EXTERNAL>::__printf_chk' -> '__printf_chk'."""
        s = str(n)
        if "::" in s:
            s = s.split("::")[-1]
        return s.strip()

    def callees(self, name: str) -> list:
        g = self._callgraph()
        if g is None or nx is None:
            return []
        try:
            return [self.clean_name(c) for c in g.successors(name)]
        except Exception:  # noqa: BLE001
            return []

    def read_at_vaddr(self, addr: str, n: int) -> bytes:
        va = int(str(addr), 0)
        off = self.vaddr_to_off(va)
        if off is None:
            off = va
        return self._data()[off:off + n]
