"""Ghidra-derived analysis tools (group: ghidra). Thin exposures of ghidra_disasm/
function_extract, mcp_control_flow_graph, call_graph, ghidra_decmap, function_summary,
ghidra_data, call_mapping."""
from __future__ import annotations

import os
import re

from .registry import tool
from .context import nx, LINENO_PREFIX


@tool(group="ghidra", params={}, desc="List functions")
def list_functions(ctx, limit: int = 400) -> list:
    vaddr_by_name, _, range_by_name = ctx._name_maps()
    fsum = ctx._func_summary()
    out = []
    for name in ctx._fext():
        lo_hi = range_by_name.get(name)
        size = (lo_hi[1] - lo_hi[0]) if lo_hi else 0
        va = vaddr_by_name.get(name)
        row = {"name": name, "addr": hex(va) if va is not None else None, "size": size}
        s = fsum.get(name) if isinstance(fsum, dict) else None
        if isinstance(s, dict):
            row["num_insns"] = s.get("num_insns")
            row["complexity"] = s.get("complexity")
        out.append(row)
    out.sort(key=lambda f: f.get("size", 0), reverse=True)
    return out[:limit]


@tool(group="ghidra", params={"name": {"type": "string"}},
      desc="Per-function metrics (signature, complexity, params); omit name for all.")
def function_summary(ctx, name: str = "") -> dict:
    fsum = ctx._func_summary()
    if not isinstance(fsum, dict):
        return {}
    if name:
        n = ctx.resolve_func(name)
        return {n: fsum.get(n, {})}
    return fsum


# Both annotations below close a JOIN the listing leaves open. The information is already in the
# binary; only the correlation is missing, and the agent has been measured not to perform it.
def _frame_delta(insns, keys):
    """Bytes pushed before `mov rbp,rsp` — the offset between the question's CFA-style frame
    coordinates and the rbp-relative ones the disassembly prints. Same rule as `stack_var`."""
    delta = 0
    for k in keys[:16]:
        t = insns[k]
        if re.match(r"\s*push\b", t):
            delta += 8
        if re.search(r"\bmov\b\s+rbp\s*,\s*rsp\b", t):
            return delta, True
    return delta, False


def _callsite_names(ctx, fname):
    """{call-target vaddr -> callee name}. `resolve_func` covers local functions but NOT imported
    ones: a `call 0x00102350` to a PLT stub resolves to nothing, so the listing shows a bare address
    while the CALLS header shows `__fpending`, and nothing says they are the same call. Invert the
    PLT stub map to close that."""
    out = {}
    for c in set(ctx.callees(fname) or []):
        try:
            stub = ctx.import_plt_stub(c)
        except Exception:  # noqa: BLE001
            stub = None
        if stub:
            out[int(stub)] = c
    return out


@tool(group="ghidra", params={"addr": {"type": "string"}, "n_instructions": {"type": "integer"}},
      required=["addr"],
      desc="Disassemble the function at addr (windowed around an inner address for large fns).")
def disassemble(ctx, addr: str, n_instructions: int = 128) -> str:
    name = ctx.resolve_func(addr)
    info = ctx._fext().get(name)
    if not isinstance(info, dict) or not info.get("instructions"):
        return f"(no function at {addr}; try list_functions for the real name)"
    insns = info["instructions"]
    keys = sorted(insns, key=lambda o: int(o))
    n = max(8, int(n_instructions or 128))
    # center the window on the requested address if it is a concrete vaddr inside the function
    center = None
    try:
        toff = ctx.vaddr_to_off(int(str(addr), 0))
        if toff is not None:
            le = [k for k in keys if int(k) <= toff]
            if le:
                center = le[-1]
    except (ValueError, TypeError):
        pass
    note = ""
    if center is not None and len(keys) > n:
        # Window of n instructions centred on the requested address, SLID (not clipped) when the
        # centre is near either end so the caller always gets the full n it asked for.
        # The old form computed `hi = idx + n//2; lo = hi - n` and clamped lo at 0, which silently
        # halved the window whenever idx < n//2 — i.e. on EVERY call that passes the function's own
        # entry address, which is exactly what the worker prompt tells the agent to do. A 290-insn
        # function returned 50 of 290 instructions for n=100.
        idx = keys.index(center)
        lo = max(0, idx - n // 2)
        hi = min(len(keys), lo + n)
        lo = max(0, hi - n)          # slide back when clipped at the end, to keep the full budget
        chosen = keys[lo:hi]
        note = f"(window: instructions {lo}-{hi} of {len(keys)}"
    elif len(keys) > n:
        lo, hi = 0, n
        chosen = keys[:n]
        note = f"(window: instructions {lo}-{hi} of {len(keys)}"
    else:
        lo, hi = 0, len(keys)
        chosen = keys
    if note:
        if hi < len(keys):
            note += f"; {len(keys) - hi} not shown"
            # OPT-IN paging hint. Naming the next address is what would let a caller actually
            # continue — the old text ("disassemble a function name/start for the top") gave it
            # nowhere to go, so it never paged. But it is a MODEL-FACING instruction and the worker
            # runs under a hard 10-tool-turn cap that it already saturates, so every disassemble it
            # spends paging is a stack_var it does not spend on a variable. Default OFF: the window
            # fix above is deterministic and strictly additive, this is not. A/B before enabling.
            if os.environ.get("AGENTIC_DISASM_PAGING_HINT", "") in ("1", "true", "yes"):
                nxt = ctx.off_to_vaddr(int(keys[hi]))
                if nxt is not None:
                    note += f" — to read them call disassemble with addr=\"{hex(nxt)}\""
        note += ")\n"
    # NOTE: annotating this listing in place -- naming call targets (`call 0x102350  ; __fpending`)
    # and tagging each `[rbp + N]` with its question-coordinate slot -- was implemented and MEASURED
    # (10-function paired A/B): it cut stack_var's found:false rate 21% -> 12% but scored -0.92, and
    # cost +22% on the largest consumer of the model's context. Removed. `register_usage` below
    # addresses the same failure more directly and took found:false to 2%.
    lines = []
    for off in chosen:
        va = ctx.off_to_vaddr(int(off))
        mark = "    <=== requested address" if off == center else ""
        lines.append(f"{hex(va) if va is not None else str(off)}    {insns[off]}{mark}")
    calls = sorted(set(ctx.callees(name)))
    head = ("CALLS: " + ", ".join(calls) + "\n\n") if calls else ""
    return head + note + "\n".join(lines)


@tool(group="ghidra", params={"addr": {"type": "string"}}, required=["addr"],
      desc="Decompile the function at addr (pseudo-C).")
def decompile(ctx, addr: str) -> str:
    name = ctx.resolve_func(addr)
    result = ctx.retrieve_oid("ghidra_decmap", {"org_by_func": True}) or {}
    fns = result.get("decompile", {})
    if name not in fns:
        return f"(no decompilation for {name})"
    decomp_map = {}
    for _, off_val in fns[name].items():
        for line_str in off_val.get("line", []):
            split = line_str.find(": ")
            if split < 0:
                continue
            try:
                line_no = int(line_str[:split])
            except ValueError:
                continue
            code = line_str[split + 2:]
            m = LINENO_PREFIX.match(code)        # Oxide duplicates the line number ('29: 29: code')
            if m:
                code = code[m.end():]
            decomp_map.setdefault(line_no, code)
    out, indent = [], 0
    for ln in sorted(decomp_map):
        code = str(decomp_map[ln])
        if "}" in code:
            indent = max(0, indent - 1)
        out.append("    " * indent + code)
        if "{" in code:
            indent += 1
    return "\n".join(out) or "(no decompiler output)"


@tool(group="ghidra", params={"addr": {"type": "string"}, "var": {"type": "string"}},
      required=["addr", "var"],
      desc="Summarize how a value is USED in a function: memory accesses (dereferences and the byte "
           "offsets reached through it), array indexing, address arithmetic, scalar arithmetic/"
           "comparison, and which callees receive it (with arg position). Reports observed usage only "
           "— useful for data-flow, struct reconstruction, type inference, and taint analysis.")
def value_usage(ctx, addr: str, var: str) -> dict:
    """Deterministic data-use summary for one decompiler variable (e.g. param_1, local_38, uVar3).
    Reports observed usage facts only — the caller does any interpretation."""
    var = (var or "").strip()
    if not var:
        return {"error": "empty var"}
    _NOT_CALL = {"for", "while", "if", "switch", "return", "sizeof", "do",
                 ctx.resolve_func(addr)}                  # C keywords + the function's own name
    dec = decompile(ctx, addr)
    if not isinstance(dec, str) or dec.startswith("(no"):
        return {"error": f"no decompilation for {addr}"}
    v = re.escape(var)
    bound = rf"(?<![\w]){v}(?![\w])"                       # the var as a whole token
    # DISAMBIGUATION: if `var` appears NOWHERE in the decompilation it is not a decompiler
    # identifier (a common failure: querying a raw register `rdi` instead of the decompiler's
    # `param_1`). Returning an empty "no usage observed" here silently starves the caller and
    # makes it conclude the variable is unused. Instead, surface the ACTUAL identifiers and, for a
    # register, its calling-convention parameter — turning a dead end into a self-correcting hint.
    if not re.search(bound, dec):
        avail = sorted(set(re.findall(
            r"\b((?:param_|local_|[a-z]{1,3}Var|[a-z]{1,4}Stack|in_|unaff_|extraout_|uStack_|"
            r"iStack_|acStack_|auStack_)\w+)\b", dec)))
        _REG2PARAM = {"rdi": "param_1", "edi": "param_1", "rsi": "param_2", "esi": "param_2",
                      "rdx": "param_3", "edx": "param_3", "rcx": "param_4", "ecx": "param_4",
                      "r8": "param_5", "r8d": "param_5", "r9": "param_6", "r9d": "param_6"}
        hint = (f"'{var}' is not a decompiler variable in this function. Use one of the identifiers "
                f"that actually appear below.")
        mapped = _REG2PARAM.get(var.lower())
        if mapped and re.search(rf"(?<![\w]){mapped}(?![\w])", dec):
            hint = (f"'{var}' is a raw register; the decompiler names it '{mapped}' "
                    f"(x86-64 calling convention). Re-query with var='{mapped}'.")
        return {"error": f"variable '{var}' not found", "hint": hint,
                "available_vars": avail[:40]}
    offsets, scalar_ops, passed_to, evidence = set(), [], [], []
    deref = indexed = ptr_arith = False
    off_re   = re.compile(rf"{bound}\s*\+\s*(0x[0-9a-fA-F]+|\d+)")          # var + N
    derefN   = re.compile(rf"\*\s*\([^()]*\)\s*\(\s*{bound}\s*\+\s*(0x[0-9a-fA-F]+|\d+)\s*\)")  # *(T*)(var + N)
    deref0   = re.compile(rf"\*\s*\(?[^()]*\)?\(?\s*{bound}\s*\)?(?![\w\[])")                    # *var / *(T*)var
    idx_re   = re.compile(rf"{bound}\s*\[\s*([^\]]*)\]")                    # var[ idx ]
    cmp_re   = re.compile(rf"{bound}\s*(==|!=|<=|>=|<|>|>>|<<|&|\||%|\^)")  # used AS A VALUE
    call_re  = re.compile(r"\b([A-Za-z_]\w*)\s*\(([^()]*)\)")
    for raw in dec.splitlines():
        l = raw.strip()
        if not re.search(bound, l):
            continue
        evidence.append(l[:100])
        for m in derefN.finditer(l):
            deref = True; offsets.add(int(m.group(1), 0))
        if deref0.search(l):
            deref = True; offsets.add(0)
        for m in idx_re.finditer(l):
            indexed = True; deref = True
            g = m.group(1).strip()
            if re.fullmatch(r"0x[0-9a-fA-F]+|\d+", g):
                offsets.add(int(g, 0))
        if off_re.search(l):
            ptr_arith = True
        if cmp_re.search(l) and not derefN.search(l) and not deref0.search(l):
            scalar_ops.append(l[:90])
        for m in call_re.finditer(l):
            callee, args = m.group(1), m.group(2)
            if callee == var or callee in _NOT_CALL:      # skip keywords / the var itself
                continue
            for ai, a in enumerate(x.strip() for x in args.split(",")):
                if re.search(bound, a):
                    passed_to.append({"callee": callee, "arg": ai + 1,
                                      "addr_of": a.lstrip().startswith("&")})
    offs = sorted(offsets)
    # FACTUAL recap of observed usage only — no type verdict; the caller interprets.
    parts = []
    if deref:
        parts.append(f"dereferenced at offset(s) {[hex(o) for o in offs]}" + (" via indexing" if indexed else ""))
    if ptr_arith:
        parts.append("address arithmetic (var + N)")
    if scalar_ops:
        parts.append(f"{len(scalar_ops)} scalar arithmetic/comparison use(s) with no dereference")
    if passed_to:
        parts.append("passed to " + ", ".join(sorted({f"{p['callee']}(arg{p['arg']})" for p in passed_to})))
    summary = "; ".join(parts) or "no dereference, arithmetic, or call usage observed in this function"
    return {"var": var, "dereferenced": deref, "access_offsets": [hex(o) for o in offs],
            "indexed": indexed, "address_arith": ptr_arith,
            "scalar_ops": scalar_ops[:6], "passed_to": passed_to[:8],
            "evidence": evidence[:12], "summary": summary}


@tool(group="ghidra", params={"addr": {"type": "string"}}, required=["addr"],
      desc="Control-flow graph of the function at addr (blocks + jump/fail edges).")
def cfg(ctx, addr: str) -> dict:
    name = ctx.resolve_func(addr)
    cfgs = ctx.retrieve_oid("mcp_control_flow_graph") or {}
    func = None
    for _, c in cfgs.items():
        if isinstance(c, dict) and c.get("name") == name:
            func = c
            break
    if func is None:
        return {}
    nodes = func.get("nodes", {})
    edges = {}
    for k, v in (func.get("edges", {}) or {}).items():
        try:
            edges[int(k)] = [int(d) for d in v]
        except (ValueError, TypeError):
            continue
    blocks = []
    for node_off, instrs in nodes.items():
        n_int = int(node_off)
        offs = sorted((int(o) for o in instrs), key=int)
        va = ctx.off_to_vaddr(n_int)
        blk = {"addr": hex(va) if va is not None else str(n_int)}
        last = offs[-4:] if offs else []
        blk["last_ops"] = [instrs[str(o)] if str(o) in instrs else instrs.get(o) for o in last]
        dests = edges.get(n_int, [])
        last_off = offs[-1] if offs else n_int
        if len(dests) == 1:
            jv = ctx.off_to_vaddr(dests[0])
            blk["jump"] = hex(jv) if jv is not None else str(dests[0])
        elif len(dests) >= 2:
            seq = sorted([d for d in dests if d > last_off])
            fail_raw = seq[0] if seq else dests[0]
            jump_raw = next((d for d in dests if d != fail_raw), dests[0])
            fv, jv = ctx.off_to_vaddr(fail_raw), ctx.off_to_vaddr(jump_raw)
            blk["jump"] = hex(jv) if jv is not None else str(jump_raw)
            blk["fail"] = hex(fv) if fv is not None else str(fail_raw)
        blocks.append(blk)
    va0 = ctx.off_to_vaddr(int(min(nodes, key=int))) if nodes else None
    return {"name": name, "addr": hex(va0) if va0 is not None else None, "blocks": blocks}


@tool(group="ghidra", params={"root": {"type": "string"}, "max_funcs": {"type": "integer"}},
      desc="Call graph from root (function -> direct callees).")
def callgraph(ctx, root: str = "main", max_funcs: int = 24) -> str:
    g = ctx._callgraph()
    if g is None or nx is None:
        return "(call graph unavailable)"
    start = ctx.resolve_func(root)
    if start not in g:
        start = "main" if "main" in g else (next(iter(g.nodes), None))
    if start is None:
        return "(no functions in call graph)"
    seen, lines, frontier = set(), [], [(start, 0)]
    while frontier and len(seen) < max_funcs:
        nm, depth = frontier.pop(0)
        if nm in seen:
            continue
        seen.add(nm)
        try:
            raw_callees = list(g.successors(nm))
        except Exception:  # noqa: BLE001
            raw_callees = []
        callees = [ctx.clean_name(c) for c in raw_callees]
        lines.append(f"{ctx.clean_name(nm)} -> " + (", ".join(callees[:20]) if callees else "(no calls)"))
        if depth < 2:
            for c in raw_callees:
                if c not in seen and c in g:
                    frontier.append((c, depth + 1))
    return "\n".join(lines)


@tool(group="ghidra", params={"addr": {"type": "string"}}, required=["addr"],
      desc="Callers of a function (or call sites of an imported libc fn).")
def xrefs_to(ctx, addr: str) -> list:
    if ctx.is_import(addr):                              # imported libc fn -> call sites of its PLT stub
        stub = ctx.import_plt_stub(addr)
        if stub is not None:
            return [{"from": r["from"], "type": "call", "fcn": r["fcn"]}
                    for r in ctx.code_refs_to(stub)]
        return []
    name = ctx.resolve_func(addr)
    _v, start_by_name, _ = ctx._name_maps()
    tgt_off = start_by_name.get(name)
    cmap = ctx._call_mapping()
    out = []
    if isinstance(cmap, dict) and tgt_off is not None:
        off_to_name = {start_by_name[n]: n for n in start_by_name}
        for foff, rel in cmap.items():
            cf = rel.get("calls_to", {}) if isinstance(rel, dict) else {}
            if any(int(k) == tgt_off for k in cf):
                cva = ctx.off_to_vaddr(int(foff))
                out.append({"from": hex(cva) if cva is not None else str(foff),
                            "type": "call", "fcn": off_to_name.get(int(foff), str(foff))})
    if not out:
        g = ctx._callgraph()
        if g is not None and nx is not None:
            try:
                for caller in g.predecessors(name):
                    out.append({"from": "", "type": "call", "fcn": ctx.clean_name(caller)})
            except Exception:  # noqa: BLE001
                pass
    return out


@tool(group="ghidra", params={"addr": {"type": "string"}, "limit": {"type": "integer"}},
      required=["addr"],
      desc="Instructions that reference an address (string/global/vaddr) — who USES it.")
def references_to(ctx, addr: str, limit: int = 256) -> list:
    s = str(addr).strip()
    try:
        target = int(s, 0)
    except ValueError:
        try:
            target = int(s, 16)
        except ValueError:                              # a name: defined function OR imported libc fn
            vaddr_by_name, _, _ = ctx._name_maps()
            target = vaddr_by_name.get(ctx.resolve_func(s))
            if target is None and ctx.is_import(s):     # import -> references to its PLT stub = call sites
                target = ctx.import_plt_stub(s)
            if target is None:
                return [{"error": f"could not interpret '{addr}' as an address or known symbol"}]
    return ctx.code_refs_to(target, limit)


def _parse_stack_off(o):
    """Parse a stack offset given as '-0x40', '0xfffffffffffffff0', or '-64' -> signed int."""
    s = str(o).strip()
    try:
        v = int(s, 0)
    except ValueError:
        try:
            v = int(s, 16)
        except ValueError:
            return None
    if v >= (1 << 63):
        v -= (1 << 64)
    return v


# x86-64 SysV: the question gives a register variable as a Ghidra register-space offset; map it to the
# argument register and its 1-based position.
_ARGREGS = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
_REGOFF_TO_REG = {0x38: "rdi", 0x30: "rsi", 0x10: "rdx", 0x08: "rcx", 0x80: "r8", 0x88: "r9"}
_REG_ALIASES = {
    "rdi": {"rdi", "edi", "di", "dil"}, "rsi": {"rsi", "esi", "si", "sil"},
    "rdx": {"rdx", "edx", "dx", "dl"},  "rcx": {"rcx", "ecx", "cx", "cl"},
    "r8":  {"r8", "r8d", "r8w", "r8b"}, "r9":  {"r9", "r9d", "r9w", "r9b"},
    "rax": {"rax", "eax", "ax", "al"},
}
_ALIAS_TO_BASE = {a: b for b, al in _REG_ALIASES.items() for a in al}


@tool(group="ghidra", params={"addr": {"type": "string"}, "reg": {"type": "string"}},
      required=["addr", "reg"],
      desc="How a REGISTER PARAMETER is used, read from the ASSEMBLY only: where the prologue spills "
           "it, every access to that home slot, whether the value is dereferenced (and at which byte "
           "offsets), whether it is used in address arithmetic, and which callees receive it. Give the "
           "register-space offset from the question (e.g. \"0x38\") or a name (\"rdi\"). "
           "`stack_var` does not work for registers; use this.")
def register_usage(ctx, addr: str, reg: str) -> dict:
    """Assembly-side counterpart to `value_usage`, which reads the DECOMPILATION and therefore cannot
    be given to the assembly-lens worker without collapsing the two-lens split. Everything here comes
    from the instruction stream.

    Method: find the prologue store of the argument register into its home stack slot, then follow the
    value linearly — a `mov <r>, [home]` makes <r> hold it until <r> is redefined, and any `[<r>]` /
    `[<r>+N]` memory operand while tracked is a DEREFERENCE (i.e. the value is a pointer). Linear and
    intra-procedural: no branch merging, so a use only reachable on another path can be missed. Reports
    observed facts; it does not name a type."""
    name = ctx.resolve_func(addr)
    info = ctx._fext().get(name)
    if not isinstance(info, dict) or not info.get("instructions"):
        return {"error": f"no function at {addr}; try list_functions"}
    r = str(reg or "").strip().lower()
    if r.startswith("param_"):
        try:
            r = _ARGREGS[int(r.split("_")[1]) - 1]
        except (ValueError, IndexError):
            return {"error": f"could not map {reg!r} to an argument register"}
    elif r.startswith("0x") or r.isdigit():
        try:
            r = _REGOFF_TO_REG[int(r, 16)]
        except (ValueError, KeyError):
            return {"error": f"register offset {reg!r} is not a SysV argument register",
                    "hint": f"integer arguments live at {', '.join(hex(k) for k in _REGOFF_TO_REG)}"}
    r = _ALIAS_TO_BASE.get(r, r)
    if r not in _ARGREGS:
        return {"error": f"{reg!r} is not an x86-64 SysV argument register"}
    argpos = _ARGREGS.index(r) + 1

    insns = info["instructions"]
    keys = sorted(insns, key=lambda o: int(o))
    delta, has_rbp = _frame_delta(insns, keys)
    callmap = _callsite_names(ctx, name)
    alias = _REG_ALIASES[r]
    va = lambda k: ctx.off_to_vaddr(int(k))

    # 1. the prologue spill: mov [rbp-N], <argreg>
    home = None
    for k in keys[:24]:
        m = re.search(r"mov\s+(?:qword|dword|word|byte)?\s*ptr\s*\[rbp \+ (-?0x[0-9a-fA-F]+)\]\s*,\s*(\w+)",
                      insns[k])
        if m and m.group(2).lower() in alias:
            home = int(m.group(1), 16)
            break

    out = {"register": r, "arg_position": argpos,
           "home_slot": None, "accesses": [], "dereferenced": False,
           "access_offsets": [], "address_arith": False, "passed_to": [], "evidence": [],
           "stride_arith": False, "strides": []}
    if home is None:
        out["summary"] = (f"{r} is never spilled to a stack slot in the prologue — it is consumed "
                          f"directly in registers (or moved via another register, e.g. "
                          f"`mov eax,esi` then a store from `al`). Read the disassembly around the "
                          f"entry point; this tool cannot follow it.")
        return out
    out["home_slot"] = (f"[rbp + {'-' if home < 0 else ''}0x{abs(home):x}]"
                        + (f" (question offset {'-' if home - delta < 0 else ''}0x{abs(home - delta):x})"
                           if has_rbp else ""))

    # 2. follow the value over the CONTROL-FLOW GRAPH, not the instruction listing.
    #
    # A linear scan cannot do this. The `if (p == NULL) p = &default;` idiom compiles to two blocks
    # that are ADJACENT IN THE LISTING but on MUTUALLY EXCLUSIVE PATHS: `mov rax,[home]` then, three
    # bytes later, `lea rax,[default]`. A text scan sees the second as a redefinition and drops the
    # value, missing every use after the join -- reporting INCONCLUSIVE (or, worse, "scalar") for a
    # pointer. Observed on mv/set_char_quoting param_1, GT `quoting_options *`.
    #
    # This is a standard forward MAY-analysis: state is the set of registers that MAY hold the
    # parameter, transfer is per instruction, and control-flow joins take the UNION, so a value
    # reaching a join on any path is still tracked through it. Iterated to a fixed point with a
    # worklist, so loops converge. MAY (not MUST) means a use is reported when the value could reach
    # it on SOME path -- the safe direction here, since missing a dereference yields a wrong scalar
    # answer while an extra one only widens the evidence.
    cfgs = ctx.retrieve_oid("mcp_control_flow_graph") or {}
    func = next((c for c in cfgs.values()
                 if isinstance(c, dict) and c.get("name") == name), None)
    blocks, succ = {}, {}
    if isinstance(func, dict) and func.get("nodes"):
        for boff, ins in func["nodes"].items():
            blocks[int(boff)] = sorted((int(o) for o in ins), key=int)
        for k, v in (func.get("edges") or {}).items():
            try:
                succ[int(k)] = [int(d) for d in v]
            except (ValueError, TypeError):
                pass
    if not blocks:                                   # no CFG: fall back to one straight-line block
        blocks = {int(keys[0]): [int(k) for k in keys]}
        succ = {}
    out["analysis"] = "cfg-dataflow" if func else "linear (no CFG available)"
    preds = {b: [] for b in blocks}
    for b, ds in succ.items():
        for d in ds:
            if d in preds:
                preds[d].append(b)

    homepat = f"[rbp + {'-' if home < 0 else ''}0x{abs(home):x}]"
    offs, ev = set(), []
    entry = min(blocks)

    def step(state, t, k):
        """Transfer one instruction. Returns the new state; records uses as a side effect."""
        st = set(state)
        # USE first — a use in this instruction refers to the value BEFORE any redefinition here
        for tr in sorted(st):
            for a in _REG_ALIASES.get(tr, {tr}):
                d = re.search(rf"ptr\s*\[{a}(?:\s*\+\s*(0x[0-9a-fA-F]+))?\]", t)
                if d:
                    out["dereferenced"] = True
                    offs.add(d.group(1) or "0x0")
                    ev.append(f"{hex(va(k))}: {t}")
                if re.search(rf"lea\s+\w+\s*,\s*\[{a}(?:\s*\+\s*0x[0-9a-fA-F]+)?\]", t):
                    out["address_arith"] = True
                    ev.append(f"{hex(va(k))}: {t}")
        cm = re.search(r"\bcall\s+(0x[0-9a-fA-F]+)", t)
        if cm and (st & set(_ARGREGS)):
            tgt = callmap.get(int(cm.group(1), 16)) or ctx.resolve_func(cm.group(1))
            for tr in sorted(st & set(_ARGREGS)):
                rec = {"callee": str(tgt), "arg_position": _ARGREGS.index(tr) + 1}
                if rec not in out["passed_to"]:
                    out["passed_to"].append(rec)
            st -= set(_ARGREGS)                      # the call consumes the argument registers
            return st
        # GEN: a load from the home slot, or a copy of a tracked register
        m = re.search(rf"mov\s+(\w+)\s*,\s*(?:qword|dword|word|byte)?\s*ptr\s*{re.escape(homepat)}", t)
        if m:
            st.add(_ALIAS_TO_BASE.get(m.group(1).lower(), m.group(1).lower()))
            return st
        mv = re.match(r"\s*mov\s+(\w+)\s*,\s*(\w+)\s*$", t)
        if mv:
            src = _ALIAS_TO_BASE.get(mv.group(2).lower(), mv.group(2).lower())
            dst = _ALIAS_TO_BASE.get(mv.group(1).lower(), mv.group(1).lower())
            if src in st:
                st.add(dst)
                return st
        # KILL: any other definition of a tracked register
        w = re.match(r"\s*(?:mov|lea|add|sub|xor|and|or|shl|shr|movzx|movsx|imul|pop)\s+(\w+)\s*,?", t)
        if w:
            st.discard(_ALIAS_TO_BASE.get(w.group(1).lower(), w.group(1).lower()))
        return st

    IN = {b: set() for b in blocks}
    # Seed the worklist with EVERY block, not just the entry: propagating only on change means a block
    # whose predecessor produces an empty state is never enqueued, so most of the function is never
    # visited at all. Every block must be transferred at least once; the change-propagation below then
    # drives it to a fixed point.
    work = sorted(blocks, reverse=True)
    seen_iters = 0
    while work and seen_iters < 500:                 # bounded; converges in a few passes in practice
        seen_iters += 1
        b = work.pop()
        st = set(IN[b])
        for k in blocks[b]:
            st = step(st, insns[str(k)] if str(k) in insns else insns.get(k, ""), k)
        for d in succ.get(b, []):
            if d in IN and not st <= IN[d]:
                IN[d] |= st
                work.append(d)
    for k in sorted({k for blk in blocks.values() for k in blk}):
        t = insns[str(k)] if str(k) in insns else insns.get(k, "")
        if homepat in t:
            out["accesses"].append(f"{hex(va(k))}: {t}")
            # STRIDE ARITHMETIC on the home slot itself. A dereference is tracked through registers,
            # so a value that is only ever ADVANCED in place -- `add qword ptr [rbp-0x58],0x5` -- was
            # previously invisible and the tool then asserted "consistent with a scalar". That is a
            # confident wrong answer on a walked buffer: measured on basenc/z85_encode param_3, GT
            # `char *`, where the output pointer advances by the 5-byte encoding stride each iteration
            # and every layer downstream (worker, verifier, decompiler_pointer) inherited `long`.
            # An 8-byte slot seeded from a parameter and incremented by a constant is characteristic
            # of pointer walking; report it as EVIDENCE, not as proof -- unlike a dereference it does
            # not establish that the value is an address, only that it is being stepped like one.
            sa = _SLOT_ARITH.search(t)
            # A stride of +-1 is a LOOP COUNTER, not a pointer walk. Measured over 10 binaries: every
            # scalar false positive (`mp_size_t`, `size_t` -- `n--`, `count--`) strides by exactly 1,
            # while every genuine pointer strides by its element size (+-0x8 for `mp_ptr`, +0x4 for
            # `wchar_t *`, +0x5 for z85's packed output). Requiring |stride| >= 2 took precision from
            # ~0.45 to 1.00 on that sample. A `char *` walked one byte at a time is the case this
            # gives up, and it is exactly the case the DEREFERENCE signal already covers -- every such
            # firing in the sample also had `dereferenced: true`.
            if (sa and sa.group(3) == homepat and sa.group(2) == "qword"
                    and abs(int(sa.group(4), 0)) >= 2):
                out["stride_arith"] = True
                st = f"{'-' if sa.group(1) == 'sub' else '+'}{sa.group(4)}"
                if st not in out["strides"]:
                    out["strides"].append(st)
                ev.append(f"{hex(va(k))}: {t}")
    out["evidence"] = ev
    out["access_offsets"] = sorted(offs)
    out["evidence"] = out["evidence"][:8]
    bits = []
    if out["dereferenced"]:
        bits.append(f"dereferenced at offset(s) {out['access_offsets']} -> it holds an ADDRESS")
    if out.get("stride_arith"):
        bits.append(f"advanced in place by a constant stride ({', '.join(out['strides'])}) on its "
                    f"8-byte slot — characteristic of a POINTER being walked through a buffer "
                    f"(evidence, not proof: no dereference was observed through a tracked register)")
    if out["address_arith"]:
        bits.append("used as a base in address arithmetic")
    if out["passed_to"]:
        bits.append("passed to " + ", ".join(f"{p['callee']}(arg {p['arg_position']})"
                                             for p in out["passed_to"][:4]))
    if not bits:
        if out["analysis"].startswith("linear"):
            # The value was loaded into a register that was then redefined on another path (the
            # `cmp [home],0 / jz / mov r,[home] / jmp / lea r,default` idiom). Linear tracking cannot
            # merge branches, so silence here is NOT evidence of a scalar -- saying so would be a
            # confident wrong answer on a pointer (observed on mv/set_char_quoting param_1, GT
            # `quoting_options *`). Report inconclusive and hand back the raw accesses.
            bits.append("INCONCLUSIVE — the value is loaded but the register is redefined on another "
                        "control-flow path, so its uses could not be followed. Read `accesses` and the "
                        "disassembly directly; do NOT infer 'scalar' from this")
        else:
            bits.append("no dereference or call flow observed; the slot is only read/written whole, "
                        "which is consistent with a scalar")
    out["summary"] = "; ".join(bits)
    return out


# --- struct-shape analysis (deterministic; oracle-only, NOT published to any agent) ---------------
# Ghidra, Binary Ninja and Hex-Rays all render a linked-list node parameter as a pointer to a
# PRIMITIVE (`undefined4 *`, `int32_t *`, `unsigned int *`) because they never assemble the observed
# field accesses into an aggregate. The accesses themselves are right there in the instruction
# stream: a load at `[p + N]` of a given operand width IS a field of width N, and a field whose
# loaded value flows back into p's own home slot IS a self-reference (the `next` of a linked list).
# This reports those observations only -- offsets, widths, self-references -- and names no C type;
# the type-recovery task renders them (keeping this layer task-agnostic).
# `add qword ptr [rbp + -0x58],0x5` -- arithmetic performed ON a stack slot rather than through
# a register. Used by `register_usage` to detect a pointer that is stepped but never
# dereferenced through a register it tracks.
_SLOT_ARITH = re.compile(
    r"\b(add|sub)\s+(qword|dword|word|byte)\s+ptr\s*(\[rbp \+ -?0x[0-9a-fA-F]+\])\s*,\s*"
    r"(0x[0-9a-fA-F]+|\d+)\b")

_SIZE_KW = {"byte": 1, "word": 2, "dword": 4, "qword": 8}
_LOAD_FIELD = re.compile(
    r"mov\s+(\w+)\s*,\s*(byte|word|dword|qword)\s*ptr\s*\[(\w+)(?:\s*\+\s*(0x[0-9a-fA-F]+))?\]")
_STORE_SLOT = re.compile(
    r"mov\s+(?:byte|word|dword|qword)?\s*ptr\s*\[rbp \+ (-?0x[0-9a-fA-F]+)\]\s*,\s*(\w+)")


@tool(group="ghidra", params={"addr": {"type": "string"}, "reg": {"type": "string"}},
      required=["addr", "reg"],
      desc="Observed aggregate shape behind an argument register: field offsets, widths, "
           "self-references, and stack slots aliasing a field.")
def struct_shape(ctx, addr: str, reg: str) -> dict:
    """Field offsets/widths reached through an argument register, plus self-reference detection."""
    name = ctx.resolve_func(addr)
    info = ctx._fext().get(name)
    if not isinstance(info, dict) or not info.get("instructions"):
        return {"error": f"no function at {addr}"}
    r = str(reg or "").strip().lower()
    if r.startswith("param_"):
        try:
            r = _ARGREGS[int(r.split("_")[1]) - 1]
        except (ValueError, IndexError):
            return {"error": f"could not map {reg!r} to an argument register"}
    elif r.startswith("0x") or r.isdigit():
        try:
            r = _REGOFF_TO_REG[int(r, 16)]
        except (ValueError, KeyError):
            return {"error": f"register offset {reg!r} is not a SysV argument register"}
    r = _ALIAS_TO_BASE.get(r, r)
    if r not in _ARGREGS:
        return {"error": f"{reg!r} is not an x86-64 SysV argument register"}

    insns = info["instructions"]
    keys = sorted(insns, key=lambda o: int(o))
    delta, has_rbp = _frame_delta(insns, keys)
    alias = _REG_ALIASES[r]
    txt = lambda k: insns[str(k)] if str(k) in insns else insns.get(k, "")

    home = None                                        # the prologue spill slot for this parameter
    for k in keys[:24]:
        m = re.search(r"mov\s+(?:qword|dword|word|byte)?\s*ptr\s*\[rbp \+ (-?0x[0-9a-fA-F]+)\]\s*,\s*(\w+)",
                      txt(k))
        if m and m.group(2).lower() in alias:
            home = int(m.group(1), 16)
            break
    out = {"register": r, "arg_position": _ARGREGS.index(r) + 1, "home_slot_qoff": None,
           "fields": {}, "self_ref_offsets": [], "alias_slots": {}, "is_aggregate": False,
           "evidence": []}
    if home is None:
        out["summary"] = f"{r} is never spilled to a stack slot; shape not followable here"
        return out
    out["home_slot_qoff"] = hex(home - delta) if has_rbp else hex(home)

    # Same forward MAY-analysis over the CFG as `register_usage`: which registers may hold the
    # parameter. Union at joins, worklist to a fixed point, every block seeded so none is skipped.
    cfgs = ctx.retrieve_oid("mcp_control_flow_graph") or {}
    func = next((c for c in cfgs.values() if isinstance(c, dict) and c.get("name") == name), None)
    blocks, succ = {}, {}
    if isinstance(func, dict) and func.get("nodes"):
        for boff, ins in func["nodes"].items():
            blocks[int(boff)] = sorted((int(o) for o in ins), key=int)
        for k, v in (func.get("edges") or {}).items():
            try:
                succ[int(k)] = [int(d) for d in v]
            except (ValueError, TypeError):
                pass
    if not blocks:
        blocks, succ = {int(keys[0]): [int(k) for k in keys]}, {}
    homepat = f"[rbp + {'-' if home < 0 else ''}0x{abs(home):x}]"

    def step(state, t):
        st = set(state)
        if re.search(rf"mov\s+(\w+)\s*,\s*(?:qword|dword|word|byte)?\s*ptr\s*{re.escape(homepat)}", t):
            m = re.search(rf"mov\s+(\w+)\s*,", t)
            st.add(_ALIAS_TO_BASE.get(m.group(1).lower(), m.group(1).lower()))
            return st
        mv = re.match(r"\s*mov\s+(\w+)\s*,\s*(\w+)\s*$", t)
        if mv:
            src = _ALIAS_TO_BASE.get(mv.group(2).lower(), mv.group(2).lower())
            dst = _ALIAS_TO_BASE.get(mv.group(1).lower(), mv.group(1).lower())
            if src in st:
                st.add(dst)
                return st
        w = re.match(r"\s*(?:mov|lea|add|sub|xor|and|or|shl|shr|movzx|movsx|imul|pop)\s+(\w+)\s*,?", t)
        if w:
            st.discard(_ALIAS_TO_BASE.get(w.group(1).lower(), w.group(1).lower()))
        return st

    IN = {b: set() for b in blocks}
    work, guard = sorted(blocks, reverse=True), 0
    while work and guard < 500:
        guard += 1
        b = work.pop()
        st = set(IN[b])
        for k in blocks[b]:
            st = step(st, txt(k))
        for d in succ.get(b, []):
            if d in IN and not st <= IN[d]:
                IN[d] |= st
                work.append(d)

    # Replay at the fixed point, recording field accesses and where their values are stored.
    fields, selfrefs, aliases_raw = {}, set(), {}
    for b in sorted(blocks):
        st, fv = set(IN[b]), {}                        # fv: register -> field offset it now holds
        for k in blocks[b]:
            t = txt(k)
            lm = _LOAD_FIELD.search(t)
            if lm and _ALIAS_TO_BASE.get(lm.group(3).lower(), lm.group(3).lower()) in st:
                off = int(lm.group(4), 16) if lm.group(4) else 0
                fields[off] = max(fields.get(off, 0), _SIZE_KW[lm.group(2)])
                fv[_ALIAS_TO_BASE.get(lm.group(1).lower(), lm.group(1).lower())] = off
                out["evidence"].append(f"{hex(ctx.off_to_vaddr(int(k)))}: {t}")
            sm = _STORE_SLOT.search(t)
            if sm:
                src = _ALIAS_TO_BASE.get(sm.group(2).lower(), sm.group(2).lower())
                if src in fv:
                    soff = int(sm.group(1), 16)
                    if soff == home:                   # field value flows back into p -> recursive
                        selfrefs.add(fv[src])
                    else:
                        aliases_raw[soff] = fv[src]
            st = step(st, t)

    # Second hop: at -O0 the recursion is rarely register-to-register. `nxt = n->next` stores the
    # field into its OWN slot, and the loop then does `n = nxt` -- so the field reaches p's home slot
    # via that local. Follow slot -> register -> home to catch it; without this a linked-list `next`
    # is reported as a plain integer field of pointer width rather than a self-reference.
    for b in sorted(blocks):
        sv = {}                                        # register -> field offset, loaded via a slot
        for k in blocks[b]:
            t = txt(k)
            lm = re.search(r"mov\s+(\w+)\s*,\s*(?:qword|dword|word|byte)?\s*ptr\s*"
                           r"\[rbp \+ (-?0x[0-9a-fA-F]+)\]", t)
            if lm and int(lm.group(2), 16) in aliases_raw:
                sv[_ALIAS_TO_BASE.get(lm.group(1).lower(), lm.group(1).lower())] = \
                    aliases_raw[int(lm.group(2), 16)]
            sm = _STORE_SLOT.search(t)
            if sm and int(sm.group(1), 16) == home:
                src = _ALIAS_TO_BASE.get(sm.group(2).lower(), sm.group(2).lower())
                if src in sv:
                    selfrefs.add(sv[src])
    out["fields"] = {hex(o): w for o, w in sorted(fields.items())}
    out["self_ref_offsets"] = [hex(o) for o in sorted(selfrefs)]
    out["alias_slots"] = {(hex(k - delta) if has_rbp else hex(k)): hex(v)
                          for k, v in sorted(aliases_raw.items())}
    # One field at offset 0 is just `T *`; an aggregate needs two distinct fields or a self-reference.
    out["is_aggregate"] = bool(len(fields) >= 2 or selfrefs)
    out["evidence"] = out["evidence"][:8]
    out["summary"] = ("no field access observed" if not fields else
                      f"fields at {sorted(out['fields'])}"
                      + (f", self-referential at {out['self_ref_offsets']}" if selfrefs else ""))
    return out


@tool(group="ghidra", params={"addr": {"type": "string"}, "offset": {"type": "string"}},
      required=["addr"],
      desc="Stack slot for a CFA-style frame offset + the instructions accessing it "
           "(omit offset to list all slots).")
def stack_var(ctx, addr: str, offset: str = "") -> dict:
    name = ctx.resolve_func(addr)
    info = ctx._fext().get(name)
    if not isinstance(info, dict) or not info.get("instructions"):
        return {"error": f"no function at {addr}; try list_functions"}
    insns = info["instructions"]
    keys = sorted(insns, key=lambda o: int(o))
    # frame-base delta: rbp = sp@entry - delta (bytes pushed before `mov rbp,rsp`) — a coordinate
    # mechanic, analogous to the vaddr/file-offset base resolution.
    delta, has_rbp_frame = 0, False
    for k in keys[:16]:
        t = insns[k]
        if re.match(r"\s*push\b", t):
            delta += 8
        if re.search(r"\bmov\b\s+rbp\s*,\s*rsp\b", t):
            has_rbp_frame = True
            break
    slots = {}                                    # rbp_off(int) -> [raw accessing instructions]
    for k in keys:
        t = insns[k]
        for m in re.finditer(r"\[rbp\s*\+\s*(-?0x[0-9a-fA-F]+)\]", t):
            ro = int(m.group(1), 16)
            va = ctx.off_to_vaddr(int(k))
            slots.setdefault(ro, []).append(f"{hex(va) if va is not None else k}: {t}")
    if not has_rbp_frame:
        return {"name": name, "frame_delta": delta,
                "note": "no rbp frame in prologue; accesses are rsp-relative",
                "rbp_slots": [hex(o) for o in sorted(slots)]}
    if offset not in ("", None):
        want = _parse_stack_off(offset)
        if want is None:
            return {"error": f"could not parse offset {offset!r}"}
        ro = want + delta
        acc = slots.get(ro)
        return {"query_offset": hex(want), "frame_delta": delta, "rbp_offset": hex(ro),
                "found": bool(acc), "accesses": acc or []}
    return {"name": name, "frame_delta": delta,
            "slots": [{"offset": hex(ro - delta), "rbp_offset": hex(ro), "accesses": slots[ro][:6]}
                      for ro in sorted(slots)]}


@tool(group="ghidra", params={},
      desc="Indirect call/jmp sites + their recorded destinations.")
def indirect_branches(ctx) -> list:
    gd = ctx._ghidra_data()
    ic = gd.get("indirect_control", {}) if isinstance(gd, dict) else {}
    out = []
    for off, v in (ic or {}).items():
        va = ctx.off_to_vaddr(int(off))
        dests = []
        for d in (v.get("values", []) if isinstance(v, dict) else []):
            try:
                dv = ctx.off_to_vaddr(int(str(d), 0))
                dests.append(hex(dv) if dv is not None else str(d))
            except ValueError:
                dests.append(str(d))
        out.append({"addr": hex(va) if va is not None else str(off),
                    "inst": v.get("inst") if isinstance(v, dict) else str(v),
                    "ghidra_dests": dests})
    return out
