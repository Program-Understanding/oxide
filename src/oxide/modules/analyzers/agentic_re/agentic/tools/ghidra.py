"""Ghidra-derived analysis tools (group: ghidra). Thin exposures of ghidra_disasm/
function_extract, mcp_control_flow_graph, call_graph, ghidra_decmap, function_summary,
ghidra_data, call_mapping."""
from __future__ import annotations

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
        idx = keys.index(center)
        hi = min(len(keys), idx + n // 2)
        lo = max(0, hi - n)
        chosen = keys[lo:hi]
        note = (f"(window: instructions {lo}-{hi} of {len(keys)}, centered on the requested address; "
                "disassemble a function name/start for the top)\n")
    elif len(keys) > n:
        chosen = keys[:n]
        note = (f"(first {n} of {len(keys)} instructions; pass an inner address to window there)\n")
    else:
        chosen = keys
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
