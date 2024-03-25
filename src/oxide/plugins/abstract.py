from oxide.core import api


def abstract(args, opts):
    oids, invalid = api.valid_oids(args)
    oids = set(api.expand_oids(oids))

    for oid in oids:
        name = api.get_field("file_meta", oid, "names")
        file_size = api.get_field("file_meta", oid, "size")
        src_type = api.get_field("src_type", oid, "type")
        print("Generating abstract domain for file:", name.pop())
        print("A", file_size, "byte", src_type, "file.")

        funcs = api.retrieve("function_extract", oid)
        print("Containing the following functions: ")
        f_names = []
        for n,f in enumerate(funcs):
            print(n,f)
            f_names.append(f)
        choice = int(input("Which function do you want to analyze:"))
        if choice < 0 or choice >= len(f_names):
            print("Invalid choice.")
            break
        disasm = api.get_field("disassembly", oid, oid)
        if not "instructions" in disasm:
            print("No instructions found")
            break
        instructions = disasm["instructions"]
        function = funcs[f_names[choice]]
        function_insns = {}
        for i in function["instructions"]:
            function_insns[i] = instructions[i]

        print("Analyzing function", f_names[choice],":")
        analysis(function_insns)
    return args

def analysis(f):
    """You start with f, which is a dictionary where the keys are offsets and
        the values are instructions.  An instruction is a dictionary with a bunch
        of different parts.  It looks like this:
        {'id': 449, 'mnemonic': 'mov', 'address': 1649, 'op_str': 'rbp, rsp',
            'size': 3, 'str': 'mov rbp, rsp', 'groups': [], 'regs_read': [],
            'regs_write': [], 'regs_access': ([], []), 'prefix': [0, 0, 0, 0],
            'opcode': [137, 0, 0, 0], 'rex': 72, 'operand_size': 8, 'modrm': 229,
            'operands':
                {'operand_0': {'type.reg': 'rbp', 'size': 8, 'access': 'write'},
                'operand_1': {'type.reg': 'rsp', 'size': 8, 'access': 'read'}}}

        If you want to print the instruction, you can use the 'str' member.
        'regs_access' is a good place to use to find alocs.
        Play around with some examples to get a better idea what can be there.
    """
    alocs = find_alocs(f)
    print("Alocs: ", alocs)
    domain = {}
    for region in alocs:
        domain[region] = {}
        for loc in alocs[region]:
            domain[region][loc] = "Bottom"

    for i in f:
        print(i,":",f[i]['str'])
        mnem = f[i]["mnemonic"]
        if mnem in ("ldr", "str", "movz"):
            handle_ldr_str_movz(f[i], domain)
        elif mnem in ("mul"):
            handle_mul(f[i], domain)
        else:
            smashed_alocs = alocs_touched(f[i])
            for loc in smashed_alocs:
                for region in domain:
                    if loc in domain[region]:
                        domain[region][loc] = "Top"
        print(domain)
        print()


def find_alocs(f):
    regs = set()
    stack = set()
    for i in f:
        regs.update(f[i]['regs_read'])
        regs.update(f[i]['regs_write'])
        for operand in f[i]['operands']:
            op = f[i]['operands'][operand]
            if 'type.reg' in op:
                regs.add(get_loc(op))
            if 'type.mem' in op:
                stack.add(get_loc(op))
    alocs = {"regs":regs, "stack":stack}
    return alocs

def alocs_touched(i):
    locs = set()
    locs.update(i['regs_write'])
    for operand in i['operands']:
        op = i['operands'][operand]
        locs.add(get_loc(op))
    return locs

def get_loc(operand):
    if "type.reg" in operand:
        loc = operand["type.reg"]
    elif "type.mem" in operand:
        loc = operand["type.mem"]["base"]
        if loc in ('sp','esp','ebp','rsp','rbp'):
            if 'displacement' in operand['type.mem']:
                loc += "+" + str(operand['type.mem']['displacement'])
            else: loc += "+0"
    else:
        loc = None
    return loc

def get_value(operand, domain):
    val = "Top"
    if "type.imm" in operand:
        val = operand["type.imm"]
    if "type.reg" in operand:
        val = domain["regs"][get_loc(operand)]
    if "type.mem" in operand:
        loc = get_loc(operand)
        val = domain["stack"][loc]
    return val

def handle_ldr_str_movz(instr, domain):
    #print(instr)
    op0 = instr['operands']['operand_0']
    op1 = instr['operands']['operand_1']
    if instr['mnemonic'] in ('movz', 'ldr'):
        val = get_value(op1, domain)
        dest = get_loc(op0)
    elif instr['mnemonic'] in ('str'):
        val = get_value(op0, domain)
        dest = get_loc(op1)
    print("Dest: ", dest, ", Value: ", val)
    if dest in domain["regs"]:
        domain["regs"][dest] = val
    elif dest in domain["stack"]:
        domain["stack"][dest] = val

def handle_mul(instr, domain):
    val1 = get_value(instr['operands']['operand_1'], domain)
    val2 = get_value(instr['operands']['operand_2'], domain)
    dest = get_loc(instr['operands']['operand_0'])
    if str(val1) in ("Top") or str(val2) in ("Top"):
        total = "Top"
    elif str(val1) in ("Bottom") or str(val2) in ("Bottom"):
        total = "Bottom"
    else:
        total = val1*val2
    print("Dest: ", dest, ", Value: ", total)
    if dest in domain["regs"]:
        domain["regs"][dest] = total
    elif dest in domain["stack"]:
        domain["stack"][dest] = total


exports = [abstract]
