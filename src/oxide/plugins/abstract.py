from oxide.core import api


def abstract(args, opts):
    oids, invalid = api.valid_oids(args)

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
        instructions = disasm["instructions"]
        function = funcs[f_names[choice]]
        function_insns = {}
        for i in function["instructions"]:
            function_insns[i] = instructions[i]

        print("Analyzing function", f_names[choice],":")
        for i in function_insns:
            print(i,":",function_insns[i]['str'])
        analysis(function_insns)
    return args

def analysis(f):
    """Your code goes here.

        You start with f, which is a dictionary where the keys are offsets and
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
    pass

exports = [abstract]
