import math
def print_table(bb_info, summary):
    def format(string, max_row_length):
        num_columns = 3
        remaining_space = max_row_length - len(string)
        column_width = math.ceil((remaining_space / num_columns) * (max_row_length / len(string)))
        formatted_string = string.format(
            "A".center(column_width),
            "B".center(column_width),
            "C".center(column_width)
        )

        return formatted_string
    header = "| A | B | C |"
    print(format(header, 1000))
    print(header)



          

    # output = ""
    # header = "| Offset | Address | Summary |"
    # max_row_length = len(header)
    # for basic_block in bb_info:
    #     for data in basic_block:
    #         address = data[0]
    #         instruction = data[1]
    #         max_row_length = max(max_row_length, len(f"| {address} | {instruction} |")*2)




summary = ["This basic block sets the value of EBP to zero, moves the value of RDX into R9, pops the value of RSI, moves the value of RSP into RDX, aligns the stack pointer by ANDing it with -0x10, pushes the value of RAX onto the stack, pushes the value of RSP onto the stack, loads the effective address of 0x100720 into R8, loads the effective address of 0x1006b0 into RCX, loads the effective address of 0x100670 into RDI, and calls the function pointed to by the value at memory address 0x00300fe0.", "This basic block loads the memory addresses 0x301010 into the registers RDI and RSI, respectively. It then pushes the value of RBP onto the stack and subtracts the value in RDI from the value in RSI, storing the result in RSI. The current value of RSP is stored in RBP. The next few instructions perform arithmetic operations on RSI to calculate a new value, which is then compared to zero using the \"jz\" instruction. If the result is zero, the program jumps to address 0x001005e0."]
data = [[[1328, "xor  ebp,ebp"], [1330, "mov  r9,rdx"], [1333, "pop  rsi"], [1334, "mov  rdx,rsp"], [1337, "and  rsp,-0x10"], [1341, "push  rax"], [1342, "push  rsp"], [1343, "lea  r8,[0x100720]"], [1350, "lea  rcx,[0x1006b0]"], [1357, "lea  rdi,[0x100670]"], [1364, "call  qword ptr [0x00300fe0]"]], [[1440, "lea  rdi,[0x301010]"], [1447, "lea  rsi,[0x301010]"], [1454, "push  rbp"], [1455, "sub  rsi,rdi"], [1458, "mov  rbp,rsp"], [1461, "sar  rsi,0x3"], [1465, "mov  rax,rsi"], [1468, "shr  rax,0x3f"], [1472, "add  rsi,rax"], [1475, "sar  rsi,0x1"], [1478, "jz  0x001005e0"]], [[1608, "push  rbp"], [1609, "mov  rbp,rsp"], [1612, "mov  dword ptr [rbp + -0xc],0x5"], [1619, "mov  dword ptr [rbp + -0x8],0x6"], [1626, "mov  dword ptr [rbp + -0x4],0x7"], [1633, "mov  edx,dword ptr [rbp + -0xc]"], [1636, "mov  eax,dword ptr [rbp + -0x8]"], [1639, "add  edx,eax"], [1641, "mov  eax,dword ptr [rbp + -0x4]"], [1644, "add  eax,edx"], [1646, "pop  rbp"], [1647, "ret"]], [[1712, "push  r15"], [1714, "push  r14"], [1716, "mov  r15,rdx"], [1719, "push  r13"], [1721, "push  r12"], [1723, "lea  r12,[0x300db8]"], [1730, "push  rbp"], [1731, "lea  rbp,[0x300dc0]"], [1738, "push  rbx"], [1739, "mov  r13d,edi"], [1742, "mov  r14,rsi"], [1745, "sub  rbp,r12"], [1748, "sub  rsp,0x8"], [1752, "sar  rbp,0x3"], [1756, "call  0x001004e8"]]]
print_table(data[:2], summary[:2])