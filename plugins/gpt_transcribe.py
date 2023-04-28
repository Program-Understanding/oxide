from core import api
import os
import json
import sys
try:
    import openai
except ImportError:
    print("OpenAI not installed. Try \"pip3 install openai")
import re

GPT_MODEL = "gpt-3.5-turbo"

# OpenAI ChatGPT Transcriber. Set api_key in .config.txt in order to set the key


def ghidra_transcribe_blocks(args, opts):
    """
        Uses chatGPT API to transcribe basic blocks.
        Syntax: ghidra_transcribe_blocks oid
        Options:
            file - Where to put transcription. Defaults to localstore
            bbsize - Minimum Size of basic block to transcribe. Defaults to 10
            pipe - Where to dump stdout
    """
    try:
        pipe = open(opts['pipe'], "w")
    except KeyError:
        pipe = sys.stdout
    try:
        gpt_key = str(api.config.chatgpt_chatgpt_token)
        openai.api_key = gpt_key
        if gpt_key is None:
            raise ShellSyntaxError("API Key is not set.")
    except Exception as e:
        print(e)

    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")
    valid = api.expand_oids(valid)

    if "bbsize" in opts:
        bbsize = opts["bbsize"]
    else:
        bbsize = 10

    for oid in valid:
        #Block dict: {"Starting Addr" : [[<Addr>][Ins]]}
        block_list = []
        basic_blocks = api.get_field("ghidra_disasm", [oid], "original_blocks")
        disasm = api.get_field("ghidra_disasm", [oid], "instructions")
        funcs = api.get_field("ghidra_disasm", [oid], "functions")
        for entry, bb_info in basic_blocks.items():
            block = []
            if len(bb_info['members']) > bbsize:
                for offset in bb_info["members"]:
                    block.append([offset[0],offset[1]])
                block_list.append(block)
            else:
                continue
        
        transcription = _process_basic_blocks(block_list)
        ## For Debugging
        # with open("test.txt", 'w') as f:
        #     f.write(json.dumps(transcription))
        #     f.write("\n")
        #     f.write(json.dumps(block_list))
        #     f.close()
        print(f"{GPT_MODEL} Transcription for Ghidra-extracted basic blocks greater than {bbsize} for file {_name(oid)}", file = pipe)
        print_table(block_list,transcription, pipe =pipe)


def print_table(bb_info, summary, header_values = ["Offset", "Instruction", "Summary"], pipe = sys.stdout):
    #Find the longest Instruction string

    instruction_strings = [instr[1] for sublist in bb_info for instr in sublist]
    longest_string_length = max(len(instr) for instr in instruction_strings) + 3
    new_line = ""
    header = ""
    output = "|"
    #Create Header
    for hvalue in header_values:
        padding = abs(longest_string_length - len(hvalue)) - (len(header_values))
        left = padding // 2
        right = padding - left
        result = "{}{}{}".format(" " * left, hvalue, " " * right)
        output += result + "|"
    max_row_length = len(output)
    new_line = "=" * (max_row_length) + "\n"
    header += new_line + output + "\n" + new_line
    output = header + "\n"

    #Lambda function for formatting string
    format_value = lambda value, longest_string_length, padding: \
    "|{}{}".format(value, " " * (longest_string_length - padding - len(str(value))))


    def split_summary(text, longest_string_length):
        words = text.split()
        chunks = []
        current_chunk = ""

        for word in words:
            if len(current_chunk) + len(word) + 1 <= longest_string_length:
                if current_chunk != "":
                    current_chunk += " "
                current_chunk += word
            else:
                chunks.append(current_chunk)
                current_chunk = word

        if current_chunk != "":
            chunks.append(current_chunk)

        return chunks

    

    for index, data in enumerate(bb_info):
        #Calculate the number of columns
        overflow = 0
        num_rows = len(data)
        summary_string = summary[index]
        summary_list = split_summary(summary_string, longest_string_length - 3)
        overflow = (len(summary_list) - num_rows)


        while summary_string:
            if len(summary_string) <= longest_string_length:
                summary.append(summary_string)
                break
            else:
                last_space = summary_string[:longest_string_length].rfind(' ')
                if last_space == -1:
                    last_space = longest_string_length
                summary.append(summary_string[:last_space])
                summary_string = summary_string[last_space+1:]
    
        summary_count = 0
        for insn in data:
            offset = insn[0]
            instruction = insn[1]
            output += format_value(offset, longest_string_length, 3)
            output += format_value(instruction, longest_string_length, 3)
            if summary_count < len(summary_list):
                output += format_value(summary_list[summary_count], longest_string_length, 3)
            else:
                output += format_value(" ", longest_string_length, 3)
            output += "|\n"
            summary_count += 1
 
        if overflow > 0:
            for i in range(overflow):
                output += format_value(" ", longest_string_length, 3)
                output += format_value(" ", longest_string_length, 3)
                output += format_value(summary_list[i + summary_count], longest_string_length, 3)
                output += "|\n"
        output += new_line
            

    print(output, file = pipe)


def _process_basic_blocks(basic_blocks, batch_size=8):
    
    responses = []
    system_role = {"role": "system", "content": "You are a helpful assistant, with knowledge of x86 Instructions. You will not enumerate basic blocks when asked, but will simply give a summary. Assume that each basic block you get is part of one program that you have previously transcribed"}
    assistant_role = {"role": "assistant", "content": "These instructions are part of a bigger program. Here are some recent addresses and what other blocks used to get there to inform you of your transcriptions:\n"}
    
    for bb in basic_blocks:
        output = {}
        first_address = ""
        user_role = {"role": "user", "content": "What does this basic block do?:\n"}
        for index, instruction in enumerate(bb):
            user_role['content'] += instruction[1] + "\n"
            if first_address == "":
                first_address = instruction[0]
            #Checks if last instruction is a jump to an address. If so, update assistant.
            if index == len(bb) - 1:
                if check_if_address(instruction[1]):
                    assistant_role['content'] += instruction[1]

        
        input_messages = []
        input_messages.append(system_role)
        input_messages.append(assistant_role)
        input_messages.append(user_role)
        size = len(bb)
        response = openai.ChatCompletion.create(
            model=GPT_MODEL,    
            messages=input_messages,
            max_tokens=3000,
            n=1,
            stop=None,
            temperature=0.5,
            stream=False
        )
        responses.append(response.choices[0].message.content)
    return responses
#Input: {1256: [1270, 'jz  0x001004fa'], 1272: [1272, 'call  rax'], 1274: .... }


#Returns if address is in string
def check_if_address(string):
    pattern = r"\[(0x[\da-fA-F]+)\]"
    match = re.search(pattern, string)
    if match:
        return True
    else:
        return False

def populate_assistant_table(assistant_role, address_dict):
    pass
def _name(oid):
    if api.exists("file_meta", oid):
        return api.get_field("file_meta", oid, "names").pop()

    if api.exists("collections_meta", oid):
        return api.get_colname_from_oid(oid)
    return None

exports = [ghidra_transcribe_blocks]
