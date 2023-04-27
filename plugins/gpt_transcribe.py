from core import api
import os
import json
import sys
try:
    import openai
except ImportError:
    print("OpenAI not installed. Try \"pip3 install openai")
import re
    

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
                    block.append((offset[0],offset[1]))
                block_list.append(block)
            else:
                continue
            
          

        transcription = _process_basic_blocks(block_list[:2])
        with open("test.txt", 'w') as f:
            f.write(json.dumps(transcription))
            f.write("\n")
            f.write(json.dumps(block_list))
            f.close()
        # print_table(transcription, block_list, pipe)

def _process_basic_blocks(basic_blocks, batch_size=8):
    
    responses = []
    system_role = {"role": "system", "content": "You are a helpful assistant, with knowledge of x86 Instructions. You will not enumerate basic blocks when asked, but will simply give a summary. Assume that each basic block you get is part of one program that you have previously transcribed"}
    assistant_role = {"role": "assistant", "content": "You are to be given a set of instructions which are a basic block of a larger program. Please summarize what these set of instructions do. Here are some recent addresses and what other blocks used to get there to inform you of your transcriptions:\n"}
    
    for bb in basic_blocks:
        output = {}
        first_address = ""
        user_role = {"role": "user", "content": "What does this basic block do?:\n"}
        for instruction in bb:
            # print(instruction[1])
            user_role['content'] += instruction[1] + "\n"
            if first_address == "":
                first_address = instruction[0]
        
        input_messages = []
        input_messages.append(system_role)
        input_messages.append(assistant_role)
        input_messages.append(user_role)
        size = len(bb)
        response = openai.ChatCompletion.create(
            model="gpt-3.5-turbo",    
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

def print_table(basic_blocks, summaries, pipe):
    if len(basic_blocks) != len(summaries):
        print("Error: The lengths of the basic_blocks and summaries lists do not match.")
        return

    # Find the maximum width of the instructions column
    instructions_column_width = max([len(" ".join([str(instruction[0]), instruction[1]])) for block in basic_blocks for instruction in block])

    # Print the table header
    print(f"{'Instructions':<{instructions_column_width}} | Summary")
    print(f"{'-'*instructions_column_width}-+-{'-'*len('Summary')}")

    # Print the table content
    for block, summary in zip(basic_blocks, summaries):
        # Print the first instruction of the block with the summary
        first_instruction = block[0]
        print(f"{' '.join([str(first_instruction[0]), first_instruction[1]]):<{instructions_column_width}} | {summary}")
        
        # Print the rest of the instructions without the summary
        for instruction in block[1:]:
            print(f"{' '.join([str(instruction[0]), instruction[1]]):<{instructions_column_width}} |")
        print()
exports = [ghidra_transcribe_blocks]
