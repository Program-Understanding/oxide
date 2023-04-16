import api
import os
# OpenAI ChatGPT Transcriber. Set api_key in .config.txt in order to set the key


def ghidra_transcribe_blocks(args, opts):
    valid, invalid = api.valid_oids(args)
    if not valid:
        raise ShellSyntaxError("No valid oids found")
    valid = api.expand_oids(valid)
    gpt_key = None
    try:
        gpt_key = str(api.config.chatgpt_chatgpt_token)
        if gpt_key is None:
            raise ShellSyntaxError("API Key is not set.")
    except Exception as e:
        print(e)
    print(gpt_key)
    for oid in valid:
        block_dict = {}
        basic_blocks = api.get_field("ghidra_disasm", [oid], "original_blocks")
        disasm = api.get_field("ghidra_disasm", [oid], "instructions")
        funcs = api.get_field("ghidra_disasm", [oid], "functions")
        for entry, bb_info in basic_blocks.items():
            for offset in bb_info["members"]:
                block_dict[entry] = offset
                # print(disasm[offset])
        batched_blocks = _batch_blocks(block_dict.items())
        for batch in batched_blocks:
            messages = [{"role": "user", "content": block} for block in batch]
            completion = openai.Completion.create(
                engine= gpt_model,
                prompt="",
                max_tokens=1024,
                n=1,
                temperature=0.7,
                messages=messages
            )

def _batch_blocks(blocks):
    batched = [blocks[i: i + 16] for i in range(0,len(blocks))]
    return batched


def _analyze(blocks, prompt=None):
    if not prompt:
        prompt = "I am going to give you a dict"


exports = [ghidra_transcribe_blocks]
