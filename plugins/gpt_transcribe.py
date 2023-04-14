from core import api
import os
#OpenAI ChatGPT Transcriber. Set api_key in .config.txt in order to set the key

def ghidra_transcribe_blocks(args, opts):
        valid, invalid = api.valid_oids(args)
        if not valid:
            raise ShellSyntaxError("No valid oids found")
        valid = api.expand_oids(valid)
        gpt_key = None
        try:
            gpt_key = str(api.chatgpt_token)
            if api_key == None:
                raise ShellSyntaxError("API Key is not set.")
        except Exception as e:
            print(e)
        print(gpt_key)

exports = [ghidra_transcribe_blocks]
