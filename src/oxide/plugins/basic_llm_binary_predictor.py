# import plugins.llm
import random

from plugins import llm
import api
import torch


encode = llm.encode
decode = llm.decode


def predict_bin(args, opts):
    """
        Takes first file from input, grabs a random 500 byte chunk, and tries to predict the next 500 bytes.
        Prints results out to console.
    """
    try:
        model = llm.model
        print(f"Using: {model}")
        if model is None:
            raise NameError
    except NameError:
        raise ShellSyntaxError("run `trainllm` from `plugin llm` before running this plugin.")

    args, invalid = api.valid_oids(args)
    if not args:
        raise ShellSyntaxError("Must provide an OID.")
    args = api.expand_oids(args)
    oid = args[0]
    raw_data = api.get_field("files", oid, "data")

    block_size = llm.block_size
    data = torch.tensor(encode(raw_data), dtype=torch.long)
    i = random.randint(0, len(data) - 1000)
    x = torch.stack([data[i:i+500]])
    next_data = [int(i) for i in data[i:i+1000]]
    context = x.to(llm.device)

    # context = torch.zeros((512, 512), dtype=torch.long, device='mps')
    print("\n\nINITIAL:\n\n")
    print(x)
    print("\n\nPREDICTED:\n\n")
    print((model.generate(context, max_new_tokens=500)[0].tolist()))
    print("\n\nACTUAL:\n\n")
    print(next_data)
exports = [predict_bin]
