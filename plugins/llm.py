""" Plugin: Utility functions for managing truth files.
"""
import torch
import torch.nn as nn
from torch.nn import functional as F
import progress, api

vocab_size = 256
block_size = 64
batch_size = 32
iterations = 10000
torch.manual_seed(1337)


def trainllm(args, opts):
    """
        Train a large language model on bytes from programs passed in.
        Syntax: trainllm <oid_list>
    """
    args, invalid = api.valid_oids(args)
    if not args:
        raise ShellSyntaxError("Must provide an OID.")

    m = BigramLanguageModel(vocab_size)
    optimizer = torch.optim.AdamW(m.parameters(), lr=1e-4)
        
    for oid in args:
        src_type = api.get_field("src_type", oid, "type")
        if "PE" not in src_type:
            continue
        
        raw_data = api.get_field("files", oid, "data")
        
        data = torch.tensor(encode(raw_data), dtype=torch.long)
        for steps in range(iterations):
            xb, yb = get_batch(data)
            logits, loss = m(xb, yb)
            optimizer.zero_grad(set_to_none=True)
            loss.backward()
            optimizer.step()

        print(logits.shape)
        print(loss)


    return args

def generate(args, opts):
    idx = torch.zeros((1,1), dtype=torch.long)
    #print(decode(m.generate(, max_new_tokens=100)[0].tolist()))


exports = [trainllm]

##################### UTILS ############################

# single byte encoding - possibly change to 2-gram encoding in the future
encode = lambda s: [i for i in s]
decode = lambda l: b''.join(l)

def get_batch(data):
    ix = torch.randint(len(data) - block_size, (batch_size,))
    x = torch.stack([data[i:i+block_size] for i in ix])
    y = torch.stack([data[i+1:i+block_size+1] for i in ix])
    return x, y

class BigramLanguageModel(nn.Module):

        def __init__(self, vocab_size):
            super().__init__()
            self.token_embedding_table = nn.Embedding(vocab_size, vocab_size)

        def forward(self, idx, targets):
            logits = self.token_embedding_table(idx) # (B,T,C)

            if targets is None:
                loss = None
            else:
                B, T, C = logits.shape
                logits = logits.view(B*T, C)
                targets = targets.view(B*T)
                loss = F.cross_entropy(logits, targets)
            return logits, loss
        
        def generate(self, idx, max_new_tokens):
            # idx is (B, T) array of indices
            for _ in range(max_new_tokens):
                # get predictions
                logits, loss = self(idx)
                # focus on last time step
                logits = logits[:,-1,:] # becomes (B, C)
                # apply softmax to get probabilities
                probs = F.softmax(logits, dim=-1) # (B, C)
                # sample from distribution
                idx_next = torch.multinomial(probs, num_samples=1) # (B, 1)
                # append sampled index to running sequence
                idx = torch.cat((idx, idx_next), dim=1) # (B, T+1)
            return idx