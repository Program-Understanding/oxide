# Modified from Andrej's Youtube tutorial, based on: https://github.com/karpathy/nanoGPT/blob/master/model.py
'''MIT License

Copyright (c) 2022 Andrej Karpathy

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
'''
'''
Modified for Oxide by Samuel Mulder 2023
'''

""" Plugin: Utility functions for managing truth files.
"""
import time
import math
import torch
import torch.nn as nn
from torch.nn import functional as F
import progress, api

vocab_size = 256
block_size = 64 # number of sequences in parallel
batch_size = 256 # Maximum context length
iterations = 1000
eval_iterations = 100
n_embed = 384 # number of embedding dimensions
learning_rate = 3e-4
n_head = 6
n_layer = 6
dropout = 0.2
if torch.cuda.is_available():
    device = "cuda"
elif torch.backends.mps.is_available() and torch.backends.mps.is_built():
    device = "mps"
else:
    device = 'cpu'
print(f"llm using device: {device}")
model = None


def savellm(args, opts):
    """
        Saves LLM to oxide/<args[0]>.pt
    """
    if len(args) != 1:
        raise ShellSyntaxError("Must provide a single filename.")
    if model is None:
        raise ShellSyntaxError("Must train llm (`trainllm <oid_list>`) before saving.")
    filename = args[0]
    if filename.endswith(".pt"):
        filename = filename[:-3]
    print(f"Saving LLM to {filename}.pt")
    torch.save(model.state_dict(), f"{filename}.pt")

def loadllm(args, opts):
    """
        Loads LLM from oxide/<args[0]>.pt
    """
    global model

    if len(args) != 1:
        raise ShellSyntaxError("Must provide a single filename.")
    filename = args[0]
    if filename.endswith(".pt"):
        filename = filename[:-3]

    model = TransformerModel()
    m = model.to(device)
    model.load_state_dict(torch.load(f"{filename}.pt"))
    model.eval()

def trainllm(args, opts):
    """
        Train a large language model on bytes from programs passed in.
        Syntax: trainllm <oid_list>
    """
    start_time = time.time()
    args, invalid = api.valid_oids(args)
    if not args:
        raise ShellSyntaxError("Must provide an OID.")
    args = api.expand_oids(args)
    global model
    if not model:
        model = TransformerModel()
        m = model.to(device)
    optimizer = torch.optim.AdamW(model.parameters(), lr=learning_rate)

    for oid in args:
        src_type = api.get_field("src_type", oid, "type")
        if "PE" not in src_type and "ELF" not in src_type and "OSX Universal Binary" not in src_type:
            print(src_type)
            continue

        raw_data = api.get_field("files", oid, "data")

        data = torch.tensor(encode(raw_data), dtype=torch.long)
        start_iter_time = time.time()
        for steps in range(iterations):
            if steps % eval_iterations == 0:
                losses = estimate_loss(data)
                print(f"step {steps}/{iterations}: loss {losses:.4f}, time: {time.time() - start_iter_time:0.1f} seconds", end="")
                if steps != 0:
                    print(f" -- (est. time remaining: {(time.time() - start_time) / steps * (iterations - steps) / 60:0.2f} minutes)")
                else:
                    print()
                start_iter_time = time.time()
            xb, yb = get_batch(data)
            logits, loss = model(xb, yb)
            optimizer.zero_grad(set_to_none=True)
            loss.backward()
            optimizer.step()

        total_time = time.time() - start_time
        print(logits.shape)
        print(loss)
        print(f"Total time to train: {float(total_time) / 60:0.2f} minutes")
        print("Save LLM model to a file using: `savellm <filename>`")
    return args

def generate(args, opts):
    idx = torch.zeros((1,1), dtype=torch.long)
    #print(decode(m.generate(, max_new_tokens=100)[0].tolist()))


exports = [trainllm, loadllm, savellm]

##################### UTILS ############################

# single byte encoding - possibly change to 2-gram encoding in the future
encode = lambda s: [i for i in s]
decode = lambda l: b''.join(l)

def new_gelu(x):
    """
    Implementation of the GELU activation function currently in Google BERT repo (identical to OpenAI GPT).
    Reference: Gaussian Error Linear Units (GELU) paper: https://arxiv.org/abs/1606.08415
    """
    return 0.5 * x * (1.0 + torch.tanh(math.sqrt(2.0 / math.pi) * (x + 0.044715 * torch.pow(x, 3.0))))

class LayerNorm(nn.Module):
    """ LayerNorm but with an optional bias. PyTorch doesn't support simply bias=False """

    def __init__(self, ndim, bias):
        super().__init__()
        self.weight = nn.Parameter(torch.ones(ndim))
        self.bias = nn.Parameter(torch.zeros(ndim)) if bias else None

    def forward(self, input):
        return F.layer_norm(input, self.weight.shape, self.weight, self.bias, 1e-5)

def get_batch(train_data, val_data=None):
    if not val_data:
        data = train_data
    else:
        data = val_data
    ix = torch.randint(len(data) - block_size, (batch_size,))
    x = torch.stack([data[i:i+block_size] for i in ix])
    y = torch.stack([data[i+1:i+block_size+1] for i in ix])
    x, y = x.to(device), y.to(device)
    return x, y

@torch.no_grad()
def estimate_loss(data):
    out = {}
    model.eval()
    losses = torch.zeros(eval_iterations)
    for k in range(eval_iterations):
        x, y = get_batch(data)
        logits, loss = model(x, y)
        losses[k] = loss.item()
    out = losses.mean()
    model.train()
    return out

class Head(nn.Module):
    """ One head of attention """
    def __init__(self, head_size):
        super().__init__()
        self.key = nn.Linear(n_embed, head_size, bias=False)
        self.query = nn.Linear(n_embed, head_size, bias=False)
        self.value = nn.Linear(n_embed, head_size, bias=False)
        #self.register_buffer('tril', torch.tril(torch.ones(block_size, block_size)))
        self.dropout = nn.Dropout(dropout)

    def forward(self, x):
        B, T, C = x.shape
        k = self.key(x) # (B, T, C)
        q = self.query(x) # (B, T, C)
        weights = q @ k.transpose(-2, -1) * C**-0.5 # (B,T,C) @ (B,C,T) -> (B,T,T)
        #weights = weights.masked_fill(self.tril[:T, :T] == 0, float('-inf')) # (B, T, T)
        weights = F.softmax(weights, dim=-1) # (B, T, T)
        weights = self.dropout(weights)
        vals = self.value(x)
        out = weights @ vals # (B, T, T) @ (B, T, C) -> (B, T, C)
        return out

class MultiHeadAttention(nn.Module):
    """ Multiple heads of self-attention in parallel """

    def __init__(self, num_heads, head_size):
        super().__init__()
        self.heads = nn.ModuleList([Head(head_size) for _ in range(num_heads)])
        self.proj = nn.Linear(n_embed, n_embed)
        self.dropout = nn.Dropout(dropout)

    def forward(self, x):
        out = torch.cat([h(x) for h in self.heads], dim=-1)
        out = self.dropout(self.proj(out))
        return out

class FeedForward(nn.Module):
    """ A simple linear layer followed by a non-linearity """

    def __init__(self, n_embed):
        super().__init__()
        self.net = nn.Sequential(nn.Linear(n_embed, 4*n_embed),
                    nn.ReLU(),
                    nn.Linear(4*n_embed, n_embed),
                    nn.Dropout(dropout))

    def forward(self, x):
        return self.net(x)


class MLP(nn.Module):

    def __init__(self, n_embed):
        super().__init__()
        self.c_fc    = nn.Linear(n_embed, 4 * n_embed, bias=False)
        self.c_proj  = nn.Linear(4 * n_embed, n_embed, bias=False)
        self.dropout = nn.Dropout(dropout)

    def forward(self, x):
        x = self.c_fc(x)
        x = new_gelu(x)
        x = self.c_proj(x)
        x = self.dropout(x)
        return x

class Block(nn.Module):
    """ Transformer Block: communication followed by computation """

    def __init__(self, n_embed, n_head):
        super().__init__()
        head_size = n_embed // n_head
        self.ln1 = LayerNorm(n_embed, bias=False)
        self.sa = MultiHeadAttention(n_head, head_size)
        self.ln2 = LayerNorm(n_embed, bias=False)
        self.mlp = MLP(n_embed)

    def forward(self, x):
        x = x + self.sa(self.ln1(x))
        x = x + self.mlp(self.ln2(x))
        return x


class TransformerModel(nn.Module):

        def __init__(self):
            super().__init__()
            self.token_embedding_table = nn.Embedding(vocab_size, n_embed)
            self.position_embedding_table = nn.Embedding(block_size, n_embed)
            self.blocks = nn.Sequential(*[Block(n_embed, n_head=n_head) for _ in range(n_layer)])
            self.ln_f = nn.LayerNorm(n_embed) # final layer norm
            self.lm_head = nn.Linear(n_embed, vocab_size, bias=False)

        def forward(self, idx, targets=None):
            # print("shape:", idx.shape)
            B, T = idx.shape

            token_embeds = self.token_embedding_table(idx) # (Batch,Time,Channels)
            pos_embeds = self.position_embedding_table(torch.arange(T, device=device)) # (T, C)
            x = token_embeds + pos_embeds # (B, T, C)
            x = self.blocks(x) # apply self attention
            x = self.ln_f(x)
            logits = self.lm_head(x) # (Batch, Time, Vocab_size)

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
                # crop context to block size
                idx_cond = idx[:, -block_size:]
                # get predictions
                logits, loss = self(idx_cond)
                # focus on last time step
                logits = logits[:,-1,:] # becomes (B, C)
                # apply softmax to get probabilities
                probs = F.softmax(logits, dim=-1) # (B, C)
                # sample from distribution
                idx_next = torch.multinomial(probs, num_samples=1) # (B, 1)
                # append sampled index to running sequence
                idx = torch.cat((idx, idx_next), dim=1) # (B, T+1)
            return idx
