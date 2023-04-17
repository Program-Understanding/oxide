""" Plugin: Utility functions for managing truth files.
"""
import torch
import torch.nn as nn
from torch.nn import functional as F
import progress, api

vocab_size = 256
block_size = 64 # number of sequences in parallel
batch_size = 256 # Maximum context length
iterations = 1000
eval_iterations = 100
n_embed = 128 # number of embedding dimensions
learning_rate = 3e-4
n_head = 4
n_layer = 6
dropout = 0.2
device = 'cuda' if torch.cuda.is_available() else 'cpu'
model = None


torch.manual_seed(1337)


def trainllm(args, opts):
    """
        Train a large language model on bytes from programs passed in.
        Syntax: trainllm <oid_list>
    """
    args, invalid = api.valid_oids(args)
    if not args:
        raise ShellSyntaxError("Must provide an OID.")
    args = api.expand_oids(args)
    global model
    if not model:
        model = BigramLanguageModel()
        m = model.to(device)
    optimizer = torch.optim.AdamW(model.parameters(), lr=learning_rate)

    for oid in args:
        src_type = api.get_field("src_type", oid, "type")
        if "PE" not in src_type and "ELF" not in src_type:
            continue

        raw_data = api.get_field("files", oid, "data")

        data = torch.tensor(encode(raw_data), dtype=torch.long)
        for steps in range(iterations):
            if steps % eval_iterations == 0:
                losses = estimate_loss(data)
                print(f"step {iter}: loss {losses:.4f}")
            xb, yb = get_batch(data)
            logits, loss = model(xb, yb)
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

class Block(nn.Module):
    """ Transformer Block: communication followed by computation """

    def __init__(self, n_embed, n_head):
        super().__init__()
        head_size = n_embed // n_head
        self.sa = MultiHeadAttention(n_head, head_size)
        self.ffwd = FeedForward(n_embed)
        self.ln1 = nn.LayerNorm(n_embed)
        self.ln2 = nn.LayerNorm(n_embed)

    def forward(self, x):
        x = x + self.sa(self.ln1(x))
        x = x + self.ffwd(self.ln2(x))
        return x


class BigramLanguageModel(nn.Module):

        def __init__(self):
            super().__init__()
            self.token_embedding_table = nn.Embedding(vocab_size, n_embed)
            self.position_embedding_table = nn.Embedding(block_size, n_embed)
            self.blocks = nn.Sequential(*[Block(n_embed, n_head=n_head) for _ in range(n_layer)])
            self.ln_f = nn.LayerNorm(n_embed) # final layer norm
            self.lm_head = nn.Linear(n_embed, vocab_size)

        def forward(self, idx, targets):
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
                idx_cond = idx[:, -block_size]
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
