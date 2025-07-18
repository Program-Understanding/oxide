#!/usr/bin/env python3
import os
# ——— Avoid CUDA fragmentation by splitting large allocations and allow merging freed segments ———
os.environ["PYTORCH_CUDA_ALLOC_CONF"] = "max_split_size_mb:128,expandable_segments:True"

from oxide.core import oxide as oxide
import torch
from fastapi import FastAPI
from pydantic import BaseModel
from transformers import AutoTokenizer, AutoModelForCausalLM, BitsAndBytesConfig

# —— USER CONFIG ——
MODEL_PATH = oxide.api.local_llm_path

print("Model Path: ", MODEL_PATH)
SYSTEM_PROMPT = "You are an expert reverse-engineer"
CONTEXT_LIMIT = 8192
OVERLAP_TOKENS = 128

# —— bitsandbytes 4-bit config ——
bnb_config = BitsAndBytesConfig(
    load_in_4bit=True,
    bnb_4bit_compute_dtype=torch.float16,
    # use the NF4 kernel and double quant to halve tables
    bnb_4bit_quant_type="nf4",
    bnb_4bit_use_double_quant=True,
    # NO CPU-offload!
    llm_int8_enable_fp32_cpu_offload=False,
)

# —— LOAD & VERIFY ONCE ——
print("⏳ Loading tokenizer…")
_tokenizer = AutoTokenizer.from_pretrained(
    MODEL_PATH,
    trust_remote_code=True,
    local_files_only=True,
)
_tokenizer.pad_token_id = _tokenizer.eos_token_id

# Precompute system prompt length
_sys_tokens = _tokenizer(SYSTEM_PROMPT, add_special_tokens=False)["input_ids"]
SYS_LEN = len(_sys_tokens)

print("⏳ Loading model in 4-bit mode…")
_model = AutoModelForCausalLM.from_pretrained(
    MODEL_PATH,
    quantization_config=bnb_config,
    device_map="auto",
    trust_remote_code=True,
    local_files_only=True,
    # pin almost all of your 24 GB to the model
    max_memory={0: "23GB", "cpu": "1GB"},
    torch_dtype=torch.float16,  # load fp16 for 4-bit quantization
)
# RE-ENABLE KV cache for blazing-fast incremental generation
_model.config.use_cache = True
_model.eval()
print("✅ Model loaded in 4-bit on GPU. Ready to serve!\n")


def build_prompt(system: str, user: str) -> str:
    """
    Wrap system prompt and user input correctly for CodeLlama-2 Instruct format.
    """
    return (
        "<s>[INST] <<SYS>>\n"
        f"{system}\n"
        "<</SYS>>\n\n"
        f"{user} [/INST]"
    )


class LLMRunner:
    def __init__(self,
                 system_prompt: str = SYSTEM_PROMPT,
                 context_limit: int = CONTEXT_LIMIT,
                 overlap: int = OVERLAP_TOKENS):
        self.system_prompt = system_prompt
        self.context_limit = context_limit
        self.overlap = overlap

    def _generate_chunk(self,
                        user_chunk: str,
                        temperature: float,
                        max_new_tokens: int) -> str:
        # free any cached but unused memory before dequantizing weights
        torch.cuda.empty_cache()
        prompt = build_prompt(self.system_prompt, user_chunk)
        inputs = _tokenizer(prompt, return_tensors="pt").to(_model.device)
        # `inference_mode` is automatic inside generate();
        # with use_cache=True it will be MUCH faster.
        outputs = _model.generate(
            **inputs,
            do_sample=True,
            temperature=temperature,
            max_new_tokens=max_new_tokens,
            pad_token_id=_tokenizer.eos_token_id,
            use_cache=True,
        )
        gen_ids = outputs[0][ inputs["input_ids"].shape[-1] : ]
        return _tokenizer.decode(gen_ids, skip_special_tokens=True)

    def generate(
        self,
        user_input: str,
        temperature: float = 0.7,
        max_new_tokens: int = 256
    ) -> str:
        torch.cuda.empty_cache()
        encoding = _tokenizer(user_input, add_special_tokens=False)
        token_ids = encoding["input_ids"]
        max_input_tokens = self.context_limit - max_new_tokens - SYS_LEN

        if len(token_ids) <= max_input_tokens:
            return self._generate_chunk(user_input, temperature, max_new_tokens)

        responses = []
        start = 0
        chunk_size = max_input_tokens - self.overlap
        while start < len(token_ids):
            chunk_ids = token_ids[start:start + chunk_size]
            chunk_text = _tokenizer.decode(chunk_ids)
            responses.append(
                self._generate_chunk(chunk_text, temperature, max_new_tokens)
            )
            start += chunk_size

        return "\n".join(responses)


runner = LLMRunner()

app = FastAPI(title="Local LLM Service")

class GenerateRequest(BaseModel):
    prompt: str
    temperature: float = 0.7
    max_new_tokens: int = 256

class GenerateResponse(BaseModel):
    response: str

@app.post("/generate", response_model=GenerateResponse)
def generate(req: GenerateRequest):
    reply = runner.generate(
        req.prompt,
        temperature=req.temperature,
        max_new_tokens=req.max_new_tokens
    )
    return GenerateResponse(response=reply)

if __name__ == "__main__":
    import uvicorn
    uvicorn.run("llm_service:app", host="0.0.0.0", port=8000, log_level="info")
