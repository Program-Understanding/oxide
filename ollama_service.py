#!/usr/bin/env python3
import os

from fastapi import FastAPI
from pydantic import BaseModel

# ——— Try to read your preferred model from oxide, else env, else a default ———
try:
    from oxide.core import oxide as oxide
except Exception:
    oxide = None

# MODEL_NAME = getattr(oxide_api, "local_llm_path")
MODEL_NAME = "llama3.1:8b-instruct-q4_K_M"
if not MODEL_NAME:
    raise ImportError("oxide.api.local_llm_path is not configured")

# Ollama host (defaults to local daemon)
OLLAMA_HOST = os.getenv("OLLAMA_HOST", "http://localhost:11434")

# —— Basic generation defaults ——
SYSTEM_PROMPT = "You are an expert reverse-engineer"
CONTEXT_LIMIT = int(os.getenv("CONTEXT_LIMIT", "8192"))  # maps to Ollama num_ctx
DEFAULT_TEMPERATURE = 0.7
DEFAULT_MAX_NEW_TOKENS = 256

# ——— Ollama client ———
try:
    import ollama
except ImportError as e:
    raise SystemExit(
        "The 'ollama' package is required. Install with: pip install ollama"
    ) from e

# Eager sanity check (optional but helpful)
def _ensure_model_available(model: str) -> None:
    try:
        # show() raises if the model isn't available locally
        ollama.show(model)
    except Exception as exc:
        raise RuntimeError(
            f"Ollama model '{model}' not found locally. "
            f"Run: `ollama pull {model}`"
        ) from exc

print(f"Using Ollama model: {MODEL_NAME} @ {OLLAMA_HOST}")
_ensure_model_available(MODEL_NAME)
print("✅ Ollama model found. Ready to serve!\n")


class LLMRunner:
    def __init__(
        self,
        model_name: str,
        system_prompt: str = SYSTEM_PROMPT,
        context_limit: int = CONTEXT_LIMIT,
    ):
        self.model_name = model_name
        self.system_prompt = system_prompt
        self.context_limit = context_limit

    def generate(
        self,
        user_input: str,
        temperature: float = DEFAULT_TEMPERATURE,
        max_new_tokens: int = DEFAULT_MAX_NEW_TOKENS,
    ) -> str:
        """
        Calls Ollama Chat API. We let Ollama handle the context window; we pass
        num_ctx to request a larger window when supported by the model.
        """
        # Options accepted by Ollama:
        # https://github.com/ollama/ollama/blob/main/docs/modelfile.md#parameters
        options = {
            "temperature": float(temperature),
            "num_predict": int(max_new_tokens),
            "num_ctx": int(self.context_limit),
        }

        resp = ollama.chat(
            model=self.model_name,
            messages=[
                {"role": "system", "content": self.system_prompt},
                {"role": "user", "content": user_input},
            ],
            options=options,
            stream=False,  # keep your current API simple; flip to True if you want SSE
        )
        # Response shape: {"model": ..., "created_at": ..., "message": {"role": "assistant", "content": "..."}}
        return resp["message"]["content"]


runner = LLMRunner(model_name=MODEL_NAME)

# ——— FastAPI Service ———
app = FastAPI(title="Local LLM Service (Ollama)")

class GenerateRequest(BaseModel):
    prompt: str
    temperature: float = DEFAULT_TEMPERATURE
    max_new_tokens: int = DEFAULT_MAX_NEW_TOKENS

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
