"""Ranks functions against a text prompt using CLAP.

CLAP (Wang et al., ISSTA 2024, arXiv:2402.16928) pairs an assembly encoder with
a text encoder trained contrastively, putting disassembly and natural language
in one space. We use the released hustcw/clap-asm and hustcw/clap-text weights
and rank by cosine similarity to the prompt.

Assembly comes from ghidra_disasm and is prepared per function: instructions in
address order, keyed by 1-based position, with intra-function jump targets
rewritten to INSTR references.
"""

import logging
import re
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np

from oxide.core import api
from oxide.modules.analyzers.query_function.config import NAME
from oxide.modules.analyzers.query_function.common import (
    as_bool,
    as_float,
    as_int,
    extract_func_name,
    first_preview_line,
    iter_functions,
    load_text_option,
    result_limit,
)

logger = logging.getLogger(NAME)


def results(oids: List[str], opts: dict) -> Dict[str, Any]:
    prompts = _load_prompts(opts)
    if not prompts:
        return {"error": "Please provide 'query', 'query_path', 'prompts', or 'prompts_path'."}

    limit = result_limit(opts)
    offset = max(0, as_int(opts.get("offset", 0), 0))
    similarity_threshold = as_float(opts.get("similarity_threshold", 0.0), 0.0)
    max_instructions = as_int(opts.get("max_instructions", 512), 512)
    batch_size = max(1, as_int(opts.get("batch_size", 16), 16))
    use_cache = as_bool(opts.get("use_cache", True))
    rebuild = as_bool(opts.get("rebuild", False))
    normalize = as_bool(opts.get("normalize_embeddings", False))
    temperature = as_float(opts.get("temperature", 0.07), 0.07)
    asm_model_id = (opts.get("asm_model_id") or "hustcw/clap-asm").strip()
    text_model_id = (opts.get("text_model_id") or "hustcw/clap-text").strip()

    try:
        encoders = _get_clap_encoders(
            asm_model_id=asm_model_id,
            text_model_id=text_model_id,
            device=(opts.get("device") or "auto").strip(),
        )
    except ImportError as err:
        return {"error": str(err), "hint": "Install torch and transformers to use backend='clap'."}
    except Exception as err:
        logger.exception("Failed to load CLAP models")
        return {"error": f"Failed to load CLAP models: {err}"}

    text_emb = _encode_clap_texts(encoders, prompts, batch_size=batch_size, normalize=normalize)
    counts: Dict[str, Dict[str, Any]] = {}
    global_candidates: List[Dict[str, Any]] = []
    per_function_labels: List[Dict[str, Any]] = []
    total_functions = 0

    for oid in oids:
        idx = _load_or_build_clap_index(
            oid=oid,
            asm_model_id=asm_model_id,
            max_instructions=max_instructions,
            batch_size=batch_size,
            use_cache=use_cache,
            rebuild=rebuild,
            normalize=normalize,
            encoders=encoders,
            counts=counts,
        )
        if not idx:
            continue
        total_functions += int(idx.get("num_indexed", 0) or 0)

        logits = idx["emb"].dot(text_emb.T)
        scores = _softmax(logits / temperature, axis=1) if len(prompts) > 1 else logits
        if len(prompts) == 1:
            # Rank every function; paging the pooled ranking is the caller's
            # job. Capping per binary here would let one file's weakest
            # matches displace another file's best.
            global_candidates.extend(_rank_single_prompt(
                idx, oid, scores[:, 0], 0,
                prompt=prompts[0],
                similarity_threshold=similarity_threshold,
            ))
            continue

        best = np.argmax(scores, axis=1)
        confidence = scores[np.arange(scores.shape[0]), best]
        for i, prompt_index in enumerate(best):
            per_function_labels.append({
                "oid": oid,
                "function_addr": idx["addrs"][i],
                "function_name": idx["names"][i],
                "prompt": prompts[int(prompt_index)],
                "prompt_index": int(prompt_index),
                "score": float(confidence[i]),
                "preview": idx["previews"][i],
            })
        for i in range(scores.shape[0]):
            for j in range(scores.shape[1]):
                if float(scores[i, j]) < similarity_threshold:
                    continue
                global_candidates.append(_candidate(idx, oid, i, float(scores[i, j]), prompts[j], prompt_index=j))

    global_candidates.sort(key=lambda x: x["score"], reverse=True)
    page = global_candidates[offset:offset + limit] if limit > 0 else global_candidates[offset:]
    result: Dict[str, Any] = {
        "prompts": prompts,
        "backend": "clap",
        "returned_count": len(page),
        "offset": offset,
        "limit": limit,
        "total_functions": total_functions,
        "counts": counts,
        "results": {
            "best_match": page[0] if page else None,
            "candidates": page,
        },
        "notes": {
            "asm_model_id": asm_model_id,
            "text_model_id": text_model_id,
            "similarity": "dot product over CLAP assembly/text embeddings",
            "temperature": temperature,
            "normalized": normalize,
            "sources": [
                "https://arxiv.org/abs/2402.16928",
                "https://github.com/Hustcw/CLAP",
                "https://huggingface.co/hustcw/clap-asm",
            ],
        },
    }
    if len(prompts) > 1:
        result["results"]["per_function_best_label"] = per_function_labels
    if not page:
        result["warning"] = "No indexed functions available from ghidra_disasm."
    return result


def _load_or_build_clap_index(
    *,
    oid: str,
    asm_model_id: str,
    max_instructions: int,
    batch_size: int,
    use_cache: bool,
    rebuild: bool,
    normalize: bool,
    encoders: "ClapEncoders",
    counts: Dict[str, Dict[str, Any]],
) -> Optional[Dict[str, Any]]:
    key = _clap_cache_key(oid, asm_model_id, max_instructions, normalize)
    if use_cache and (not rebuild) and api.local_exists(NAME, key):
        try:
            blob = api.local_retrieve(NAME, key) or {}
            idx = blob.get(oid)
            if idx:
                counts[oid] = {
                    "cache": "hit",
                    "num_functions": idx.get("num_functions", 0),
                    "num_indexed": idx.get("num_indexed", 0),
                }
                return idx
        except Exception:
            logger.exception("Failed to load cached CLAP index for oid=%s", oid)

    funcs = api.get_field("ghidra_disasm", oid, "functions") or {}
    blocks = api.get_field("ghidra_disasm", oid, "original_blocks") or {}
    instructions = api.get_field("ghidra_disasm", oid, "instructions") or {}
    f_list = list(iter_functions(funcs))
    addrs: List[str] = []
    names: List[str] = []
    asm_functions: List[Dict[str, str]] = []
    previews: List[str] = []
    for addr, finfo in f_list:
        asm_items = _function_assembly(
            finfo,
            blocks,
            instructions,
            max_instructions=max_instructions,
        )
        if not asm_items:
            continue
        addrs.append(str(addr))
        names.append(extract_func_name(finfo, addr))
        asm_functions.append(_assembly_dict(asm_items))
        previews.append(first_preview_line("\n".join(text for _, text in asm_items)))

    counts[oid] = {"cache": "miss", "num_functions": len(f_list), "num_indexed": len(asm_functions)}
    if not asm_functions:
        return None
    idx = {
        "num_functions": len(f_list),
        "num_indexed": len(asm_functions),
        "addrs": addrs,
        "names": names,
        "previews": previews,
        "emb": _encode_clap_asm(encoders, asm_functions, batch_size=batch_size, normalize=normalize),
    }
    if use_cache:
        try:
            api.local_store(NAME, key, {oid: idx})
        except Exception:
            logger.exception("Failed to cache CLAP index for oid=%s", oid)
    return idx


def _rank_single_prompt(
    idx: Dict[str, Any],
    oid: str,
    sims: np.ndarray,
    top_k: int,
    prompt: Optional[str] = None,
    similarity_threshold: float = float("-inf"),
) -> List[Dict[str, Any]]:
    k_local = sims.shape[0] if top_k <= 0 else min(top_k, sims.shape[0])
    if k_local <= 0:
        return []
    loc = np.argpartition(-sims, k_local - 1)[:k_local]
    loc = loc[np.argsort(-sims[loc])]
    return [
        _candidate(idx, oid, int(i), float(sims[i]), prompt)
        for i in loc
        if float(sims[i]) >= similarity_threshold
    ]


def _candidate(
    idx: Dict[str, Any],
    oid: str,
    i: int,
    score: float,
    prompt: Optional[str] = None,
    prompt_index: Optional[int] = None,
) -> Dict[str, Any]:
    out = {
        "oid": oid,
        "function_addr": idx["addrs"][i],
        "function_name": idx["names"][i],
        "func_addr": idx["addrs"][i],
        "func_name": idx["names"][i],
        "score": score,
        "similarity": score,
        "search_mode": "semantic",
        "match_type": "semantic",
        "preview": idx["previews"][i],
    }
    if prompt is not None:
        out["prompt"] = prompt
    if prompt_index is not None:
        out["prompt_index"] = prompt_index
    return out


def _function_assembly(
    finfo: Any,
    blocks: Dict[Any, Any],
    instructions: Dict[Any, Any],
    max_instructions: int,
) -> List[Tuple[int, str]]:
    """Collect a function's instructions in ascending address order.

    An instruction's position is what its INSTR token keys on, so block
    traversal order must not leak into the sequence; a reordered function
    silently misaligns every reference into it.

    max_instructions is a memory guard rather than a tuning knob. The tokenizer
    caps a function at 1024 tokens, which binds first at any realistic density.
    """
    rows: List[Tuple[int, str]] = []
    for block_addr in _block_addrs(finfo):
        block = blocks.get(block_addr) or blocks.get(str(block_addr))
        if not isinstance(block, dict):
            continue
        for member in block.get("members", []) or []:
            if not isinstance(member, (list, tuple)) or len(member) < 2:
                continue
            text = _resolve_member_text(member, instructions)
            if text:
                rows.append((as_int(member[0], -1), text))
    rows.sort(key=lambda row: row[0])
    return rows[:max_instructions] if max_instructions > 0 else rows


def _block_addrs(finfo: Any) -> Iterable[Any]:
    if isinstance(finfo, dict):
        return finfo.get("blocks", []) or []
    return []


def _resolve_member_text(member: Sequence[Any], instructions: Dict[Any, Any]) -> str:
    addr = member[0] if len(member) > 0 else None
    text = str(member[1]).strip() if len(member) > 1 else ""
    if text and text.lower() != "null":
        return text

    candidates = []
    if addr is not None:
        candidates.extend([addr, str(addr)])
        try:
            addr_i = int(addr)
        except Exception:
            addr_i = None
        if addr_i is not None:
            candidates.extend([addr_i, f"{addr_i:x}", f"0x{addr_i:x}"])
    for key in candidates:
        if key in instructions:
            resolved = str(instructions[key]).strip()
            if resolved and resolved.lower() != "null":
                return resolved
    return ""


def _assembly_dict(rows: Sequence[Tuple[int, str]]) -> Dict[str, str]:
    """Build the per-function instruction map the AsmTokenizer expects.

    Keys are the instruction's 1-based position in the function. The tokenizer
    turns each key into an "INSTR<key>" token and resolves it against a
    vocabulary holding INSTR1 through INSTR1024, so any other key scheme
    becomes [UNK].

    Jump targets are rewritten to the INSTR reference for the instruction they
    land on. The encoder shares an INSTR token's embedding with the instruction
    embedding at that position, which is how control flow reaches the
    representation; a raw target address leaves it out entirely.
    """
    kept = [(addr, text) for addr, text in rows if text]
    index_of = {addr: position for position, (addr, _text) in enumerate(kept, start=1)}
    return {
        str(position): _rebase_jump_target(text, index_of)
        for position, (_addr, text) in enumerate(kept, start=1)
    }


JUMP_TO_ADDRESS = re.compile(r"^(j\S*)(\s+)0x([0-9a-fA-F]+)$")


def _rebase_jump_target(text: str, index_of: Dict[int, int]) -> str:
    """Rewrite a jump's target address to the INSTR reference it lands on.

    Only jumps are rewritten, so a call keeps its target. A target outside the
    function has no position to reference and is left as-is.
    """
    match = JUMP_TO_ADDRESS.match(text.strip())
    if not match:
        return text
    position = index_of.get(int(match.group(3), 16))
    if position is None:
        return text
    return f"{match.group(1)}{match.group(2)}INSTR{position}"


def _load_prompts(opts: dict) -> List[str]:
    query = load_text_option(opts, "query", "query_path")
    if query:
        return [query]
    raw = load_text_option(opts, "prompts", "prompts_path")
    return [line.strip() for line in raw.splitlines() if line.strip()]


def _clap_cache_key(oid: str, asm_model_id: str, max_instructions: int, normalize: bool) -> str:
    """Key a cached CLAP index.

    The key covers the inputs to encoding but not how the assembly text itself
    is built, so any change to _function_assembly or _assembly_dict must be
    followed by deleting the stored clap_asm_* entries. Nothing detects a stale
    index; it simply returns embeddings of text that is no longer produced.
    """
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", f"clap_asm_{oid}_{asm_model_id}_{max_instructions}_{normalize}")


def _softmax(x: np.ndarray, axis: int) -> np.ndarray:
    shifted = x - np.max(x, axis=axis, keepdims=True)
    exp = np.exp(shifted)
    return exp / np.sum(exp, axis=axis, keepdims=True)


class ClapEncoders:
    def __init__(self, asm_tokenizer: Any, asm_model: Any, text_tokenizer: Any, text_model: Any, torch: Any, device: Any):
        self.asm_tokenizer = asm_tokenizer
        self.asm_model = asm_model
        self.text_tokenizer = text_tokenizer
        self.text_model = text_model
        self.torch = torch
        self.device = device


CLAP_ENCODERS: Optional[ClapEncoders] = None


CLAP_ENCODER_KEY: Optional[Tuple[str, str, str]] = None


def _get_clap_encoders(*, asm_model_id: str, text_model_id: str, device: str) -> ClapEncoders:
    global CLAP_ENCODERS, CLAP_ENCODER_KEY
    key = (asm_model_id, text_model_id, device)
    if CLAP_ENCODERS is not None and CLAP_ENCODER_KEY == key:
        return CLAP_ENCODERS
    try:
        import torch
        from transformers import AutoModel, AutoTokenizer
    except ImportError as err:
        raise ImportError("query_function backend='clap' requires torch and transformers.") from err

    actual_device = torch.device("cuda" if device == "auto" and torch.cuda.is_available() else "cpu")
    if device and device != "auto":
        actual_device = torch.device(device)
    asm_tokenizer = AutoTokenizer.from_pretrained(asm_model_id, trust_remote_code=True)
    text_tokenizer = AutoTokenizer.from_pretrained(text_model_id, trust_remote_code=True)
    asm_model = AutoModel.from_pretrained(asm_model_id, trust_remote_code=True).to(actual_device)
    text_model = AutoModel.from_pretrained(text_model_id, trust_remote_code=True).to(actual_device)
    asm_model.eval()
    text_model.eval()
    CLAP_ENCODERS = ClapEncoders(asm_tokenizer, asm_model, text_tokenizer, text_model, torch, actual_device)
    CLAP_ENCODER_KEY = key
    return CLAP_ENCODERS


def _encode_clap_asm(encoders: ClapEncoders, texts: Sequence[Dict[str, str]], batch_size: int, normalize: bool) -> np.ndarray:
    return _encode_clap(encoders, encoders.asm_tokenizer, encoders.asm_model, texts, batch_size, normalize)


def _encode_clap_texts(encoders: ClapEncoders, texts: Sequence[str], batch_size: int, normalize: bool) -> np.ndarray:
    return _encode_clap(encoders, encoders.text_tokenizer, encoders.text_model, texts, batch_size, normalize)


def _encode_clap(
    encoders: ClapEncoders,
    tokenizer: Any,
    model: Any,
    texts: Sequence[str],
    batch_size: int,
    normalize: bool,
) -> np.ndarray:
    batches: List[np.ndarray] = []
    torch = encoders.torch
    with torch.no_grad():
        for start in range(0, len(texts), batch_size):
            batch = list(texts[start:start + batch_size])
            inputs = _tokenize_clap_batch(tokenizer, batch)
            inputs = {key: value.to(encoders.device) for key, value in inputs.items()}
            output = model(**inputs)
            emb = _clap_output_embedding(output, inputs, torch)
            if len(emb.shape) != 2:
                raise ValueError(
                    f"CLAP embedding must be 2-D (batch, hidden), got shape {tuple(emb.shape)}. "
                    "Normalizing or scoring a non-pooled tensor would operate on the wrong axis."
                )
            if normalize:
                emb = torch.nn.functional.normalize(emb, p=2, dim=1)
            batches.append(emb.detach().cpu().numpy().astype(np.float32))
    return np.vstack(batches) if batches else np.empty((0, 0), dtype=np.float32)


def _clap_output_embedding(output: Any, inputs: Dict[str, Any], torch: Any) -> Any:
    if hasattr(output, "shape") and len(output.shape) == 2:
        return output
    pooler_output = getattr(output, "pooler_output", None)
    if pooler_output is not None and hasattr(pooler_output, "shape"):
        return pooler_output
    emb = getattr(output, "last_hidden_state", None)
    if emb is None and isinstance(output, (tuple, list)) and output:
        emb = output[0]
    if emb is None:
        raise ValueError(
            "CLAP model output did not expose a usable embedding tensor "
            "(expected direct tensor, pooler_output, or last_hidden_state)."
        )
    if len(emb.shape) == 2:
        return emb
    mask = inputs.get("attention_mask")
    if mask is None:
        return emb.mean(dim=1)
    mask = mask.unsqueeze(-1).expand(emb.size()).float()
    return torch.sum(emb * mask, dim=1) / torch.clamp(mask.sum(dim=1), min=1e-9)


def _tokenize_clap_batch(tokenizer: Any, batch: Sequence[Any]) -> Dict[str, Any]:
    if batch and isinstance(batch[0], dict):
        # The AsmTokenizer takes per-function dicts, and its custom __call__
        # forwards kwargs into pad(), which rejects truncation.
        return tokenizer(batch, padding=True, return_tensors="pt")
    try:
        return tokenizer(batch, padding=True, truncation=True, return_tensors="pt")
    except TypeError:
        return tokenizer(batch, padding=True, return_tensors="pt")
