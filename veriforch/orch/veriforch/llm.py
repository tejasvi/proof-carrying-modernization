"""Claude client for proposals (contracts, invariants, counterexamples, patches).

One entry point, `LLM.ask_json`, which returns a parsed JSON object validated by the API against a JSON
schema. Every call is logged to `<run>/llm/usage.jsonl` with its list-price cost, and the full exchange to
`<run>/llm/transcripts/`. A run has a dollar budget (this run's spend, not the ledger's history); a call that would start
beyond it raises BudgetExceeded.
"""
from __future__ import annotations

import json
import os
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

# List prices in $ per million tokens: input, output, cache read, 1-hour cache write.
PRICES = {
    "claude-opus-5-5": (4.0, 20.0, 0.20, 8.0),     # cache write at the 1-hour TTL price
    "claude-sonnet-5-5": (2.0, 10.0, 0.20, 4.0),
    "claude-haiku-5-5": (0.10, 0.50, 0.01, 0.20),
}
DEFAULT_MODEL = "claude-opus-5-5"


class BudgetExceeded(RuntimeError):
    pass


class LLMError(RuntimeError):
    pass


@dataclass
class Usage:
    calls: int = 0
    dollars: float = 0.0
    input_tokens: int = 0
    output_tokens: int = 0
    cache_read: int = 0


class LLM:
    def __init__(self, run_dir: Path, budget: float = 50.0, model: str = DEFAULT_MODEL):
        self.run_dir = Path(run_dir)
        self.budget = budget
        self.model = model
        self.usage = Usage()
        self._lock = threading.Lock()
        self._client = None
        (self.run_dir / "llm" / "transcripts").mkdir(parents=True, exist_ok=True)
        self._load_spent()
        self._start_dollars = self.usage.dollars     # the budget applies to this run, not the ledger's history

    def _load_spent(self) -> None:
        p = self.run_dir / "llm" / "usage.jsonl"
        if p.exists():
            for line in p.read_text().splitlines():
                try:
                    d = json.loads(line)
                except ValueError:
                    continue
                self.usage.calls += 1
                self.usage.dollars += d.get("dollars", 0.0)

    @property
    def client(self):
        if self._client is None:
            import anthropic
            self._client = anthropic.AnthropicVertex(
                project_id=os.environ["ANTHROPIC_VERTEX_PROJECT_ID"],
                region=os.environ.get("CLOUD_ML_REGION", "global"),
                max_retries=4,
                timeout=600.0,
            )
        return self._client

    def ask_json(self, task: str, system: str, user: str, schema: dict[str, Any], *,
                 model: str | None = None, effort: str = "high", max_tokens: int = 64000) -> dict[str, Any]:
        """Ask for one JSON object matching `schema`. `task` labels the call in the ledger."""
        # Structured outputs are blocked by the Vertex organisation policy: ask for JSON in text and validate.
        text = self.ask_text(task, system, user + "\n\n" + json_instructions(schema), model=model, effort=effort,
                             max_tokens=max_tokens)
        return parse_json_answer(text, schema)

    def ask_text(self, task: str, system: str, user: str, *, model: str | None = None, effort: str = "high",
                 max_tokens: int = 64000) -> str:
        """Ask for a free-form answer (e.g. source files). Same ledger, transcripts and budget as `ask_json`."""
        import anthropic
        model = model or self.model
        with self._lock:
            run_spent = self.usage.dollars - self._start_dollars
            if run_spent >= self.budget:
                raise BudgetExceeded(f"LLM budget ${self.budget:.2f} for this run spent (${run_spent:.2f} this run, "
                                     f"${self.usage.dollars:.2f} in the run directory's ledger)")
        t0 = time.time()
        try:
            with self.client.messages.stream(
                model=model,
                max_tokens=max_tokens,
                system=[{"type": "text", "text": system, "cache_control": {"type": "ephemeral", "ttl": "1h"}}],
                messages=[{"role": "user", "content": user}],
                output_config={"effort": effort},
            ) as stream:
                resp = stream.get_final_message()
        except anthropic.BadRequestError as e:
            raise LLMError(f"bad request: {e.message}") from e
        except anthropic.APIStatusError as e:
            raise LLMError(f"API error {e.status_code}: {e.message}") from e
        except anthropic.APIConnectionError as e:
            raise LLMError(f"connection error: {e}") from e
        dt = time.time() - t0
        u = resp.usage
        pin, pout, pcr, pcw = PRICES.get(model, PRICES[DEFAULT_MODEL])
        cache_w = u.cache_creation_input_tokens or 0
        cache_r = u.cache_read_input_tokens or 0
        dollars = (u.input_tokens * pin + u.output_tokens * pout + cache_r * pcr + cache_w * pcw) / 1e6
        text = next((b.text for b in resp.content if b.type == "text"), "")
        rec = {"t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "task": task, "model": model,
               "effort": effort, "seconds": round(dt, 1), "input": u.input_tokens, "output": u.output_tokens,
               "cache_read": cache_r, "cache_write": cache_w, "dollars": round(dollars, 5),
               "stop": resp.stop_reason}
        with self._lock:
            self.usage.calls += 1
            self.usage.dollars += dollars
            self.usage.input_tokens += u.input_tokens
            self.usage.output_tokens += u.output_tokens
            self.usage.cache_read += cache_r
            with open(self.run_dir / "llm" / "usage.jsonl", "a") as f:
                f.write(json.dumps(rec) + "\n")
            n = self.usage.calls
        tpath = self.run_dir / "llm" / "transcripts" / f"{n:05d}_{_slug(task)}.json"
        tpath.write_text(json.dumps({"task": task, "model": model, "system_sha": _sha(system),
                                     "user": user, "answer": text, "usage": rec}, indent=1))
        spath = self.run_dir / "llm" / "transcripts" / f"system_{_sha(system)}.txt"
        if not spath.exists():
            spath.write_text(system)
        if resp.stop_reason == "refusal":
            raise LLMError("model declined the request")
        if resp.stop_reason == "max_tokens":
            raise LLMError("answer truncated at max_tokens")
        return text


def json_instructions(schema: dict[str, Any]) -> str:
    props = schema.get("properties", {})
    keys = ", ".join(f"`{k}` ({v.get('type', 'any')})" for k, v in props.items())
    return ("Answer with exactly one JSON object and nothing else (no prose, no code fence), with the keys "
            + keys + ". Strings must be valid JSON strings (escape newlines as \\n and quotes as \\\").")


def parse_json_answer(text: str, schema: dict[str, Any]) -> dict[str, Any]:
    """Parse the first JSON object in `text` and check the schema's required keys and simple types."""
    t = text.strip()
    if t.startswith("```"):
        t = t.split("\n", 1)[1] if "\n" in t else t
        t = t.rsplit("```", 1)[0]
    start = t.find("{")
    if start < 0:
        raise LLMError(f"answer has no JSON object: {text[:200]!r}")
    dec = json.JSONDecoder()
    try:
        obj, _ = dec.raw_decode(t[start:])
    except ValueError as e:
        raise LLMError(f"answer is not valid JSON ({e}): {text[:300]!r}") from e
    if not isinstance(obj, dict):
        raise LLMError("answer is not a JSON object")
    types = {"string": str, "array": list, "object": dict, "boolean": bool, "integer": int, "number": (int, float)}
    for k in schema.get("required", []):
        if k not in obj:
            raise LLMError(f"answer lacks key {k!r}")
    for k, v in schema.get("properties", {}).items():
        ty = types.get(v.get("type", ""))
        if k in obj and ty and not isinstance(obj[k], ty):
            raise LLMError(f"key {k!r} has the wrong type")
    return obj


def _slug(s: str) -> str:
    return "".join(c if c.isalnum() or c in "-_." else "_" for c in s)[:60]


def _sha(s: str) -> str:
    import hashlib
    return hashlib.sha256(s.encode()).hexdigest()[:16]
