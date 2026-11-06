"""Data model shared by every component. All objects round-trip through JSON."""
from __future__ import annotations

import dataclasses
import hashlib
import json
import os
import threading
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


def sha256(text: str | bytes) -> str:
    if isinstance(text, str):
        text = text.encode()
    return hashlib.sha256(text).hexdigest()


class JsonMixin:
    def to_json(self) -> dict[str, Any]:
        return dataclasses.asdict(self)  # type: ignore[arg-type]

    @classmethod
    def from_json(cls, d: dict[str, Any]):
        names = {f.name for f in dataclasses.fields(cls)}  # type: ignore[arg-type]
        return cls(**{k: v for k, v in d.items() if k in names})


@dataclass
class Variant(JsonMixin):
    """One build configuration of the target (e.g. a set of -D flags)."""
    name: str
    flags: list[str] = field(default_factory=list)
    sources: list[str] = field(default_factory=list)   # overrides Target.sources when non-empty


@dataclass
class Target(JsonMixin):
    """A target repository and how to build and test it."""
    name: str
    lang: str                      # "cir" | "jimple" | "strictts" | "cobol" | "rust"
    root: str                      # absolute path of the source tree (this version)
    sources: list[str]             # translation units / classes / files to verify, relative to root
    include: list[str] = field(default_factory=list)
    variants: list[Variant] = field(default_factory=lambda: [Variant("default")])
    tests: list[str] = field(default_factory=list)       # test files, relative to root
    entry: list[str] = field(default_factory=list)       # API entry points (unit names); empty = all non-static
    version: str = "v0"            # source version label; patches create v1, v2, ...
    extra: dict[str, Any] = field(default_factory=dict)  # adapter-specific settings

    @classmethod
    def from_json(cls, d):
        d = dict(d)
        d["variants"] = [Variant.from_json(v) if isinstance(v, dict) else v for v in d.get("variants", [])] or [Variant("default")]
        return super().from_json.__func__(cls, d)  # type: ignore[attr-defined]


@dataclass
class Unit(JsonMixin):
    """One function or method."""
    name: str
    sym: str
    lean_decl: str
    kind: str = "internal"         # api | internal | test | harness
    signature: Any = None          # bridge-specific
    callees: list[str] = field(default_factory=list)
    scope: str = "in_scope"        # in_scope | gap:<reason>
    loc: str = ""
    body_hash: str = ""
    source: str = ""               # source text of the function (for prompts and reports)

    @property
    def in_scope(self) -> bool:
        return self.scope == "in_scope"


@dataclass
class Contract(JsonMixin):
    unit: str
    binders: str                   # Lean binders, e.g. "(b : Nat) (m : Mem) (hb : b < m.next)"
    statement: str                 # the conclusion, e.g. "Returns ctx fn_f.sym [...] m (fun r m' => ...)"
    origin: str = "template"       # template | llm | annotation | assumed
    strength: str = "noub"         # noub | functional
    attrs: str = "@[cir_spec]"     # attributes on the theorem (bridge-specific)
    note: str = ""
    imports: list[str] = field(default_factory=list)   # Lean modules the statement needs (e.g. VerifOrch.Cir.Entry)

    def key(self) -> str:
        return sha256(self.binders + "\n" + self.statement)


@dataclass
class ProofScript(JsonMixin):
    tactics: str                   # tactic block, one tactic per line, without the leading `by`
    options: list[str] = field(default_factory=list)   # `set_option ... in` lines put before the theorem
    origin: str = "template"


@dataclass
class Obligation(JsonMixin):
    unit: str
    module: str                    # Lean module name, e.g. VO.default.jsmn_init
    contract: Contract
    proof: ProofScript
    imports: list[str] = field(default_factory=list)
    theorem: str = ""              # theorem name

    @classmethod
    def from_json(cls, d):
        d = dict(d)
        d["contract"] = Contract.from_json(d["contract"])
        d["proof"] = ProofScript.from_json(d["proof"])
        return super().from_json.__func__(cls, d)  # type: ignore[attr-defined]


@dataclass
class LeanMessage(JsonMixin):
    severity: str
    line: int
    col: int
    text: str


@dataclass
class ObligationResult(JsonMixin):
    status: str                    # proved | stuck | error | timeout | cached
    seconds: float = 0.0
    goals: list[str] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)
    axioms: list[str] = field(default_factory=list)
    cache_key: str = ""
    messages: list[LeanMessage] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return self.status in ("proved", "cached")

    @classmethod
    def from_json(cls, d):
        d = dict(d)
        d["messages"] = [LeanMessage.from_json(m) for m in d.get("messages", [])]
        return super().from_json.__func__(cls, d)  # type: ignore[attr-defined]


@dataclass
class ConcreteInput(JsonMixin):
    unit: str
    args: Any                      # bridge-specific JSON
    note: str = ""


@dataclass
class ReplayResult(JsonMixin):
    mode: str                      # native | semantic
    outcome: str                   # ok | ub | crash | timeout | exception | error
    detail: str = ""
    confirmed: bool = False        # True when the replay shows the failure the obligation predicted


@dataclass
class Finding(JsonMixin):
    unit: str
    variant: str
    summary: str
    goals: list[str] = field(default_factory=list)
    counterexample: ConcreteInput | None = None
    replays: list[ReplayResult] = field(default_factory=list)
    verdict: str = "unconfirmed"   # real_bug | missing_precondition | spec_too_strong | tool_gap | unconfirmed
    explanation: str = ""
    contract: dict | None = None   # {binders, statement, tactics} of the obligation that failed (patch loop input)

    @classmethod
    def from_json(cls, d):
        d = dict(d)
        if d.get("counterexample"):
            d["counterexample"] = ConcreteInput.from_json(d["counterexample"])
        d["replays"] = [ReplayResult.from_json(r) for r in d.get("replays", [])]
        return super().from_json.__func__(cls, d)  # type: ignore[attr-defined]


@dataclass
class Patch(JsonMixin):
    unit: str
    diff: str                      # unified diff, paths relative to the target root
    rationale: str = ""
    kind: str = "guard"            # guard | type_widen | general


@dataclass
class PatchCertificate(JsonMixin):
    unit: str
    new_safe: str = ""             # theorem name: patched function meets the contract on all valid inputs
    new_safe_status: str = "missing"
    conservative: str = ""         # theorem name: EquivOn (original unsafe) new old
    conservative_status: str = "missing"
    changed_set: str = ""          # human-readable description of the inputs whose behaviour changed
    corollary: str = "VerifOrch.changed_iff_unsafe"
    notes: str = ""


def write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if hasattr(obj, "to_json"):
        obj = obj.to_json()
    elif isinstance(obj, list):
        obj = [o.to_json() if hasattr(o, "to_json") else o for o in obj]
    # a temporary name per process and thread: concurrent writers of one file (e.g. two variants storing the
    # same cache entry) must not rename each other's temporary file
    tmp = path.with_suffix(path.suffix + f".{os.getpid()}.{threading.get_ident()}.tmp")
    tmp.write_text(json.dumps(obj, indent=1, sort_keys=True) + "\n")
    tmp.replace(path)


def read_json(path: Path) -> Any:
    return json.loads(path.read_text())
