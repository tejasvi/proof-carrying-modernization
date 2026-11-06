"""Test promotion (DESIGN.md step 2), language-independent part.

A test case is turned into two harnesses written in the target language:

* concrete: the test's literal inputs inlined and its original checks kept as assertions. It must pass
  when run natively; its theorem is the test itself, stated in the bridge's semantics.
* symbolic: literal inputs lifted to parameters. Checks that compare a result with an input-specific
  expected value are dropped (they hold only for the test's input); checks relating results to inputs or
  to each other are kept. Its theorem: for every valid input, the harness runs without undefined
  behaviour / panics and every kept assertion holds.

Symbolic harnesses that are identical up to the lifted literals are merged: one theorem then covers all
the test cases it came from. The language adapter extracts test cases, writes the harness code, compiles
it, and renders the theorem statements; this module holds the records, the policy, and the driver.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Protocol

from .model import Contract, Target, Variant, sha256, write_json


@dataclass
class Arg:
    text: str                      # source text at the call site
    kind: str                      # string | int | enum | expr
    value: Any = None              # decoded literal value when known
    ctype: str = ""


@dataclass
class TestCase:
    name: str                      # e.g. test_object#2
    origin: str                    # file:line
    function: str                  # the test function it comes from
    kind: str                      # wrapper_call | whole_function
    wrapper: str = ""              # helper called by a wrapper_call case
    args: list[Arg] = field(default_factory=list)
    stmt: str = ""                 # source text of the statement (wrapper_call) or function body (whole_function)
    inputs: list[str] = field(default_factory=list)          # what is lifted in the symbolic version
    expected: list[str] = field(default_factory=list)        # input-specific checks dropped there
    kept: list[str] = field(default_factory=list)            # relational checks kept there


@dataclass
class Param:
    name: str
    ctype: str
    role: str                      # cstring | int | buffer | scalar
    elem: str = ""                 # buffer element type (record name for structs)
    count: str = ""                # buffer: name of the parameter bounding the element count
    lo: int | None = None
    hi: int | None = None


@dataclass
class Harness:
    name: str                      # function name in the harness file (vo_hc_* / vo_hs_*)
    kind: str                      # concrete | symbolic
    cases: list[str]               # test cases it covers
    params: list[Param] = field(default_factory=list)
    code: str = ""                 # the harness function's source
    kept_checks: list[str] = field(default_factory=list)
    dropped_checks: list[str] = field(default_factory=list)
    native: str = "not_run"        # pass | fail:<line> | error | not_run (concrete only)
    translated: bool = False       # the bridge's front end produced a unit for it
    scope: str = ""                # bridge scope status of the harness unit
    contract: dict | None = None   # Contract JSON of its theorem
    statement_ok: str = "unchecked"   # ok | error:<msg> | unchecked
    note: str = ""

    def key(self) -> str:
        return sha256(self.code)


@dataclass
class PromotionReport:
    target: str
    variant: str
    cases: list[TestCase]
    harnesses: list[Harness]
    harness_file: str = ""
    native_log: str = ""

    def stats(self) -> dict[str, int]:
        con = [h for h in self.harnesses if h.kind == "concrete"]
        sym = [h for h in self.harnesses if h.kind == "symbolic"]
        return {
            "test_cases": len(self.cases),
            "concrete_harnesses": len(con),
            "symbolic_harnesses": len(sym),
            "concrete_native_pass": sum(h.native == "pass" for h in con),
            "translated": sum(h.translated for h in self.harnesses),
            "in_scope": sum(h.scope == "in_scope" for h in self.harnesses),
            "statement_ok": sum(h.statement_ok == "ok" for h in self.harnesses),
        }

    def to_json(self) -> dict:
        import dataclasses
        return {"target": self.target, "variant": self.variant, "stats": self.stats(),
                "harness_file": self.harness_file, "native_log": self.native_log,
                "cases": [dataclasses.asdict(c) for c in self.cases],
                "harnesses": [dataclasses.asdict(h) for h in self.harnesses]}


class Promoter(Protocol):
    """What a language adapter provides for test promotion."""

    def extract(self, target: Target, variant: Variant, work: Path) -> list[TestCase]: ...

    def generate(self, target: Target, variant: Variant, cases: list[TestCase], work: Path) -> tuple[list[Harness], Path]: ...

    def run_native(self, target: Target, variant: Variant, harnesses: list[Harness], harness_file: Path, work: Path) -> str: ...

    def translate(self, target: Target, variant: Variant, harnesses: list[Harness], harness_file: Path, run_dir: Path): ...

    def contracts(self, build, harnesses: list[Harness]) -> None: ...

    def check_statements(self, build, harnesses: list[Harness]) -> None: ...


def merge_symbolic(harnesses: list[Harness]) -> list[Harness]:
    """Merge symbolic harnesses with identical code (they differ only in the literals that were lifted)."""
    out: list[Harness] = []
    seen: dict[str, Harness] = {}
    for h in harnesses:
        if h.kind != "symbolic":
            out.append(h)
            continue
        k = h.key()
        if k in seen:
            for c in h.cases:
                if c not in seen[k].cases:
                    seen[k].cases.append(c)
            for d in h.dropped_checks:
                if d not in seen[k].dropped_checks:
                    seen[k].dropped_checks.append(d)
            continue
        seen[k] = h
        out.append(h)
    return out


def promote(promoter: Promoter, target: Target, variant: Variant, run_dir: Path, *, native: bool = True,
            translate: bool = True, check: bool = True, log=print) -> PromotionReport:
    """Extract, generate, run natively, translate, render theorems, and check that they elaborate."""
    work = run_dir / target.version / variant.name / "promote"
    work.mkdir(parents=True, exist_ok=True)
    cases = promoter.extract(target, variant, work)
    log(f"[{variant.name}] {len(cases)} test cases")
    harnesses, hfile = promoter.generate(target, variant, cases, work)
    harnesses = merge_symbolic(harnesses)
    rep = PromotionReport(target.name, variant.name, cases, harnesses, str(hfile))
    if native:
        rep.native_log = promoter.run_native(target, variant, harnesses, hfile, work)
    if translate:
        build = promoter.translate(target, variant, harnesses, hfile, run_dir)
        if build is not None:
            promoter.contracts(build, harnesses)
            if check:
                promoter.check_statements(build, harnesses)
    write_json(work / "promote.json", rep)
    log(f"[{variant.name}] {rep.stats()}")
    return rep
