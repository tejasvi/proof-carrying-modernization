"""The interface every bridge adapter implements (see DESIGN.md)."""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from ..lean import LeanPackage
from ..model import (ConcreteInput, Contract, Obligation, Patch, ProofScript, ReplayResult, Target, Unit,
                     Variant)


@dataclass
class Build:
    """Artifacts of one variant of one source version."""
    target: Target
    variant: Variant
    dir: Path                        # runs/<name>/<version>/<variant>/
    pkg: LeanPackage                 # the generated Lake package
    gen_modules: dict[str, str] = field(default_factory=dict)   # Lean module -> cache key
    units: list[Unit] = field(default_factory=list)
    info: dict[str, Any] = field(default_factory=dict)          # adapter-specific (IR paths, scan JSON, ...)

    @property
    def ns(self) -> str:
        """Lean namespace prefix for this build's generated modules (an adapter may choose a revision-independent
        one, e.g. modular C builds, whose revisions have separate packages)."""
        return self.info.get("ns") or f"VO.{_ident(self.target.version)}.{_ident(self.variant.name)}"


@dataclass
class PromotedTest:
    name: str                        # e.g. test_object_1
    origin: str                      # file:line of the original test
    kind: str                        # symbolic | concrete
    harness_unit: str                # unit name of the generated harness function
    contract: Contract | None = None # the theorem: harness runs without UB and all assertions pass
    note: str = ""


class Adapter:
    lang = "?"

    def build(self, target: Target, variant: Variant, run_dir: Path) -> Build:
        raise NotImplementedError

    def noub_contract(self, unit: Unit, build: Build) -> Contract:
        raise NotImplementedError

    def default_proof(self, unit: Unit, build: Build) -> ProofScript:
        raise NotImplementedError

    def render(self, ob: Obligation, build: Build) -> str:
        raise NotImplementedError

    def promote_tests(self, target: Target, build: Build, run_dir: Path) -> list[PromotedTest]:
        raise NotImplementedError

    def replay(self, unit: Unit, inp: ConcreteInput, build: Build, mode: str) -> ReplayResult:
        raise NotImplementedError

    def apply_patch(self, target: Target, patch: Patch, run_dir: Path) -> Target:
        raise NotImplementedError

    def prompt_pack(self) -> str:
        raise NotImplementedError


def _ident(s: str) -> str:
    out = "".join(c if c.isalnum() else "_" for c in s)
    return out if out[:1].isalpha() else "v" + out
