"""CI old ≡ new for a changed Java method, through equiv-lean's Jimple bridge (`equiv_jimple`,
EquivLean.Bridge.Jimple.Auto, in veriforch's pinned copy of equiv-lean built against JimpleLean 20261025T0149Z).

Each revision's Jimple is imported whole (`jimple_import "<dir>"`, from a content-addressed copy of its .jimple files:
Lake does not track them, and the module's name and text follow their digest) into the run's equivalence package
(`lean_eqj`), whose JimpleLean is the one equiv-lean is built against, whatever VO_JIMPLE_DIR the scheduler uses. One
module per changed method states, with the method's own declaration on both sides (`P.«C».«m(params)».ref`, or
`m(params):ret` where the class declares two methods differing only in the return type, as JimpleLean names them):

    theorem equivalent (recv : Addr) (x0 : I32) … (σ : State) :
        Equiv (· = ·) (Call.mk New.prog mNew [.ref recv, .int x0, …] σ) (Call.mk Old.prog mOld [… same …] σ) := by
      equiv_jimple

Partial correctness (a diverging run has no outcome); equal outcomes are the same return value or exception and the
same final state. The receiver of an instance method and reference parameters are non-null addresses into an arbitrary
heap; int/short/byte/char/boolean are `.int x` (any 32-bit value), long `.long x`, float/double their bit vectors.
Verdicts:
* `equivalent`: the theorem, with standard axioms only;
* `behaviour_changed`: equiv_jimple's runs of both versions on sampled arguments end differently. R is equality and
  the statement has no precondition, so a sampled disagreement is a counterexample (reported as the tactic shows it);
* `unknown`, with the reason: equiv_jimple's message otherwise (argument types it cannot sample, loops that do not
  correspond one to one or run out of lockstep, a product it cannot close within `jimple.maxHeartbeats`), a timeout,
  or a changed signature;
* `unchanged`: the method's class file is byte-identical in both revisions (javac output), so the change CI sees is
  Soot's: its local splitting and packing are not deterministic across runs (T1 thrift, 10-25: `readVarint32` with
  `result#1_1`/`result#1_2` assigned differently). No statement is made; as for any unchanged method, its callees may
  still have changed.
"""
from __future__ import annotations

import os
import re
import subprocess
from pathlib import Path

from ...lean import RUN1, VO_ROOT, LeanPackage, Requirement
from ...model import Unit, sha256
from ..base import Build, _ident
from . import build as jb

EQUIVLEAN_J = Path(os.environ.get("VO_EQUIVLEAN_JIMPLE_DIR", str(VO_ROOT / "deps" / "equivlean-751764f-jimple-0149Z")))
EQUIVLEAN_J_PIN = os.environ.get("VO_EQUIVLEAN_JIMPLE_PIN", "equivlean-751764f")
EQ_JIMPLE = Path(os.environ.get("VO_EQUIVLEAN_JIMPLE_JIMPLELEAN_DIR",
                                str(VO_ROOT / "deps" / "JimpleLean-20261025T0149Z")))
EQ_JIMPLE_PIN = os.environ.get("VO_EQUIVLEAN_JIMPLE_JIMPLELEAN_PIN", "snapshot-20261025T0149Z")
EQ_TARGET = "EquivLean.Bridge.Jimple.Auto"
# jvc's heartbeat budget per symbolic execution inside equiv_jimple (equiv_jimple's own default is 400000) and the
# wall clock of one verdict module
JVC_HEARTBEATS = int(os.environ.get("VO_EQUIV_JIMPLE_HEARTBEATS", "400000"))
VERDICT_TIMEOUT = int(os.environ.get("VO_EQUIV_JIMPLE_TIMEOUT", "900"))
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
_INT_LIKE = {"int", "short", "byte", "char", "boolean"}
_DIFF_RE = re.compile(r"the two methods end differently on (\d+) of (\d+) sampled inputs \(a counterexample if it meets "
                      r"the precondition\), e\.g\. (.*)", re.S)


class EqjPackage(LeanPackage):
    """The run's equivalence package: JimpleLean (equiv-lean's snapshot) required, equiv-lean on LEAN_PATH (built by
    `ensure_equivlean`, never by Lake here)."""

    def lean_path(self) -> str:
        return super().lean_path() + ":" + str(EQUIVLEAN_J / ".lake/build/lib/lean")


def eq_package(run_dir: Path) -> EqjPackage:
    pkg = EqjPackage(run_dir / "lean_eqj", "vo_" + _ident(run_dir.name) + "_eqj",
                     [Requirement("JimpleLean", str(EQ_JIMPLE), EQ_JIMPLE_PIN, ["Jimple"])], ["VOEqJ"],
                     run_dir / "cache" / "olean_eqj")
    pkg.pin = f"JimpleLean@{EQ_JIMPLE_PIN};equivlean@{EQUIVLEAN_J_PIN}"     # equiv-lean is part of every cache key
    return pkg


def ensure_equivlean() -> None:
    """Build the pinned equiv-lean's Jimple bridge once (Lake skips up-to-date work). Its lakefile must require the
    JimpleLean of the equivalence package, or its oleans would not load next to the imported programs."""
    lf = (EQUIVLEAN_J / "lakefile.toml").read_text()
    m = re.search(r'name = "JimpleLean"\s*\npath = "([^"]+)"', lf)
    if not m or (EQUIVLEAN_J / m.group(1)).resolve() != EQ_JIMPLE.resolve():
        raise RuntimeError(f"{EQUIVLEAN_J} is not built against {EQ_JIMPLE}")
    stamp = EQUIVLEAN_J / ".vo_built"
    want = f"{EQUIVLEAN_J_PIN}:{EQ_TARGET}"
    if stamp.exists() and stamp.read_text() == want:
        return
    p = subprocess.run([str(RUN1), "-t", "1800", "-m", "64", "-c", "0.6", "--", "lake", "build", EQ_TARGET],
                       cwd=EQUIVLEAN_J, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=1900)
    if p.returncode != 0:
        raise RuntimeError(f"equiv-lean build failed:\n{p.stdout[-3000:]}")
    stamp.write_text(want)


def program_module(pkg: EqjPackage, b: Build, run_dir: Path) -> tuple[str, str]:
    """The build's whole program in the equivalence package: (module, cache key). The module imports a copy of the
    build's .jimple files stored under their digest, and is named after it."""
    files = sorted(f for f in Path(b.info["jimple_dir"]).glob("*.jimple") if not f.name.startswith("META-INF."))
    if not files:
        raise RuntimeError(f"no .jimple files in {b.info['jimple_dir']}")
    texts = [(f.name, f.read_text()) for f in files]
    digest = sha256("".join(n + "\n" + t for n, t in texts))
    store = run_dir / "cache" / "jimple_eqj" / digest[:24]
    if not store.exists():
        tmp = store.with_name(f"{store.name}.{os.getpid()}.tmp")
        tmp.mkdir(parents=True, exist_ok=True)
        for n, t in texts:
            (tmp / n).write_text(t)
        try:
            tmp.rename(store)
        except OSError:
            if not store.exists():
                raise
    mod = f"VOEqJ.P_{digest[:16]}"
    text = "\n".join(["/- Generated by veriforch (adapters/jimple/equiv.py): one revision's whole program, for old ≡ new "
                      "verdicts. -/", "import Jimple", "", f'jimple_import "{store}" as {mod}', ""])
    r = pkg.check(mod, text, {}, timeout=900, mem_gib=64, core_h=0.3)
    if not r.ok:
        raise RuntimeError(f"the program of revision {b.target.version} does not import in the equivalence package: "
                           f"{r.errors[:2]}")
    return mod, r.cache_key


def method_key(b: Build, u: Unit) -> str:
    """JimpleLean's name of the method in its class: `name(params)`, with `:ret` when two declarations share it."""
    s = u.signature or {}
    key = f"{s.get('name')}({','.join(s.get('params', []))})"
    dup = (b.info.get("dup_keys") or {}).get(s.get("cls"))
    if dup is None:
        f = Path(b.info["jimple_dir"]) / f"{s.get('cls')}.jimple"
        dup = [k for k, n in jb.declared_keys(f.read_text()).items() if n > 1] if f.exists() else []
    return key + (f":{s.get('ret')}" if key in dup else "")


def arguments(u: Unit) -> tuple[str, str]:
    """(binders, argument list) of the call: the receiver first for an instance method, then the parameters."""
    s = u.signature or {}
    binders, args = [], []
    if not s.get("static"):
        binders.append("(recv : Addr)")
        args.append(".ref recv")
    for i, t in enumerate(s.get("params", [])):
        if t in _INT_LIKE:
            binders.append(f"(x{i} : I32)")
            args.append(f".int x{i}")
        elif t == "long":
            binders.append(f"(x{i} : I64)")
            args.append(f".long x{i}")
        elif t in ("float", "double"):
            binders.append(f"(x{i} : BitVec {32 if t == 'float' else 64})")
            args.append(f".{t} x{i}")
        else:
            binders.append(f"(a{i} : Addr)")
            args.append(f".ref a{i}")
    return " ".join(binders), "[" + ", ".join(args) + "]"


def render(mod: str, binders: str, args: str, old_mod: str, new_mod: str, cls: str, key_old: str, key_new: str) -> str:
    def ref(m: str, k: str) -> str:
        return f"{m}.«{cls}».«{k}».ref"
    return "\n".join([
        "/- Generated by veriforch (adapters/jimple/equiv.py): old ≡ new for one changed method. -/",
        f"import {EQ_TARGET}", f"import {old_mod}", f"import {new_mod}", "",
        "open Jimple EquivLean EquivLean.Jimple", "",
        "set_option maxHeartbeats 4000000", "set_option maxRecDepth 30000",
        f"set_option jimple.maxHeartbeats {JVC_HEARTBEATS}", "",
        f"namespace {mod}", "",
        "/-- old ≡ new: the same outcome (return value or exception, and final state) on every input whose run "
        "terminates. -/",
        f"theorem equivalent {binders} (σ : State) :".replace("  ", " "),
        "    Equiv (· = ·)",
        f"      (Call.mk {new_mod}.prog {ref(new_mod, key_new)} {args} σ)",
        f"      (Call.mk {old_mod}.prog {ref(old_mod, key_old)} {args} σ) := by",
        "  equiv_jimple", "",
        f"end {mod}", "", f"#print axioms {mod}.equivalent", ""])


def verdict(adapter, u_old: Unit, u_new: Unit, b_old: Build, b_new: Build, run_dir: Path) -> dict:
    so, sn = u_old.signature or {}, u_new.signature or {}
    shape = lambda s: (s.get("params"), s.get("ret"), bool(s.get("static")))     # noqa: E731
    if shape(so) != shape(sn):
        return {"verdict": "unknown", "detail": f"signature changed: {so.get('ret')} ({', '.join(so.get('params', []))})"
                f"{' static' if so.get('static') else ''} became {sn.get('ret')} ({', '.join(sn.get('params', []))})"
                f"{' static' if sn.get('static') else ''}; old ≡ new is not stated"}
    cf_old, cf_new = (Path(b.info.get("classes", "")) / (sn["cls"].replace(".", "/") + ".class") for b in (b_old, b_new))
    if cf_old.is_file() and cf_new.is_file() and cf_old.read_bytes() == cf_new.read_bytes():
        return {"verdict": "unchanged", "detail": "the class file is byte-identical in both revisions (javac output); "
                "the Jimple differs only by Soot's local naming and packing, a front-end artefact"}
    pkg = eq_package(run_dir)
    pkg.ensure()
    ensure_equivlean()
    old_mod, k_old = program_module(pkg, b_old, run_dir)
    new_mod, k_new = program_module(pkg, b_new, run_dir)
    if old_mod == new_mod:
        raise RuntimeError(f"both revisions have the same Jimple ({old_mod}): refusing a vacuous comparison")
    binders, args = arguments(u_new)
    eid = jb._component(_ident(f"{u_new.name}_{old_mod[-16:]}_{new_mod[-16:]}"))
    mod = f"VOEqJ.V.{eid}"
    text = render(mod, binders, args, old_mod, new_mod, sn["cls"], method_key(b_old, u_old), method_key(b_new, u_new))
    res = pkg.check(mod, text, {old_mod: k_old, new_mod: k_new}, timeout=VERDICT_TIMEOUT, mem_gib=64,
                    core_h=max(0.3, 1.25 * VERDICT_TIMEOUT / 3600))
    out = {"module": mod, "seconds": res.seconds, "programs": {"old": old_mod, "new": new_mod},
           "statement": "Equiv (· = ·) new old: partial correctness; receiver and reference arguments non-null, "
                        "any heap; equiv_jimple"}
    errs = [m.text for m in res.messages if m.severity == "error"]
    ax = None
    for m in res.messages:
        mm = re.search(r"'([^']+)' depends on axioms: \[(.*)\]", m.text, re.S)
        if mm and mm.group(1).endswith(".equivalent"):
            ax = [a.strip() for a in mm.group(2).split(",") if a.strip()]
    if not errs and res.status != "timeout" and res.ok and ax is not None and set(ax) <= STD_AXIOMS:
        return {**out, "verdict": "equivalent", "theorem": f"{mod}.equivalent", "axioms": ax}
    for e in errs:
        d = _DIFF_RE.search(e)
        if d:
            sample = " ".join(d.group(3).split("\n")[0].split())[:800]
            ts = re.fullmatch(r"arguments \((.*)\): target (.*), source (.*)", sample)
            same = " (the rendered results are the same: the final states differ)" if ts and ts.group(2) == ts.group(3) \
                else ""
            return {**out, "verdict": "behaviour_changed", "witness": {"args": sample},
                    "detail": f"{d.group(1)} of {d.group(2)} sampled inputs end differently{same} (R is equality and the "
                              "statement has no precondition: a counterexample)"}
    if res.status == "timeout":
        detail = f"timeout after {VERDICT_TIMEOUT} s"
    elif errs:
        detail = " ".join(errs[0].split())[:600]
    elif ax is not None:
        detail = f"non-standard axioms: {ax}"
    else:
        detail = f"status {res.status}: {(res.errors or [''])[0][:300]}"
    return {**out, "verdict": "unknown", "detail": detail}
