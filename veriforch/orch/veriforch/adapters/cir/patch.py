"""C patches: apply a source patch to a new version tree, and render/check its certificate.

The certificate module of a patch of unit `f` (version vOld -> vNew) has three theorems:

* `new_safe`: the patched function satisfies the unit's contract (no UB, returns normally, `post`);
* `conservative`: equiv-lean's `EquivOn (VerifOrch.Cir.Bad WT ctxOld fOld) ctxNew fNew ctxOld fOld`:
  on every well-typed call where the original is safe, both versions have the same caller-visible
  outcome. A well-typed call has the contract's argument shapes, and each pointer argument points into
  a block that exists at the call;
* `changed_iff_unsafe`: the instance of `VerifOrch.Cir.changed_iff_unsafe_at` at the contract's
  calls: the outcome changed exactly when the original was unsafe.

Certificates are checked in the run's generated Lean package with equiv-lean (pinned snapshot
built against the same cirlean) and veriforch's `VerifOrch` library added to `LEAN_PATH`.
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
from pathlib import Path

from ...lean import RUN1, VO_ROOT, LeanPackage, Requirement
from ...model import ObligationResult, Patch, Target, Variant
from ..base import _ident
from . import build as cbuild

# The equiv-lean snapshot certificates and CI verdicts use, and the cirlean it is built against. scripts/vo sets
# all four from scripts/cert_pin.env for `ci` and `patch` (one file to change when equiv-lean re-pins).
EQUIVLEAN = Path(os.environ.get("VO_EQUIVLEAN_DIR", str(VO_ROOT / "deps" / "equivlean-32d231d")))
EQUIVLEAN_PIN = os.environ.get("VO_EQUIVLEAN_PIN", "equivlean-32d231d")
VERIFORCH_LEAN = ["VerifOrch/Patch.lean", "VerifOrch/Int.lean", "VerifOrch/Cir/Patch.lean"]


# Certificates use the cirlean that the pinned equiv-lean snapshot was built against (the scheduler builds the
# compared versions with the same cirlean: scripts/vo sets VO_CIRLEAN_* to it for `ci` and `patch`).
CERT_CIRLEAN = Path(os.environ.get("VO_CERT_CIRLEAN_DIR", str(cbuild.VO_ROOT / "deps" / "cirlean")))   # 87a2905
CERT_CIRLEAN_PIN = os.environ.get("VO_CERT_CIRLEAN_PIN", "87a2905")


class CertPackage(LeanPackage):
    """The run's generated package, with equiv-lean on LEAN_PATH (never built by Lake here)."""

    def lean_path(self) -> str:
        return super().lean_path() + ":" + str(EQUIVLEAN / ".lake/build/lib/lean")


def cert_package(run_dir: Path) -> CertPackage:
    reqs = [Requirement("cirlean", str(CERT_CIRLEAN), CERT_CIRLEAN_PIN, ["CIR"]),
            Requirement("equivlean", str(EQUIVLEAN), EQUIVLEAN_PIN, [])]
    # a package of its own: it pins equiv-lean's cirlean, which may differ from the scheduler's
    pkg = CertPackage(run_dir / "lean_cert", "vo_" + _ident(run_dir.name) + "_cert", reqs[:1], ["Gen", "VO", "VerifOrch", "VOCert", "VOEquiv"],
                      run_dir / "cache" / "olean_cert")
    pkg.pin = ";".join(f"{r.name}@{r.pin}" for r in reqs)   # equiv-lean is part of every certificate key
    return pkg


def ensure_equivlean() -> None:
    """Build the pinned equiv-lean snapshot's cirlean bridge (Lake skips up-to-date work)."""
    stamp = EQUIVLEAN / ".vo_built"
    targets = ["EquivLean.Core.Facts", "EquivLean.Bridge.Cir.Tactic", "EquivLean.Bridge.Cir.Obs",
               "EquivLean.Bridge.Cir.AutoCouple", "EquivLean.Bridge.Cir.PtrArgs"]
    want = EQUIVLEAN_PIN + ":" + ",".join(targets)
    if stamp.exists() and stamp.read_text() == want:
        return
    p = subprocess.run([str(RUN1), "-t", "1200", "-m", "128", "-c", "0.4", "--", "lake", "build", *targets],
                       cwd=EQUIVLEAN, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=1300)
    if p.returncode != 0:
        raise RuntimeError(f"equiv-lean build failed:\n{p.stdout[-3000:]}")
    stamp.write_text(want)


def ensure_verifOrch(pkg: CertPackage) -> dict[str, str]:
    """Copy VerifOrch's Lean sources into the package and check them. Returns module -> cache key."""
    keys: dict[str, str] = {}
    for rel in VERIFORCH_LEAN:
        mod = rel[:-len(".lean")].replace("/", ".")
        src = (VO_ROOT / rel).read_text()
        res = pkg.check(mod, src, dict(keys), mem_gib=64)
        if not res.ok:
            raise RuntimeError(f"{mod} does not check: {res.errors[:3]} {res.goals[:1]}")
        keys[mod] = res.cache_key
    return keys


# -- applying patches ------------------------------------------------------------------------

def new_version(target: Target, run_dir: Path, version: str) -> Target:
    """A copy of the target's source tree under runs/<t>/src/<version> (the original is never edited)."""
    if not re.fullmatch(r"v\d+[a-z0-9_]*", version):
        raise ValueError(f"bad version label {version!r}")
    runs = (VO_ROOT / "runs").resolve()
    src_root = (run_dir / "src").resolve()
    dst = (src_root / version).resolve()
    # allowlist: only runs/<target>/src/<version> may ever be replaced
    if src_root.parent.parent != runs or dst.parent != src_root:
        raise ValueError(f"refusing to write outside runs/<target>/src: {dst}")
    if dst.exists():
        shutil.rmtree(dst)
    shutil.copytree(target.root, dst, ignore=shutil.ignore_patterns(".git"))
    return Target.from_json({**target.to_json(), "root": str(dst), "version": version})


def apply_patch(target: Target, patch: Patch, run_dir: Path, version: str) -> Target:
    """Copy the tree and apply the unified diff there. Raises if the diff does not apply cleanly."""
    nt = new_version(target, run_dir, version)
    pdir = run_dir / "src" / f"{version}.diff"
    pdir.write_text(patch.diff if patch.diff.endswith("\n") else patch.diff + "\n")
    for strip in ("-p1", "-p0"):
        p = subprocess.run([str(RUN1), "-t", "60", "-c", "0.05", "--", "patch", strip, "--forward", "--batch",
                            "--no-backup-if-mismatch", "-i", str(pdir)],
                           cwd=nt.root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=120)
        if p.returncode == 0:
            return nt
        # undo a partial application before trying the other strip level
        nt = new_version(target, run_dir, version)
    raise ValueError(f"patch does not apply:\n{p.stdout[-1500:]}")


# -- certificate rendering -------------------------------------------------------------------

def split_call(statement: str) -> tuple[str, str, str]:
    """`Returns ctx fn_f.sym [ARGS] m (fun ...)` -> (decl, ARGS text including brackets, memory var)."""
    m = re.search(r"Returns\s+ctx\s+(fn_\w+)\.sym\s+", statement)
    if not m:
        raise ValueError(f"not a Returns statement: {statement[:120]}")
    i = m.end()
    if statement[i] != "[":
        raise ValueError("argument list not found")
    depth = 0
    for j in range(i, len(statement)):
        c = statement[j]
        depth += c == "["
        depth -= c == "]"
        if depth == 0:
            break
    args = statement[i:j + 1]
    rest = statement[j + 1:].split()
    return m.group(1), args, rest[0]


def binder_groups(binders: str) -> list[tuple[list[str], str, str]]:
    """Split `(a b : Int) {k : Nat} (h : P)` into (names, type, bracket) groups."""
    out, depth, start, open_c = [], 0, None, ""
    pairs = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
    for i, c in enumerate(binders):
        if depth == 0 and c in pairs:
            depth, start, open_c = 1, i, c
            continue
        if depth > 0:
            if c in "({[⦃":
                depth += 1
            elif c in ")}]⦄":
                depth -= 1
                if depth == 0:
                    inner = binders[start + 1:i]
                    if ":" in inner:
                        names, ty = inner.split(":", 1)
                        out.append((names.split(), ty.strip(), open_c))
    return out


_PROP_MARKS = ("≤", "<", "≥", ">", "=", "≠", "∧", "∨", "→", "∀", "∃", "↔", "¬")


def is_hyp(names: list[str], ty: str) -> bool:
    return any(k in ty for k in _PROP_MARKS) or all(n.startswith("h") for n in names)


def qualify(text: str, gen_ns: str) -> str:
    """Point unqualified `ctx` / `fn_*` / `rec_*` of a contract at one Gen module."""
    text = re.sub(r"(?<![\w.])ctx(?![\w])", f"{gen_ns}.ctx", text)
    return re.sub(r"(?<![\w.])(fn_\w+|rec_\w+)", lambda mm: f"{gen_ns}.{mm.group(1)}", text)


def render_certificate(cert_id: str, binders: str, statement: str, new_tactics: str, gen_old: str,
                       gen_new: str, conservative_tactics: str | None = None, imports: list[str] | None = None) -> str:
    decl, args, mem = split_call(statement)
    groups = binder_groups(binders)
    names = [n for ns, _, br in groups if br == "(" for n in ns]
    var_groups = [(ns, ty) for ns, ty, br in groups if not is_hyp(ns, ty) and mem not in ns]
    var_names = [n for ns, _ in var_groups for n in ns]
    used = [n for n in var_names if re.search(r"(?<![\w.])" + re.escape(n) + r"(?![\w])", args)]
    used_groups = [([n for n in ns if n in used], ty) for ns, ty in var_groups]
    ex = " ".join(f"({' '.join(ns)} : {ty})" for ns, ty in used_groups if ns)
    # a pointer argument of a well-typed call points into a block that exists at the call: a pointer into a block
    # the callee allocates later would alias the callee's own locals, which the two versions allocate differently
    ptrs = [n for ns, ty in used_groups for n in ns if ty.strip() == "Ptr"]
    # (bound names chosen so that they cannot capture the contract's own variable names)
    conds = [f"(∀ vo_blk vo_path, {n} = Ptr.loc vo_blk vo_path → vo_blk < vo_m.next)" for n in ptrs]
    wt_body = " ∧ ".join([f"args = {args}"] + conds)
    wt_body = f"∃ {ex}, {wt_body}" if ex else wt_body
    old_f, new_f = f"{gen_old}.{decl}.sym", f"{gen_new}.{decl}.sym"
    old_c, new_c = f"{gen_old}.ctx", f"{gen_new}.ctx"
    hwt = [f"hwt{k}" for k in range(len(conds))]
    obtain = "⟨" + ", ".join(used + ["rfl"] + hwt) + "⟩" if used else "rfl"
    cons = conservative_tactics or "\n".join([
        "intro args m hbad",
        "simp only [VerifOrch.Cir.Bad, not_or, Classical.not_not, WT] at hbad",
        f"obtain ⟨{obtain}, hsafe⟩ := hbad",
        # one simulation direction (patched = target, original = source) plus the original's safety
        # (equiv-lean's recommended shape; the reverse product direction can be false for guard patches)
        # first one simulation direction plus the original's safety (equiv-lean's recommended shape), then
        # the product of both directions with the original's no-UB facts in context
        "first",
        "  | (refine EquivLean.Equiv.of_sim_of_safe ?_ (fun _ => VerifOrch.Cir.safe_of_safeRet hsafe); equiv_cir)",
        "  | (have hs0 := VerifOrch.Cir.safe_of_safeRet hsafe; rw [safe_res_iff_holds] at hs0; cir_hrun hs0;",
        "     all_goals equiv_cir)",
    ])
    ns = f"VOCert.{_ident(cert_id)}"
    lines = [f"import {i}" for i in (["CIR", gen_old, gen_new, "EquivLean.Core.Facts", "EquivLean.Bridge.Cir.Tactic",
                                      "EquivLean.Bridge.Cir.AutoCouple", "EquivLean.Bridge.Cir.PtrArgs", "VerifOrch.Cir.Patch"]
                                     + (imports or []))]
    lines += ["", "set_option maxHeartbeats 4000000", "", f"namespace {ns}", "",
              "open CIR EquivLean EquivLean.Cir", "",
              "/-- Well-typed calls of the contract (the argument shapes). -/",
              f"def WT (args : List Val) ({'vo_m' if conds else '_m'} : Mem) : Prop := {qualify(wt_body, gen_new)}", "",
              "/-- The patched function meets the unit's contract. -/",
              f"theorem new_safe {qualify(binders.strip(), gen_new)} :",
              f"    {qualify(statement.strip(), gen_new)} := by"]
    lines += ["  " + t for t in new_tactics.strip("\n").splitlines()]
    lines += ["", "/-- Wherever the original is safe (on well-typed calls), the versions agree. -/",
              f"theorem conservative : EquivOn (VerifOrch.Cir.Bad WT {old_c} {old_f}) {new_c} {new_f} {old_c} {old_f} := by"]
    lines += ["  " + t for t in cons.strip("\n").splitlines()]
    lines += ["", "/-- On the contract's calls the outcome changed exactly where the original was unsafe. -/",
              f"theorem changed_iff_unsafe {qualify(binders.strip(), gen_new)}"
              + "".join(f" (hwt{k} : {c.replace('vo_m.next', mem + '.next')})" for k, c in enumerate(conds)) + " :",
              f"    ¬ VerifOrch.Cir.Agree {new_c} {new_f} {old_c} {old_f} {qualify(args, gen_new)} {mem} ↔",
              f"      ¬ VerifOrch.Cir.SafeRet {old_c} {old_f} {qualify(args, gen_new)} {mem} :=",
              f"  VerifOrch.Cir.changed_iff_unsafe_at (WT := WT) {('⟨' + ', '.join(used + ['rfl'] + hwt) + '⟩') if used else 'rfl'}",
              f"    (VerifOrch.Cir.safeRet_of_returns (new_safe {' '.join(names)})) conservative", ""]
    for t in ("new_safe", "conservative", "changed_iff_unsafe"):
        lines.append(f"#print axioms {t}")
    lines += ["", f"end {ns}", ""]
    return "\n".join(lines)


def check_certificate(pkg: CertPackage, cert_id: str, text: str, import_keys: dict[str, str],
                      timeout: int = 590) -> tuple[ObligationResult, dict[str, str]]:
    """Check the certificate module; report which of the three theorems failed (by error line)."""
    mod = f"VOCert.{_ident(cert_id)}"
    res = pkg.check(mod, text, import_keys, timeout=timeout, mem_gib=64, core_h=0.3)
    status = {t: "proved" for t in ("new_safe", "conservative", "changed_iff_unsafe")}
    lines = text.splitlines()
    starts = {t: next((i + 1 for i, l in enumerate(lines) if l.startswith(f"theorem {t} ")), 10**9)
              for t in status}
    order = sorted(starts.items(), key=lambda kv: kv[1])
    for msg in res.messages:
        if msg.severity != "error":
            continue
        owner = None
        for t, ln in order:
            if msg.line >= ln:
                owner = t
        if owner:
            status[owner] = "failed"
    if res.status in ("timeout", "error") and all(v == "proved" for v in status.values()):
        status = {t: res.status for t in status}
    return res, status


# -- evidence for a rejected patch -----------------------------------------------------------

INT_PROBES = [0, 1, -1, 2, 7, 1000, -1000, 1073741824, -1073741824, 1073741825, 2147483647, -2147483648,
              2147483646, -2147483647]


def disagreement_witness(pkg: CertPackage, gen_old: str, gen_new: str, decl: str, n_int_args: int,
                         import_keys: dict[str, str], limit: int = 400) -> dict | None:
    """Run both versions on boundary integer inputs (cirlean interpreter, `#eval`) and return the first
    input on which the original is safe and the outcomes differ, or None. Only for all-int signatures."""
    import itertools
    combos = list(itertools.islice(itertools.product(INT_PROBES, repeat=n_int_args), limit))
    lst = ", ".join("[" + ", ".join(f".int ({v})" for v in c) + "]" for c in combos)
    src = f"""import CIR
import {gen_old}
import {gen_new}
open CIR

def voShow : Res (Exit × Mem) → String
  | .ok (.ret (some (.int r)), _) => s!"ret {{r}}"
  | .ok (.ret none, _) => "ret void"
  | .ok _ => "other exit"
  | .ub msg => s!"ub {{msg}}"
  | .div => "diverges"

#eval Id.run do
  let mut out := ""
  for args in ([{lst}] : List (List Val)) do
    let o := voShow (evalCall {gen_old}.ctx {gen_old}.{decl}.sym args {gen_old}.module.initMem)
    let n := voShow (evalCall {gen_new}.ctx {gen_new}.{decl}.sym args {gen_new}.module.initMem)
    if o.startsWith "ret" && o != n then
      out := s!"WITNESS {{repr args}} | {{o}} | {{n}}"
      break
  return (if out == "" then "NONE" else out)
"""
    mod = "VOCert.Witness_" + _ident(gen_new.replace(".", "_")) + "_" + decl
    res = pkg.check(mod, src, import_keys, mem_gib=64, use_cache=False)
    for msg in res.messages:
        t = msg.text.strip().strip('"')
        if t.startswith("WITNESS"):
            fields = [x.strip() for x in t[len("WITNESS"):].split("|")] + ["", "", ""]
            return {"args": fields[0], "original": fields[1], "patched": fields[2]}
        if t == "NONE":
            return None
    return {"error": (res.errors or ["no output"])[0][:500]}
