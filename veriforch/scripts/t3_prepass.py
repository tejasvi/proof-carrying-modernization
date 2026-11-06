"""Pre-registration T, step T3: the front-end pre-pass of one commit and one language (C1's procedure, as in
scripts/prereg_c.py `changed_functions`: materialise + build of both revisions, as `vo ci` does; no Lean run for
C/C++ and Java, no model call). It gives the changed functions, which fix the budget B, and the TUs `vo ci` names.

    <frozen>/.venv/bin/python -B t3_prepass.py SPEC.json OUT.json

SPEC: {"target": TOML, "base": SHA, "head": SHA, "run_dir": DIR, "changed_files": [paths relative to the target
root, from `git diff --name-only base head`]}. Run with VO_ROOT and PYTHONPATH on the frozen copy and the bridge pins
in the environment (the same as the `vo ci` run that follows).

C and C++ (a compile_commands target, one variant per TU):
1. both revisions are materialised (veriforch.ci.materialise: git archive, flags re-rooted);
2. a TU is affected when its source or a file in its include closure (clang -MM with the TU's flags, exactly as
   adapters/cir/build.py compiles it; preprocessing only) at the base or at the head is a changed file; a TU whose
   closure cannot be computed counts as affected;
3. every affected TU is built at both revisions (adapter.build: clang -fclangir, cir2lean, cirscan); a failure is
   recorded with the revision and the error (blocked: build); otherwise its changed units are the units present at
   both revisions whose body hash differs (as veriforch.ci.run_ci).
Java and Rust (one variant): both revisions are built (adapter.build) and compared the same way.
OUT: {"variants": {name: {"affected": bool, "why": ..., "blocked": {...} | null, "changed": [...], "added": [...],
"removed": [...], "units": {name: {"loc": rel path:line, "body_hash": ...}}, "seconds": s}}, "order": [variant
names in target order], "error": null | text}.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
import time
import traceback
from pathlib import Path


def rel_loc(loc: str, root: str) -> str:
    """`file:line` of a unit, with the file relative to the materialised revision's root."""
    if not loc:
        return ""
    f, _, line = loc.rpartition(":")
    try:
        f = str(Path(f).resolve().relative_to(Path(root).resolve()))
    except ValueError:
        pass
    return f"{f}:{line}"


def deps_of(cbuild, t, v, work: Path) -> set[str] | None:
    """The include closure of TU variant v at revision t (absolute paths), by clang -MM with the build's flags."""
    root = Path(t.root)
    srcs = v.sources or t.sources
    if len(srcs) != 1:
        return None
    src = root / srcs[0]
    is_cxx = srcs[0].endswith((".cpp", ".cc", ".cxx", ".hpp"))
    cmd = [str(cbuild.CLANG if not is_cxx else cbuild.TOOLCHAIN / "bin" / "clang++")]
    if is_cxx:
        cmd += ["-std=c++20"] + t.extra.get("cxxflags", [])
    work.mkdir(parents=True, exist_ok=True)
    dfile = work / (re.sub(r"\W", "_", v.name) + ".d")
    if dfile.exists():
        dfile.unlink()
    cmd += [f"-I{root / i}" for i in t.include] + v.flags + t.extra.get("cflags", [])
    cmd += ["-MM", "-MF", str(dfile), str(src)]
    p = cbuild.run_tool(cmd, work, timeout=300, core_h=0.05)
    if p.returncode != 0 or not dfile.exists():
        return None
    text = dfile.read_text().replace("\\\n", " ")
    body = text.split(":", 1)[1] if ":" in text else ""
    out = set()
    for tok in body.split():
        out.add(str((work / tok).resolve()) if not Path(tok).is_absolute() else str(Path(tok).resolve()))
    return out


def deps_batch(cbuild, t, vs: list, work: Path) -> dict[str, set[str] | None]:
    """The include closures of several TU variants of revision t at once: one `clang -MM` per group of TUs with the
    same compiler and flags (each input is preprocessed on its own; the first dependency of each rule is its source).
    A group whose call fails falls back to one call per TU (deps_of)."""
    root = Path(t.root)
    groups: dict[tuple, list] = {}
    for v in vs:
        srcs = v.sources or t.sources
        is_cxx = len(srcs) == 1 and srcs[0].endswith((".cpp", ".cc", ".cxx", ".hpp"))
        groups.setdefault((is_cxx, tuple(v.flags)), []).append(v)
    out: dict[str, set[str] | None] = {}
    work.mkdir(parents=True, exist_ok=True)
    for (is_cxx, flags), group in groups.items():
        cmd = [str(cbuild.CLANG if not is_cxx else cbuild.TOOLCHAIN / "bin" / "clang++")]
        if is_cxx:
            cmd += ["-std=c++20"] + t.extra.get("cxxflags", [])
        cmd += [f"-I{root / i}" for i in t.include] + list(flags) + t.extra.get("cflags", []) + ["-MM"]
        srcs = {str((root / (v.sources or t.sources)[0]).resolve()): v.name for v in group}
        p = subprocess.run([str(cbuild.RUN1), "-t", "900", "-c", "0.3", "--", *cmd, *srcs], cwd=work,
                           capture_output=True, text=True, timeout=1000)
        got: dict[str, set[str]] = {}
        if p.returncode == 0:
            for rule in p.stdout.replace("\\\n", " ").split("\n"):
                if ":" not in rule:
                    continue
                deps = [str((work / x).resolve()) if not Path(x).is_absolute() else str(Path(x).resolve())
                        for x in rule.split(":", 1)[1].split()]
                if deps and deps[0] in srcs:
                    got[srcs[deps[0]]] = set(deps)
        for v in group:
            out[v.name] = got[v.name] if v.name in got else deps_of(cbuild, t, v, work)
    return out


def unit_map(b, root: str) -> dict:
    return {u.name: {"loc": rel_loc(u.loc, root), "body_hash": u.body_hash} for u in b.units}


def compare(ub: dict, uh: dict) -> tuple[list, list, list]:
    changed = sorted(n for n in uh if n in ub and uh[n]["body_hash"] != ub[n]["body_hash"])
    return changed, sorted(set(uh) - set(ub)), sorted(set(ub) - set(uh))


def main(spec_path: str, out_path: str) -> int:
    from veriforch.ci import _variant_at, materialise
    from veriforch.cli import adapter_for
    from veriforch.config import load_target
    spec = json.loads(Path(spec_path).read_text())
    t = load_target(spec["target"])
    rd = Path(spec["run_dir"])
    rd.mkdir(parents=True, exist_ok=True)
    ad = adapter_for(t.lang)
    res: dict = {"variants": {}, "order": [v.name for v in t.variants], "error": None, "lang": t.lang}
    tb, th = materialise(t, spec["base"], rd), materialise(t, spec["head"], rd)
    changed_files = set(spec.get("changed_files") or [])
    multi = t.lang == "cir" and bool(t.extra.get("compile_commands"))
    if multi:
        from veriforch.adapters.cir import build as cbuild
        abs_changed = {str((Path(r.root) / f).resolve()) for r in (tb, th) for f in changed_files}
        # include closures of every TU present at both revisions (TUs whose own source changed need none)
        need = [v for v in t.variants if _variant_at(tb, v) is not None and _variant_at(th, v) is not None
                and (v.sources or t.sources)[0] not in changed_files]
        closures = {side: deps_batch(cbuild, r, [_variant_at(r, v) for v in need], rd / "deps" / r.version)
                    for side, r in (("base", tb), ("head", th))}
    for v in t.variants:
        t0 = time.time()
        vb, vh = _variant_at(tb, v), _variant_at(th, v)
        rec: dict = {"affected": True, "why": "single-variant library", "blocked": None, "changed": [],
                     "added": [], "removed": [], "units_base": {}, "units_head": {},
                     "source": (v.sources or t.sources or [""])[0] if multi else None}
        if vh is None or vb is None:
            rec.update(affected=False, why=f"sources absent at {'head' if vh is None else 'base'}")
            res["variants"][v.name] = rec
            continue
        if multi:
            src = (v.sources or t.sources)[0]
            if src in changed_files:
                rec["why"] = f"its source {src} changed"
            else:
                hit, unknown = [], []
                for side, r in (("base", tb), ("head", th)):
                    d = closures[side].get(v.name)
                    if d is None:
                        unknown.append(r.version)
                    else:
                        hit += sorted(str(Path(x).relative_to(Path(r.root).resolve())) for x in d & abs_changed
                                      if x.startswith(str(Path(r.root).resolve())))
                if hit:
                    rec["why"] = "includes changed " + ", ".join(sorted(set(hit)))
                elif unknown:
                    rec["why"] = f"include closure not computed at {unknown}: counted as affected"
                else:
                    rec.update(affected=False, why="no changed file in its include closure")
        if rec["affected"]:
            builds = {}
            for side, r, vv in (("base", tb, vb), ("head", th, vh)):
                try:
                    builds[side] = ad.build(r, vv, rd)
                except Exception as e:
                    rec["blocked"] = {"revision": side, "rev": r.version, "error": f"{type(e).__name__}: {e}"[-4000:]}
                    break
            if rec["blocked"] is None:
                ub, uh = unit_map(builds["base"], tb.root), unit_map(builds["head"], th.root)
                rec["changed"], rec["added"], rec["removed"] = compare(ub, uh)
                rec["units_base"] = {n: ub[n] for n in rec["changed"] + rec["removed"]}
                rec["units_head"] = {n: uh[n] for n in rec["changed"] + rec["added"]}
        rec["seconds"] = round(time.time() - t0, 1)
        res["variants"][v.name] = rec
    Path(out_path).write_text(json.dumps(res, indent=1))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1], sys.argv[2]))
    except Exception as e:                      # recorded for the driver: a pre-pass crash is not a verdict
        Path(sys.argv[2]).write_text(json.dumps({"error": f"{type(e).__name__}: {e}"[-3000:],
                                                 "traceback": traceback.format_exc()[-6000:]}))
        sys.exit(1)
