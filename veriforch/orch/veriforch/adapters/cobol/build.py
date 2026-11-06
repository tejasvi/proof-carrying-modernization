"""COBOL build: surface-IR JSON programs -> one Gen module (`cobol_program` per program) -> units.

A target's sources are surface-IR JSON files (coblean's extraction contract, Cobol/Frontend/Surface.lean),
as produced by coblean's front end (tools/cobolfe) or a hand-written extractor. A build variant is a set
of compiler options applied to the JSON `config` (`"trunc=bin"`, `"sizeErrorTruncates=false"`, ...).
Units are whole programs; callees are the programs a program CALLs that are part of the target.

Source mode (target option `frontend = "cobolfe"`): the sources are COBOL programs, extracted by the front end of
the pinned coblean itself (`tools/cobolfe/cobolfe.py`, with the target's `copybook_dirs`), so front end and Lean
semantics come from one snapshot. A program the front end rejects is a unit with scope
`gap:frontend:<error class>`. With `elab_check = true`, every extracted program is first elaborated in a module of
its own (`cobol_program`); one that fails is a unit with scope `gap:elaboration:<error class>` and stays out of the
Gen module, so it cannot block the others (a census over a whole application).
"""
from __future__ import annotations

import json
import os
import re
from pathlib import Path

from ...lean import RUN1, VO_ROOT, LeanPackage, Requirement
from ...model import Target, Unit, Variant, sha256
from ..base import Build, _ident

# The pinned coblean. Override with VO_COBLEAN_DIR / VO_COBLEAN_PIN (a run with an override gets its own package
# directory, as for cirlean), e.g. a green snapshot copied into deps/ (deps/coblean-20261024T0803Z for prereg D).
COBLEAN = Path(os.environ.get("VO_COBLEAN_DIR", str(VO_ROOT / "deps" / "coblean-20261023")))
COBLEAN_PIN = os.environ.get("VO_COBLEAN_PIN", "copy-20261023T1929Z")


def lean_package(run_dir: Path) -> LeanPackage:
    req = Requirement("coblean", str(COBLEAN), COBLEAN_PIN, ["Cobol"])
    pkg_dir = run_dir / ("lean" if "VO_COBLEAN_PIN" not in os.environ else f"lean_{_ident(COBLEAN_PIN)}")
    return LeanPackage(pkg_dir, "vo_" + _ident(run_dir.name), [req], ["Gen", "VO"],
                       run_dir / "cache" / "olean")


_LOC_RE = re.compile(r"(/[^\s:]+|[\w./-]+\.(?:cbl|CBL|cob|COB|cpy|CPY)):\d+:\d+:\s*")


def error_class(text: str) -> str:
    """A tool's error class from its first error line: file positions, search-path lists and line numbers
    removed (`copybook DFHAID not found`, `OCCURS DEPENDING ON is not supported`, `unknown data name DIBSTAT`)."""
    line = next((l for l in text.splitlines() if l.strip()), "").strip()
    line = re.sub(r"^(cobolfe|error|Error):\s*", "", line)
    line = re.sub(r"^\d+:\d+:\s*", "", line)
    line = _LOC_RE.sub("", line)
    line = re.sub(r"\s+in \[.*$", "", line)            # "... not found in ['dir', ...]"
    line = re.sub(r"\s*/\S+?(?=:\s|\s|$)", "", line)       # absolute paths (run directories, sources)
    line = re.sub(r"\(line \d+\)", "", line)
    line = re.sub(r"\s+", " ", line).strip()
    return line[:120] or "unknown error"


def _frontend(target: Target, vdir: Path) -> list[dict]:
    """Source mode: run the pinned coblean's front end on each COBOL source (cached by source, copybooks, pin).
    -> [{"src", "name", "ir": path or None, "error": class or None}]"""
    import subprocess
    root = Path(target.root)
    cdirs = [str(root / d) for d in target.extra.get("copybook_dirs", [])]
    cpy_digest = sha256(json.dumps(sorted(
        (str(f.relative_to(root)), sha256(f.read_text(errors="replace")))
        for d in cdirs for f in Path(d).glob("*") if f.is_file())))
    fe = COBLEAN / "tools" / "cobolfe" / "cobolfe.py"
    out_dir = vdir / "ir"
    out_dir.mkdir(parents=True, exist_ok=True)
    cache = vdir.parents[1] / "cache" / "cobolfe"
    cache.mkdir(parents=True, exist_ok=True)
    res = []
    for rel in target.sources:
        src = root / rel
        name = src.stem.upper()
        key = sha256(json.dumps([COBLEAN_PIN, rel, sha256(src.read_text(errors="replace")), cpy_digest,
                                 target.extra.get("cobolfe_flags", [])]))
        hit = cache / f"{key}.json"
        if hit.exists():
            d = json.loads(hit.read_text())
        else:
            irp = out_dir / f"{name}.ir.json"
            if irp.exists():
                irp.unlink()
            cmd = [str(RUN1), "-t", "300", "-m", "8", "-c", "0.1", "--", "python3", "-I", str(fe), str(src),
                   *[x for d in cdirs for x in ("-I", d)], *target.extra.get("cobolfe_flags", []),
                   "-o", str(irp), "--report"]
            p = subprocess.run(cmd, cwd=vdir, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                               timeout=420, env=dict(os.environ, VO_ROOT=str(VO_ROOT)))
            ok = p.returncode == 0 and irp.exists()
            d = {"rc": p.returncode, "stderr": p.stderr[-4000:], "ir": irp.read_text() if ok else None,
                 "error": None if ok else error_class(p.stderr or p.stdout or f"exit {p.returncode}")}
            tmp = hit.with_name(hit.name + f".{os.getpid()}.tmp")
            tmp.write_text(json.dumps(d))
            tmp.replace(hit)
        irp = out_dir / f"{name}.ir.json"
        if d["ir"] is not None:
            irp.write_text(d["ir"])
            name = json.loads(d["ir"]).get("name", name)
        res.append({"src": rel, "name": name, "ir": str(irp) if d["ir"] is not None else None,
                    "error": d["error"]})
    return res


def prog_ident(name: str) -> str:
    """Lean name of a program constant (`ACCT-INT` -> `Prog_ACCT_INT`)."""
    return "Prog_" + re.sub(r"\W", "_", name)


def _apply_options(cfg: dict, flags: list[str]) -> dict:
    cfg = dict(cfg)
    for f in flags:
        if "=" not in f:
            continue
        k, v = f.split("=", 1)
        if v.lower() in ("true", "false"):
            cfg[k] = v.lower() == "true"
        else:
            try:
                cfg[k] = int(v)
            except ValueError:
                cfg[k] = v
    return cfg


def _walk(x, out_calls: list[str], out_unsup: list[str]) -> None:
    if isinstance(x, dict):
        for k, v in x.items():
            if k == "call" and isinstance(v, dict) and "prog" in v:
                if v["prog"] not in out_calls:
                    out_calls.append(v["prog"])
            elif k == "unsupported" and isinstance(v, dict):
                what = v.get("what", "?")
                if what not in out_unsup:
                    out_unsup.append(what)
            _walk(v, out_calls, out_unsup)
    elif isinstance(x, list):
        for v in x:
            _walk(v, out_calls, out_unsup)


def build(target: Target, variant: Variant, run_dir: Path) -> Build:
    vdir = run_dir / target.version / variant.name
    vdir.mkdir(parents=True, exist_ok=True)
    pkg = lean_package(run_dir)
    gen_mod = f"Gen.{_ident(target.version)}_{_ident(variant.name)}.Unit"
    gen_path = pkg.src(gen_mod)
    gen_path.parent.mkdir(parents=True, exist_ok=True)
    root = Path(target.root)
    source_mode = target.extra.get("frontend") == "cobolfe"
    blocked: list[dict] = []           # programs the front end or the elaboration check rejected
    if source_mode:
        fe = _frontend(target, vdir)
        inputs = [(x["src"], Path(x["ir"])) for x in fe if x["ir"]]
        blocked = [{"name": x["name"], "src": x["src"], "scope": "gap:frontend:" + x["error"]} for x in fe
                   if not x["ir"]]
    else:
        inputs = [(s, root / s) for s in target.sources]
    progs = []
    for s, path in inputs:
        d = json.loads(path.read_text())
        d["config"] = _apply_options(d.get("config", {}), variant.flags)
        name = d["name"]
        jname = f"{prog_ident(name)}.ir.json"
        text = json.dumps(d, sort_keys=True)
        (gen_path.parent / jname).write_text(text)
        calls, unsup = [], []
        _walk(d.get("paras", []), calls, unsup)
        progs.append({"name": name, "json": jname, "src": s, "calls": calls, "unsupported": unsup,
                      "hash": sha256(text)[:16], "data": d.get("data", []), "files": d.get("files", []),
                      "isMain": d.get("isMain", False)})
    if target.extra.get("elab_check") and progs:
        pkg.ensure()
        good = []
        for p in progs:
            emod = f"Gen.{_ident(target.version)}_{_ident(variant.name)}.Elab_{_ident(p['name'])}"
            src = "\n".join(["/- Generated by veriforch: elaboration check of one program. -/", "import Cobol", "",
                             "namespace " + emod, "open Cobol", "",
                             f'cobol_program {prog_ident(p["name"])} from "{p["json"]}"', "", "end " + emod, ""])
            epath = pkg.src(emod)
            epath.parent.mkdir(parents=True, exist_ok=True)
            # the module reads the IR next to the Gen module: same directory
            if epath.parent != gen_path.parent:
                (epath.parent / p["json"]).write_text((gen_path.parent / p["json"]).read_text())
            # failures are cached too (pkg.check stores successes only), so later builds of the same tree do not
            # elaborate a rejected program again
            fkey = pkg.key(src + (gen_path.parent / p["json"]).read_text(), {})
            fpath = vdir.parents[1] / "cache" / "elab_fail" / f"{fkey}.json"
            if fpath.exists():
                blocked.append(dict(json.loads(fpath.read_text()), name=p["name"], src=p["src"]))
                continue
            r = pkg.check(emod, src, {}, timeout=int(target.extra.get("gen_timeout", 900)))
            if r.ok:
                good.append(p)
            else:
                b = {"name": p["name"], "src": p["src"],
                     "scope": "gap:elaboration:" + error_class((r.errors or [r.status])[0])}
                blocked.append(b)
                fpath.parent.mkdir(parents=True, exist_ok=True)
                fpath.write_text(json.dumps(b))
        progs = good
    lines = ["/- Generated by veriforch from surface-IR JSON. Do not edit. -/", "import Cobol", "",
             "namespace " + gen_mod, "open Cobol", ""]
    for p in progs:
        lines.append(f'cobol_program {prog_ident(p["name"])} from "{p["json"]}"')
    lines += ["", "end " + gen_mod, ""]
    new = "\n".join(lines)
    if not gen_path.exists() or gen_path.read_text() != new:
        gen_path.write_text(new)
    names = {p["name"] for p in progs}
    cobol_src = target.extra.get("cobol_sources", {})
    units = []
    for p in progs:
        scope = "in_scope" if not p["unsupported"] else "gap:unsupported:" + ",".join(p["unsupported"])[:200]
        src_text = ""
        for rel in cobol_src.get(p["name"], []):
            f = root / rel
            if f.exists():
                src_text += f"      *> ---- {rel}\n" + f.read_text(errors="replace") + "\n"
        u = Unit(name=p["name"], sym=prog_ident(p["name"]), lean_decl=f"{gen_mod}.{prog_ident(p['name'])}",
                 kind="api" if (not target.entry or p["name"] in target.entry) else "internal",
                 callees=[c for c in p["calls"] if c in names], scope=scope, loc=p["src"], body_hash=p["hash"],
                 source=src_text)
        u.signature = {"externals": [c for c in p["calls"] if c not in names], "files": p["files"],
                       "isMain": p["isMain"]}
        if source_mode and not u.source:
            u.source = (root / p["src"]).read_text(errors="replace")
        units.append(u)
    for b in blocked:
        units.append(Unit(name=b["name"], sym=prog_ident(b["name"]), lean_decl=f"{gen_mod}.{prog_ident(b['name'])}",
                          kind="api", callees=[], scope=b["scope"], loc=b["src"],
                          body_hash=sha256(b["src"] + b["scope"])[:16],
                          source=(root / b["src"]).read_text(errors="replace") if source_mode else ""))
    return Build(target=target, variant=variant, dir=vdir, pkg=pkg, units=units,
                 info={"gen_module": gen_mod, "gen_ns": gen_mod, "programs": progs,
                       "gen_dir": str(gen_path.parent), "blocked": blocked})


def data_table(data: list, depth: int = 0, out: list | None = None, counts: dict | None = None) -> list:
    """Indented listing of the data division: level, name, PIC, usage, OCCURS, REDEFINES."""
    out = [] if out is None else out
    for it in data:
        pic = it.get("pic")
        pics = json.dumps(pic, separators=(",", ":")) if pic else ""
        extra = []
        if it.get("usage") and it["usage"] != "display":
            extra.append(f"usage {it['usage']}")
        if it.get("occurs", 1) not in (1, None):
            extra.append(f"occurs {it['occurs']}")
        if it.get("redefines"):
            extra.append(f"redefines #{it['redefines']}")
        if it.get("value") is not None:
            extra.append("value " + json.dumps(it["value"], separators=(",", ":"))[:40])
        conds = [_first_str(c) for c in it.get("conds", [])]
        if conds:
            extra.append("88: " + ", ".join(conds))
        out.append(f"{'  ' * depth}{it.get('level', '')} {it.get('name', '')} (#{it.get('id')}) {pics} {'; '.join(extra)}".rstrip())
        data_table(it.get("children", []), depth + 1, out, counts)
    return out


def _first_str(x) -> str:
    """Name of a level-88 entry: `{"name": ...}` or `[id, [name, ranges]]` depending on the extractor."""
    if isinstance(x, str):
        return x
    if isinstance(x, dict):
        return str(x.get("name", ""))
    if isinstance(x, list):
        for y in x:
            n = _first_str(y)
            if n:
                return n
    return ""


def unique_names(data: list) -> set[str]:
    seen: dict[str, int] = {}

    def go(xs):
        for it in xs:
            n = it.get("name", "")
            seen[n] = seen.get(n, 0) + 1
            go(it.get("children", []))
    go(data)
    return {n for n, c in seen.items() if c == 1 and n not in ("", "FILLER")}
