"""Thrift T1, Rust: find the items on which Aeneas aborts the whole crate (writes the target's `aeneas_prune_file`).

Aeneas (deps/aeneas-fdebf20) translates a crate or nothing when it meets certain constructs: an uncaught exception
and no Lean file at all. On lib/rs: a dynamic trait type in the signature of a trait's method
(`TInputProtocolFactory::create(..) -> Box<dyn TInputProtocol + Send>`), core::str::pattern::Pattern (a generic
associated type), and every function that builds a value of a type Aeneas failed (thrift::Error has a variant
`User(Box<dyn Error + Sync + Send>)`). The Rust adapter keeps these out of the LLBC that Aeneas reads
(orch/veriforch/adapters/rust/build.py `prune_llbc`, target option `aeneas_prune_file`); this driver finds them:
Charon once (inside bubblewrap, with the target's options, as the adapter runs it), then repeatedly
    prune the LLBC with the current file -> Aeneas
and, while Aeneas aborts, it attributes the abort to the item whose span the last error before the exception names
and appends it to `pruned` (a trait declaration, an impl or a function; Charon's `--exclude` cannot do this: it drops
a trait with its name and Aeneas then aborts on the impls; excluding a method leaves its signature in the trait).
The file's `opaque` list and `dyn_fields` are written by hand (see notes/thrift/T1_rsts.md).

    tools/thrift_rsts/triage_rs.py TARGET.toml [MAX_ITERATIONS]
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

VO_ROOT = Path("/home/user/veriforch")
sys.path.insert(0, str(VO_ROOT / "orch"))
from veriforch.adapters.rust import build as rb  # noqa: E402
from veriforch.config import load_target  # noqa: E402
from veriforch.model import sha256  # noqa: E402

_SRC = re.compile(r"Source: '(?P<f>[^']+)', lines (?P<l0>\d+):(?P<c0>\d+)-(?P<l1>\d+):(?P<c1>\d+)")
_ERR = re.compile(r"^\[Error\]\s*(?P<msg>.*)$")


def abort_site(out: str) -> dict | None:
    """The last `[Error] ... Source: ...` before Aeneas's uncaught exception (None when Aeneas did not abort)."""
    i = out.find("Uncaught exception")
    if i < 0:
        return None
    lines = out[:i].splitlines()
    for k in range(len(lines) - 1, -1, -1):
        m = _ERR.match(lines[k].strip())
        if not m:
            continue
        for l in lines[k + 1:k + 4]:
            s = _SRC.search(l)
            if s:
                return {"message": m.group("msg").strip(), "file": s.group("f"), "l0": int(s.group("l0")),
                        "c0": int(s.group("c0")), "l1": int(s.group("l1")), "c1": int(s.group("c1"))}
        return {"message": m.group("msg").strip(), "file": "", "l0": 0, "c0": 0, "l1": 0, "c1": 0}
    return {"message": "(no error line before the exception)", "file": "", "l0": 0, "c0": 0, "l1": 0, "c1": 0}


def attribute(t: dict, site: dict) -> dict | None:
    """The item whose span is the error's span (trait declaration, then impl, then function), else the smallest
    function or impl enclosing it (an impl's method alone: if Aeneas then aborts on the impl, the impl's span names
    it and the next iteration prunes the impl)."""
    its = rb.llbc_items(t)
    key = (site["file"], site["l0"], site["c0"], site["l1"], site["c1"])
    rank = {"trait_decl": 0, "trait_impl": 1, "fun_decl": 2}
    exact = sorted((x for x in its if (x["file"], x["l0"], x["c0"], x["l1"], x["c1"]) == key),
                   key=lambda x: rank[x["kind"]])
    if exact:
        return exact[0]
    enc = [x for x in its if x["file"] == site["file"] and (x["l0"], x["c0"]) <= (site["l0"], site["c0"])
           and (x["l1"], x["c1"]) >= (site["l1"], site["c1"]) and x["kind"] != "trait_decl"]
    return min(enc, key=lambda x: (x["l1"] - x["l0"], rank[x["kind"]])) if enc else None


def reason(x: dict, site: dict) -> str:
    """The `<reason>` of `gap:aeneas-abort:<reason>` (no commas: blocker_freq splits tokens at commas)."""
    if x["kind"] == "trait_decl" and site["message"].startswith("Dynamic trait types"):
        return f"dyn-trait-signature:{x['path']}"
    if x["kind"] == "trait_decl":
        return f"library-trait:{x['path']}"
    return "uncaught-aeneas-exception"


def main(argv: list[str]) -> int:
    t = load_target(argv[0])
    max_it = int(argv[1]) if len(argv) > 1 else 40
    work = VO_ROOT / "scratch" / "thrift_rsts" / "rs" / f"triage_{t.name}"
    out_file = rb._opt_path(t, "aeneas_prune_file")
    files, crate, _ = rb._cargo_manifest(t)
    promoted = {k: (rb.promote_tests(v.decode("utf-8", "replace"))[0].encode() if k.endswith(".rs") else v)
                for k, v in files.items()}
    cdir = work / "crate"
    rb._write_tree(cdir, promoted)
    llbc = cdir / f"{crate}.llbc"
    stamp = cdir / "charon_options.json"
    opts = json.dumps(rb._charon_options(t))
    if not llbc.exists() or not stamp.exists() or stamp.read_text() != opts:
        if llbc.exists():
            llbc.unlink()
        got, out = rb._charon(work, cdir, crate, t)
        if got is None:
            print(f"Charon failed: {out[-1500:]}", flush=True)
            return 1
        stamp.write_text(opts)
    raw = llbc.read_text()
    log = work / "triage.jsonl"
    for it in range(1, max_it + 1):
        spec = json.loads(out_file.read_text())
        d = json.loads(raw)
        removed = rb.prune_llbc(d, json.loads(json.dumps(spec)))
        pl = cdir / f"{crate}.pruned.llbc"
        pl.write_text(json.dumps(d))
        gen = work / "gen"
        acmd = [rb.AENEAS / "bin" / "aeneas", "-backend", "lean", "-split-files", "-no-progress-bar",
                "-all-computable", "-max-recdepth", "100000", "-subdir", f"It{it}", "-dest", gen, pl]
        q = rb._job(acmd, work, mem_gib=48, timeout=2400, core_h=6.0, env={"TMPDIR": work / "tmp", "NO_COLOR": "1"},
                    log=work / "logs" / f"aeneas_{it}.txt")
        site = abort_site(rb._text(q.stdout))
        done = (gen / f"It{it}" / "Funs.lean").exists() or (gen / f"It{it}" / "Types.lean").exists()
        rec = {"iteration": it, "aeneas_exit": q.returncode, "lean_files": done, "site": site,
               "pruned_items": len(spec.get("pruned", [])), "removed_functions": len(removed)}
        if site is None and done:
            rec["result"] = "aeneas completed"
            with open(log, "a") as f:
                f.write(json.dumps(rec) + "\n")
            print(f"[{it}] Aeneas completed: {len(spec.get('pruned', []))} pruned items, {len(removed)} functions "
                  f"removed", flush=True)
            return 0
        x = attribute(d["translated"], site) if site else None
        if x is None or any((e["kind"], e["path"], e["line"]) == (x["kind"], x["path"], x["l0"])
                            for e in spec.get("pruned", [])):
            rec["result"] = "abort not attributed" if x is None else f"abort again on pruned {x['path']}"
            with open(log, "a") as f:
                f.write(json.dumps(rec) + "\n")
            print(f"[{it}] {rec['result']}: {site}", flush=True)
            return 1
        spec.setdefault("pruned", []).append({"kind": x["kind"], "path": x["path"], "file": x["file"], "line": x["l0"],
                                              "end": x["l1"], "reason": reason(x, site), "message": site["message"],
                                              "iteration": it})
        spec["llbc_sha256"] = sha256(raw)
        out_file.write_text(json.dumps(spec, indent=1))
        rec["result"] = f"prune {x['kind']} {x['path']}"
        with open(log, "a") as f:
            f.write(json.dumps(rec) + "\n")
        print(f"[{it}] abort ({site['message'][:80]}) at {site['file']}:{site['l0']} -> prune {x['kind']} "
              f"{x['path']} ({x['file']}:{x['l0']})", flush=True)
    print(f"no completion after {max_it} iterations", flush=True)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
