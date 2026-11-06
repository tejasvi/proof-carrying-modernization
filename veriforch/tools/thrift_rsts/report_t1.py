"""Thrift T1 report, Rust + TypeScript, in the form of notes/thrift/T1_SPEC_FOR_WORKERS.md (PREREG_T_v1 "T1"):

* notes/thrift/T1_rsts_units.tsv   language, unit, path, in_scope, gaps: every unit of the frame (T2's input);
* notes/thrift/T1_rsts_blockers.tsv  families and tokens by the number of frame units whose closure carries them
                                     (blocker_freq.py's format and token rules);
* notes/thrift/T1_rsts.json        every unit (frame or not) with name, file, line, component, kind, scope, closure
                                   gaps; summaries; the TypeScript scan of the test code (outside the frame);
* the tables of notes/thrift/T1_rsts.md (printed, markdown).

Frozen rules used as they are: language / component / lib_source from ~/fv_paper/prereg/T/tools/thrift_paths.py
(imported read-only); `tokens` and `family` below are copied from ~/fv_paper/prereg/tools/blocker_freq.py (it runs its
main() on import, and the Rust adapter's units are not one of its KINDs, so the spec says to apply its token rules).
In scope = D's definition: the unit is emitted and no member of its call-graph closure has a gap.

Rust units: the functions with a body of the thrift crate as the Rust adapter enumerates them, i.e. the adapter's
units (runs/thrift_rs/v0/default/units.json, from the pruned LLBC), plus the functions the pruning removed before
Aeneas and the functions Charon kept opaque (both: scope `gap:aeneas-abort:<item>`; tools/thrift_rsts/triage_rs.py).
The call graph is Charon's (direct calls in the unpruned LLBC) together with the adapter's callees. A test's own
`gap:reaches:` scope is read as in scope here: its closure already carries the reached unit's gap.

    tools/thrift_rsts/report_t1.py [--include-tests] > tables.md
"""
from __future__ import annotations

import collections
import json
import math
import re
import sys
from pathlib import Path

VO = Path("/home/user/veriforch")
sys.path.insert(0, str(VO / "orch"))
sys.path.insert(0, "/home/user/fv_paper/prereg/T/tools")
sys.dont_write_bytecode = True
import thrift_paths  # noqa: E402  (frozen, read only)
from veriforch.adapters.rust import build as rb  # noqa: E402

THRIFT = VO / "targets" / "thrift"
NOTES = VO / "notes" / "thrift"
RS_RUN = VO / "runs" / "thrift_rs" / "v0" / "default"
PRUNE = VO / "targets" / "thrift_rs.aeneas_prune.json"
TS_SCRATCH = VO / "scratch" / "thrift_rsts" / "ts"
LIBRARY_FUNCTIONS = VO / "scratch" / "thrift_rsts" / "rs" / "library_functions.json"   # tools/thrift_rsts/cfgtest_rs.py
TS_PROJECTS = {"thrift_ts": "lib/ts", "thrift_ts_nodets": "lib/nodets/test"}


# -- blocker_freq.py's token rules (copied verbatim) --------------------------------------------------------------------

def tokens(scope):
    if not scope or scope == "in_scope":
        return []
    parts = scope.split(":", 2)
    if len(parts) == 2 or (len(parts) == 3 and not parts[2]):
        return [parts[1]]
    return [f"{parts[1]}:{x}" for x in parts[2].split(",") if x]


def family(tok):
    if tok.startswith("unmodelled:"):
        body = tok.split(":", 1)[1].split("/")[0]
        return "unmodelled:" + body.rsplit(".", 1)[0]
    return tok


def clean(tok: str) -> str:
    """A token as one TSV field item: the Rust adapter's free-text gap messages (Aeneas's, Lean's) contain spaces and
    newlines, which the space-separated gaps column cannot hold: whitespace runs become `_` (the only change)."""
    return re.sub(r"\s+", "_", tok.strip())


def token_class(tok: str) -> str:
    """A coarser grouping of the Rust tokens for the .md tables (not part of the TSV): the gap class and the kind of
    message (Lean's messages name generated identifiers and positions)."""
    cls, _, msg = tok.partition(":")
    m = msg.replace("_", " ")
    if cls == "lean":
        for pat, name in (("imports a module that does not check", "imports a module that does not check"),
                          ("Unknown constant", "unknown constant (a definition that failed elsewhere)"),
                          ("not supported by code generator", "code generator: calls a noncomputable definition"),
                          ("fail to show termination", "termination (instance definitions)"),
                          ("could not resolve recursive fields", "trait default bodies not exposed"),
                          ("Failed to infer universe", "universe levels"),
                          ("Application type mismatch", "type mismatch"), ("type mismatch", "type mismatch")):
            if pat in m:
                return f"lean: {name}"
        return "lean: other (" + m[:60] + ")"
    if cls == "aeneas":
        return "aeneas: " + m[:80]
    return tok


# -- Rust ----------------------------------------------------------------------------------------------------------------

def rust_units() -> tuple[list[dict], dict]:
    """The adapter's units (runs/thrift_rs/v0/default/units.json): every function with a body of the crate, the
    pruned and opaque ones included (scope gap:aeneas-abort:<reason>), callees from the unpruned LLBC. A unit is
    cfg(test) code (kind test: a test or a helper of a test module) when Charon on the unpromoted crate
    (tools/thrift_rsts/cfgtest_rs.py) does not have it."""
    b = json.loads((RS_RUN / "rust_build.json").read_text())
    adapter = json.loads((RS_RUN / "units.json").read_text())
    lib = json.loads(LIBRARY_FUNCTIONS.read_text())["library_functions"]
    libkeys = {(f["path"], f["file"], f["line"]) for f in lib}
    units = []
    for a in adapter:
        path, line = a["loc"].rsplit(":", 1)
        rel = str(Path(path).relative_to(THRIFT / "lib" / "rs"))
        rust_path = (a.get("signature") or {}).get("rust")
        is_lib = (rust_path, rel, int(line)) in libkeys
        units.append({"lang": "Rust", "name": a["name"], "rust_path": rust_path, "file": f"lib/rs/{rel}",
                      "line": int(line), "kind": "function" if is_lib else "test",
                      "test_attr": a["kind"] == "test", "scope": a["scope"], "callees": a["callees"]})
    names = [u["name"] for u in units]
    if len(set(names)) != len(names):
        raise RuntimeError("adapter unit names are not unique: " +
                           str([n for n, c in collections.Counter(names).items() if c > 1][:5]))
    missing = libkeys - {(u["rust_path"], u["file"][len("lib/rs/"):], u["line"]) for u in units}
    # a library function the adapter does not enumerate (the closure of a function Charon keeps opaque): in the frame
    # with blocker_freq's token for a population unit without a front-end unit
    for path, file, line in sorted(missing):
        units.append({"lang": "Rust", "name": f"{path.split('::', 1)[-1].replace('::', '.')}@{file}:{line}",
                      "rust_path": path, "file": f"lib/rs/{file}", "line": line, "kind": "function",
                      "test_attr": False, "scope": "gap:not-emitted", "callees": []})
    llbc = json.loads((Path(b["frontend"]) / "crate" / "thrift.llbc").read_text())["translated"]
    trait_paths = {rb._name(x["item_meta"]["name"]) for x in llbc["trait_decls"] if x and x["item_meta"].get("is_local")}
    return units, {"build": b, "spec": json.loads(PRUNE.read_text()) if PRUNE.exists() else {},
                   "library_functions_not_units": sorted(missing), "trait_paths": trait_paths}


def tsv_kind(u: dict, trait_paths: set[str]) -> str:
    """test: #[cfg(test)] code; method: a function of an impl block (its Rust path has an `{impl}` component, also
    Charon's FnOnce shims) or a provided method of a trait; else fn."""
    if u["kind"] == "test":
        return "test"
    p = u.get("rust_path") or ""
    return "method" if "{impl}" in p or p.rsplit("::", 1)[0] in trait_paths else "fn"


def closure_tokens(units: list[dict]) -> None:
    """D's definition over the call graph: the gap tokens of every closure member (`gap:reaches:` read as in scope)."""
    by = {u["name"]: u for u in units}

    def own(u):
        return [] if u["scope"].startswith("gap:reaches:") else tokens(u["scope"])
    for u in units:
        seen, todo, toks = set(), [u["name"]], set()
        while todo:
            n = todo.pop()
            if n in seen or n not in by:
                continue
            seen.add(n)
            toks |= set(own(by[n]))
            todo += by[n]["callees"]
        u["gaps"] = sorted({clean(t) for t in toks})
        u["in_scope"] = 0 if toks else 1
        u["closure_size"] = len(seen)


# -- TypeScript (outside the frame: every .ts file is under a test directory; thrift.d.ts is not TS) -----------------------

_TS_ERR = re.compile(r"^(?P<file>[^()]+)\((?P<line>\d+),(?P<col>\d+)\): error (?P<code>TS\d+): (?P<msg>.*)$")


def ts_units() -> tuple[list[dict], dict]:
    errs: dict[str, list[dict]] = collections.defaultdict(list)
    for rel in TS_PROJECTS.values():
        for line in (TS_SCRATCH / f"tsc_{rel.replace('/', '_')}.txt").read_text().splitlines():
            m = _TS_ERR.match(line.strip())
            if m:
                mod = re.search(r"Cannot find (?:module|name) '([^']+)'", m.group("msg"))
                errs[f"{rel}/{m.group('file')}"].append({"line": int(m.group("line")), "code": m.group("code"),
                                                        "missing": mod.group(1) if mod else None,
                                                        "msg": m.group("msg")})
    out, cov = [], {}
    for proj, rel in TS_PROJECTS.items():
        d = VO / "runs" / proj / "v0" / "src"
        cov[proj] = json.loads(next(d.glob("*.coverage.json")).read_text())["summary"]
        for u in json.loads((d / "units.json").read_text()):
            row = u["signature"]["row"]
            file = f"{rel}/{row['file']}"
            out.append({"lang": thrift_paths.language(file), "name": u["name"], "file": file, "line": row["line"],
                        "kind": row["kind"], "scope": u["scope"], "callees": u["callees"],
                        "missing_modules": sorted({e["missing"] for e in errs.get(file, []) if e["missing"]})})
    decls = json.loads((TS_SCRATCH / "decls.json").read_text())
    rows = {(u["file"], u["line"]) for u in out}
    info = {"coverage_summary": cov, "tsc_errors": dict(errs),
            "thrift_d_ts_declarations_without_body": dict(collections.Counter(
                x["container"] or "(module function)" for x in decls if x["file"] == "lib/ts/thrift.d.ts" and not x["hasBody"])),
            "functions_with_body_not_coverage_rows": len([x for x in decls if x["hasBody"] and (x["file"], x["line"]) not in rows])}
    return out, info


# -- tables --------------------------------------------------------------------------------------------------------------

def wilson(k: int, n: int, z: float = 1.959964) -> str:
    if n == 0:
        return "-"
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return f"[{100 * max(0, c - h):.1f}, {100 * min(1, c + h):.1f}]"


def rate_table(units: list[dict], comps: list[str]) -> list[str]:
    out = ["| component | units | emitted, own scope in_scope | in scope (closure, D) | rate | Wilson 95% |",
           "|---|---:|---:|---:|---:|---|"]
    for c in comps + ["TOTAL"]:
        cu = [u for u in units if c == "TOTAL" or u["component"] == c]
        own = sum(u["scope"] == "in_scope" for u in cu)
        k = sum(u["in_scope"] for u in cu)
        out.append(f"| {c} | {len(cu)} | {own} | {k} | {100 * k / len(cu):.1f}% | {wilson(k, len(cu))} |" if cu
                   else f"| {c} | 0 | 0 | 0 | - | - |")
    return out


def reason(scope: str) -> str:
    """A readable gap class of a unit's own scope (for the gap table; the TSV keeps the raw tokens)."""
    if scope == "in_scope":
        return "in_scope"
    if scope.startswith("gap:aeneas-abort:"):
        if "str-pattern-gat" in scope:
            return "aeneas-abort: body reaches core::str::pattern::Pattern (Charon keeps it opaque)"
        if "dyn-trait-signature" in scope:
            return "aeneas-abort: implements a trait method with a dyn type in its signature (pruned)"
        return "aeneas-abort: " + scope.split(":", 2)[2]
    if scope == "gap:not-emitted":
        return "not emitted (the body of a closure inside an opaque function)"
    if scope.startswith("gap:aeneas:"):
        m = scope[len("gap:aeneas:"):]
        return "aeneas: " + (m if len(m) < 70 else m[:67] + "...")
    if scope.startswith("gap:external:"):
        return "external: calls an unmodelled library item"
    if scope.startswith("gap:lean:"):
        m = scope[len("gap:lean:"):]
        return "lean: " + ("imports a module that does not check" if m.startswith("imports a module") else
                           "the generated module does not check")
    if scope.startswith("gap:reaches:"):
        return "test reaches a gap unit"
    return ":".join(scope.split(":", 2)[:2])


def gap_table(units: list[dict], comps: list[str]) -> list[str]:
    us = [u for u in units if u["scope"] != "in_scope"]
    cnt = collections.Counter(reason(u["scope"]) for u in us)
    out = ["| own gap (unit's scope) | units | " + " | ".join(comps) + " |", "|---|---:|" + "---:|" * len(comps)]
    for r, n in cnt.most_common():
        out.append(f"| {r} | {n} | " + " | ".join(str(sum(1 for u in us if reason(u["scope"]) == r and u["component"] == c))
                                                for c in comps) + " |")
    return out


def blockers(units: list[dict]) -> tuple[collections.Counter, collections.Counter, collections.Counter]:
    tok, fam, alone = collections.Counter(), collections.Counter(), collections.Counter()
    for u in units:
        for t in u["gaps"]:
            tok[t] += 1
        fs = {family(t) for t in u["gaps"]}
        for f in fs:
            fam[f] += 1
        if len(fs) == 1:
            alone[next(iter(fs))] += 1
    return tok, fam, alone


def blocker_table(units: list[dict], top: int = 15) -> list[str]:
    _, fam, alone = blockers(units)
    out = ["| blocker family (closure token) | units whose closure carries it | units unlocked if it alone were fixed |",
           "|---|---:|---:|"]
    for f, n in sorted(fam.items(), key=lambda kv: (-kv[1], kv[0]))[:top]:
        out.append(f"| `{f[:110]}` | {n} | {alone[f]} |")
    return out


def class_table(units: list[dict], top: int = 20) -> list[str]:
    """Blocker classes (token_class) by the number of units whose closure carries one."""
    cnt = collections.Counter()
    alone = collections.Counter()
    for u in units:
        cs = {token_class(t) for t in u["gaps"]}
        for c in cs:
            cnt[c] += 1
        if len(cs) == 1:
            alone[next(iter(cs))] += 1
    out = ["| blocker class (grouped tokens) | units whose closure carries it | units unlocked if it alone were fixed |",
           "|---|---:|---:|"]
    for c, n in sorted(cnt.items(), key=lambda kv: (-kv[1], kv[0]))[:top]:
        out.append(f"| {c} | {n} | {alone[c]} |")
    return out


def file_table(units: list[dict]) -> list[str]:
    out = ["| file | units | own scope in_scope | in scope (closure) | most frequent own gap |", "|---|---:|---:|---:|---|"]
    for f in sorted({u["file"] for u in units}):
        fu = [u for u in units if u["file"] == f]
        top = collections.Counter(reason(u["scope"]) for u in fu if u["scope"] != "in_scope").most_common(1)
        out.append(f"| {f} | {len(fu)} | {sum(u['scope'] == 'in_scope' for u in fu)} | {sum(u['in_scope'] for u in fu)} | "
                   f"{top[0][0] + f' ({top[0][1]})' if top else '-'} |")
    return out


def main(argv: list[str]) -> int:
    include_tests = "--include-tests" in argv
    rs, rinfo = rust_units()
    closure_tokens(rs)
    for u in rs:
        u["component"] = thrift_paths.component(u["file"])
        u["language"] = thrift_paths.language(u["file"])
        u["in_frame"] = bool(thrift_paths.lib_source(u["file"]) and (include_tests or u["kind"] != "test"))
    ts, tinfo = ts_units()
    for u in ts:
        u["component"] = thrift_paths.component(u["file"])
        u["language"] = thrift_paths.language(u["file"])
        u["in_frame"] = bool(thrift_paths.lib_source(u["file"]))
        u["gaps"] = tokens(u["scope"])
        u["in_scope"] = 0 if u["gaps"] else 1
    frame = sorted([u for u in rs + ts if u["in_frame"]], key=lambda u: (u["language"], u["file"], u["line"], u["name"]))
    keys = [u["name"] for u in frame]
    if len(set(keys)) != len(keys):
        raise RuntimeError("unit keys are not unique")
    NOTES.mkdir(parents=True, exist_ok=True)
    # the TSV: the frame (kind fn / method) and the #[cfg(test)] code (kind test, outside the frame: the evidence-owner session's draw script
    # leaves those rows out itself)
    tests = sorted([u for u in rs if u["kind"] == "test" and not u["in_frame"]],
                   key=lambda u: (u["language"], u["file"], u["line"], u["name"]))
    rows = sorted(frame + tests, key=lambda u: (u["language"], u["file"], u["line"], u["name"]))
    if len({u["name"] for u in rows}) != len(rows):
        raise RuntimeError("unit keys are not unique")
    with open(NOTES / "T1_rsts_units.tsv", "w") as fh:
        fh.write("language\tunit\tpath\tin_scope\tgaps\tkind\n")
        for u in rows:
            fh.write(f"{u['language']}\t{u['name']}\t{u['file']}\t{u['in_scope']}\t{' '.join(u['gaps'])}\t"
                     f"{tsv_kind(u, rinfo['trait_paths'])}\n")
    tok, fam, _ = blockers(frame)
    blocked = sum(1 for u in frame if u["gaps"])
    with open(NOTES / "T1_rsts_blockers.tsv", "w") as fh:
        fh.write(f"# population {len(frame)} units; {blocked} with at least one gap token in the closure\n")
        fh.write("level\tname\tunits\n")
        for f, c in sorted(fam.items(), key=lambda kv: (-kv[1], kv[0])):
            fh.write(f"family\t{f}\t{c}\n")
        for t, c in sorted(tok.items(), key=lambda kv: (-kv[1], kv[0])):
            fh.write(f"token\t{t}\t{c}\n")
    comps = ["protocol", "transport", "server", "other"]
    rs_frame = [u for u in rs if u["in_frame"]]
    rs_tests = [u for u in rs if u["kind"] == "test"]
    helpers = [u for u in rs_tests if not u["test_attr"]]
    summary = {"rust_frame": {c: {"units": len(cu), "own_in_scope": sum(u["scope"] == "in_scope" for u in cu),
                                  "in_scope": sum(u["in_scope"] for u in cu)}
                              for c in comps + ["TOTAL"] for cu in [[u for u in rs_frame if c == "TOTAL" or u["component"] == c]]},
               "rust_cfg_test_functions": {"total": len(rs_tests), "test_fns": len(rs_tests) - len(helpers),
                                           "helpers": len(helpers)},
               "rust_tests_outside_frame": {"units": len(rs_tests) if not include_tests else 0,
                                            "in_scope": sum(u["in_scope"] for u in rs_tests) if not include_tests else 0},
               "ts_frame_units": sum(1 for u in ts if u["in_frame"]),
               "ts_scan_outside_frame": {"units": len(ts), "in_scope": sum(u["in_scope"] for u in ts)}}
    doc = {"target": "Apache Thrift f0eb8b84eb5654a949dda7c8ae444a11ca63e632 (targets/thrift_PIN.txt)",
           "step": "T1 coverage scan (PREREG_T_v1), no model calls", "include_tests_in_frame": include_tests,
           "fields": {"name": "unit key (TSV column unit)", "file": "repository path", "component": "thrift_paths",
                      "scope": "the unit's own scope (adapter scope string; aeneas-abort = pruned/opaque, see .md)",
                      "gaps": "blocker_freq tokens of the call-graph closure", "in_scope": "D's definition (closure)",
                      "in_frame": "lib_source(file) and, unless include_tests, not a test"},
           "summary": summary, "units": sorted(rs + ts, key=lambda u: (u["language"] or "", u["file"], u["line"], u["name"])),
           "rust_pruning": rinfo["spec"], "rust_library_functions_not_units": rinfo["library_functions_not_units"],
           "tsv": "language unit path in_scope gaps kind: the frame (kind fn/method) + #[cfg(test)] functions (kind test)",
           "rust_build": {k: rinfo["build"].get(k) for k in ("charon_version", "test_build", "rust_tests", "node_modules",
                                                             "failed_modules", "callgraph_mismatch")},
           "ts_info": tinfo}
    (NOTES / "T1_rsts.json").write_text(json.dumps(doc, indent=1) + "\n")
    print(f"frame: {len(frame)} units ({sum(1 for u in frame if u['language'] == 'Rust')} Rust, "
          f"{sum(1 for u in frame if u['language'] == 'TS')} TS); in scope {sum(u['in_scope'] for u in frame)}\n")
    print("### Rust frame (library functions of lib/rs/src" + (", tests included" if include_tests else ", #[test] excluded") + ")\n")
    print("\n".join(rate_table(rs_frame, comps)) + "\n")
    print("\n".join(gap_table(rs_frame, comps)) + "\n")
    print("\n".join(blocker_table(rs_frame)) + "\n")
    print("\n".join(class_table(rs_frame)) + "\n")
    print("\n".join(file_table(rs_frame)) + "\n")
    if not include_tests:
        print("### Rust in-file #[test] functions (outside the frame)\n")
        print("\n".join(rate_table(rs_tests, comps)) + "\n")
        print("\n".join(gap_table(rs_tests, comps)) + "\n")
    print("### TypeScript scan of the test code (outside the frame)\n")
    print("\n".join(file_table(ts)) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
