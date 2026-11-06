"""A candidate Rust crate for tiny-regex-c, run natively and as its Charon + Aeneas extraction in Lean.

    run_batch(crate_src_dir, jobs) -> results

`crate_src_dir` holds the translation's src/lib.rs (the only file used: the runner writes Cargo.toml, crate name
`tiny_regex`, no dependencies, debug profile with overflow checks, as in Aeneas's semantics). A job is
{"kind": "m", "pattern": hex, "text": hex} (re_match) or {"kind": "c", "pattern": hex} (re_compile). Every job
runs twice:
* native: one generated driver process calls the crate on every job (a panic is caught per job; a watchdog ends a
  job that runs too long, and the driver restarts after it);
* Lean: Charon and Aeneas extract the crate, Lean compiles the extraction, and one generated module `#eval`s the
  extracted function on every job (each on its own thread, with a time limit).

Results: a version that does not build gives ONE element {"status": "compile_error" | "runner_error", "stage",
"message"} (stages: cargo, driver = the crate lacks the agreed interface, charon, aeneas, interface, lean); when only
the extraction fails (charon, aeneas, interface, lean), the element also holds the native results ("native": [R]).
Otherwise
one dict per job: {"native": R, "aeneas": R} with R one of {"m": [ret, len]}, {"c": null | {"objs": [[kind, ch,
ccl] x 30], "ccl_buf": [40 bytes]}}, {"panic": msg}, {"timeout": true}, {"fail": msg} (Aeneas), {"div": true},
{"crash": msg}, {"runner_error": msg}.

Helpers (jobs, cargo, Lean paths) come from veriforch.modernize.rustrun; every cargo, Charon, Aeneas, Lean and
driver job goes through scripts/run1.sh. Work directories: scratch/c2rust/work/<key> (key: the source and
RUNNER_VERSION), results cached per job list.
"""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path

from ..modernize.rustrun import (AENEAS_BIN, VO_ROOT, _LEAN_PRELUDE, _PROFILE, _cargo_env, _cargo_errors, _job,
                                 _lean, _locked, _messages, _once, _rust_source_of, _save_log, _text, CARGO)

RUNNER_VERSION = "c2rust-run-1"
WORK = VO_ROOT / "scratch" / "c2rust" / "work"
CRATE = "tiny_regex"
MOD = "VoC2R"
CASE_SECONDS = 10
LEAN_CASE_SECONDS = 60

INTERFACE = """pub const MAX_REGEXP_OBJECTS: usize = 30;
pub const MAX_CHAR_CLASS_LEN: usize = 40;
#[derive(Clone, Copy)] pub struct RegexObj { pub kind: u8, pub ch: u8, pub ccl: usize }
#[derive(Clone, Copy)] pub struct Regex { pub objs: [RegexObj; 30], pub ccl_buf: [u8; 40] }
pub fn re_compile(pattern: &[u8]) -> Option<Regex>
pub fn re_matchp(pattern: Option<&Regex>, text: &[u8]) -> (i32, i32)
pub fn re_match(pattern: &[u8], text: &[u8]) -> (i32, i32)"""


def workdir(src_dir: Path) -> Path:
    lib = Path(src_dir) / "src" / "lib.rs"
    h = hashlib.sha256(RUNNER_VERSION.encode() + b"\0" + (lib.read_bytes() if lib.is_file() else b""))
    w = WORK / h.hexdigest()[:16]
    (w / "tmp").mkdir(parents=True, exist_ok=True)
    return w


def _prepare(src_dir: Path, w: Path) -> dict | None:
    lib = Path(src_dir) / "src" / "lib.rs"
    if not lib.is_file() or lib.is_symlink():
        return {"stage": "setup", "message": "the crate has no src/lib.rs"}
    d = w / "crate"
    if not (d / "Cargo.toml").exists():
        (d / "src").mkdir(parents=True, exist_ok=True)
        (d / "src" / "lib.rs").write_bytes(lib.read_bytes())
        (d / "Cargo.toml").write_text(
            f'[package]\nname = "{CRATE}"\nversion = "0.1.0"\nedition = "2021"\nbuild = false\nautobins = false\n'
            'autoexamples = false\nautotests = false\nautobenches = false\n\n[lib]\npath = "src/lib.rs"\n\n'
            "[dependencies]\n\n" + _PROFILE + "\n[workspace]\n")
    return None


def _cargo_build(w: Path, crate_dir: Path, log: str) -> subprocess.CompletedProcess:
    p = _job([CARGO, "build", "-j", "1", "--offline"], crate_dir, mem_gib=64, timeout=900, env=_cargo_env(w))
    _save_log(w, log, p)
    return p


_DRIVER = r'''#![allow(unused)]
use std::io::Write;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

static CURRENT: AtomicUsize = AtomicUsize::new(usize::MAX);
static STARTED: AtomicU64 = AtomicU64::new(0);

fn now_ms() -> u64 {
    match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => d.as_millis() as u64,
        Err(_) => 0,
    }
}

fn emit(line: &str) {
    let out = std::io::stdout();
    let mut lock = out.lock();
    let _ = lock.write_all(b"\n");
    let _ = lock.write_all(line.as_bytes());
    let _ = lock.write_all(b"\n");
    let _ = lock.flush();
}

fn unhex(s: &str) -> Vec<u8> {
    if s == "-" {
        return Vec::new();
    }
    let b = s.as_bytes();
    (0..b.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).expect("vo-driver: hex")).collect()
}

fn jstr(b: &[u8]) -> String {
    let mut o = String::from("\"");
    for &c in b {
        match c {
            b'"' => o.push_str("\\\""),
            b'\\' => o.push_str("\\\\"),
            0x20..=0x7e => o.push(c as char),
            _ => o.push_str(&format!("\\u{:04x}", c)),
        }
    }
    o.push('"');
    o
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let data = std::fs::read_to_string(&args[1]).expect("vo-driver: job file");
    let first: usize = args[2].parse().expect("vo-driver: first job");
    let limit_ms: u64 = args[3].parse().expect("vo-driver: time limit");
    let mut jobs: Vec<(u8, Vec<u8>, Vec<u8>)> = Vec::new();
    for line in data.lines() {
        let f: Vec<&str> = line.split_ascii_whitespace().collect();
        if f.len() >= 2 {
            jobs.push((f[0].as_bytes()[0], unhex(f[1]), if f.len() > 2 { unhex(f[2]) } else { Vec::new() }));
        }
    }
    std::panic::set_hook(Box::new(|info| {
        let p = info.payload();
        let msg = if let Some(s) = p.downcast_ref::<&str>() {
            s.to_string()
        } else if let Some(s) = p.downcast_ref::<String>() {
            s.clone()
        } else {
            String::from("panic")
        };
        let at = match info.location() {
            Some(l) => format!(" (line {})", l.line()),
            None => String::new(),
        };
        emit(&format!("VOPANIC {} {}", CURRENT.load(Ordering::SeqCst), jstr(format!("{}{}", msg, at).as_bytes())));
    }));
    std::thread::spawn(move || loop {
        std::thread::sleep(std::time::Duration::from_millis(20));
        let k = CURRENT.load(Ordering::SeqCst);
        if k != usize::MAX && now_ms().saturating_sub(STARTED.load(Ordering::SeqCst)) > limit_ms {
            emit(&format!("VOTIMEOUT {}", k));
            std::process::exit(3);
        }
    });
    let worker = std::thread::Builder::new().stack_size(1 << 28).spawn(move || {
        for k in first..jobs.len() {
            STARTED.store(now_ms(), Ordering::SeqCst);
            CURRENT.store(k, Ordering::SeqCst);
            emit(&format!("VOSTART {}", k));
            let (kind, p, t) = &jobs[k];
            if *kind == b'm' {
                let r = std::panic::catch_unwind(|| tiny_regex::re_match(p, t));
                CURRENT.store(usize::MAX, Ordering::SeqCst);
                if let Ok((a, b)) = r {
                    emit(&format!("VOCASE {} m {} {}", k, a, b));
                }
            } else {
                let r = std::panic::catch_unwind(|| tiny_regex::re_compile(p));
                CURRENT.store(usize::MAX, Ordering::SeqCst);
                match r {
                    Ok(None) => emit(&format!("VOCASE {} c 0", k)),
                    Ok(Some(re)) => {
                        let mut o = format!("VOCASE {} c 1", k);
                        for j in 0..30 {
                            let x = re.objs[j];
                            o.push_str(&format!(" {} {} {}", x.kind, x.ch, x.ccl));
                        }
                        for j in 0..40 {
                            o.push_str(&format!(" {}", re.ccl_buf[j]));
                        }
                        emit(&o);
                    }
                    Err(_) => {}
                }
            }
        }
    });
    let _ = worker.expect("vo-driver: thread").join();
}
'''


def _parse_dump(fields: list[str]) -> dict | None:
    if fields[0] == "0":
        return None
    d = [int(x) for x in fields[1:]]
    return {"objs": [d[3 * j:3 * j + 3] for j in range(30)], "ccl_buf": d[90:130]}


def _native_build(w: Path, src_dir: Path) -> dict | None:
    err = _prepare(src_dir, w)
    if err:
        return err
    p = _cargo_build(w, w / "crate", "cargo_lib")
    if p.returncode != 0:
        return {"stage": "cargo", "message": _cargo_errors(p.stderr)}
    d = w / "driver"
    (d / "src").mkdir(parents=True, exist_ok=True)
    (d / "Cargo.toml").write_text(
        '[package]\nname = "vo_driver"\nversion = "0.1.0"\nedition = "2021"\nbuild = false\n\n'
        f'[dependencies]\n{CRATE} = {{ path = "../crate" }}\n\n' + _PROFILE + "\n[workspace]\n")
    (d / "src" / "main.rs").write_text(_DRIVER)
    p = _cargo_build(w, d, "cargo_driver")
    if p.returncode != 0:
        return {"stage": "driver", "message": "the crate does not have the agreed interface. Expected:\n" + INTERFACE
                + "\n\nCompiling a caller of that interface against the crate fails:\n" + _cargo_errors(p.stderr, 5000)}
    return None


def _job_lines(jobs: list[dict]) -> str:
    return "".join(f"{j['kind']} {j['pattern'] or '-'}" + (f" {j['text'] or '-'}" if j["kind"] == "m" else "") + "\n"
                   for j in jobs)


def _native_batch(w: Path, jobs: list[dict], case_seconds: int) -> list[dict]:
    n = len(jobs)
    data = w / "batch" / "jobs.txt"
    data.parent.mkdir(exist_ok=True)
    data.write_text(_job_lines(jobs))
    exe = w / "target" / "debug" / "vo_driver"
    res: dict[int, dict] = {}
    first = 0
    while first < n:
        p = _job([exe, data, first, case_seconds * 1000], w, mem_gib=32,
                 timeout=120 + (n - first) * 2 + case_seconds, env={"RUST_BACKTRACE": "0"})
        started, timeout_of = [], None
        for line in _text(p.stdout).splitlines():
            f = line.split(" ")
            if len(f) < 2 or f[0] not in ("VOSTART", "VOCASE", "VOPANIC", "VOTIMEOUT") or not f[1].isdigit():
                continue
            k = int(f[1])
            if f[0] == "VOSTART":
                started.append(k)
            elif f[0] == "VOCASE":
                res[k] = {"m": [int(f[3]), int(f[4])]} if f[2] == "m" else {"c": _parse_dump(f[3:])}
            elif f[0] == "VOPANIC" and k not in res:
                res[k] = {"panic": json.loads(line.split(" ", 2)[2])}
            elif f[0] == "VOTIMEOUT":
                timeout_of = k
                res.setdefault(k, {"timeout": True})
        hung = [k for k in started if k not in res]
        if hung and timeout_of is None:
            res[hung[0]] = {"crash": f"the driver died (exit {p.returncode}): {_text(p.stderr).strip()[-800:]}"}
        if not started:
            for k in range(first, n):
                res[k] = {"runner_error": f"driver failed (exit {p.returncode}): {_text(p.stderr)[-800:]}"}
        first = min([k for k in range(first, n) if k not in res], default=n)
    return [res[k] for k in range(n)]


# -- extraction ---------------------------------------------------------------------------------------------------

def _extract(w: Path) -> dict | None:
    env = {"CARGO_TARGET_DIR": w / "target_charon", "TMPDIR": w / "tmp", "CARGO_TERM_COLOR": "never",
           "NO_COLOR": "1", "CARGO_NET_OFFLINE": "true"}
    p = _job([AENEAS_BIN / "charon", "cargo", "--preset=aeneas", "--", "-j1"], w / "crate", mem_gib=64, timeout=900,
             env=env, core_h=1.5)
    _save_log(w, "charon", p)
    if p.returncode in (124, 137) or b"[job timed out]" in (p.stderr or b""):
        return {"stage": "charon", "harness": True, "message": f"charon killed by the harness (exit {p.returncode})"}
    llbc = w / "crate" / f"{CRATE}.llbc"
    out = _text(p.stdout) + _text(p.stderr)
    if p.returncode != 0 or not llbc.exists() or re.search(r"^error", out, re.M):
        return {"stage": "charon", "message": "Charon (Rust to LLBC, for Aeneas) rejects the crate:\n"
                + _cargo_errors(out)}
    p = _job([AENEAS_BIN / "aeneas", "-backend", "lean", "-split-files", "-no-progress-bar", "-max-recdepth",
              "100000", "-subdir", MOD, "-dest", w / "gen", llbc], w, mem_gib=48, timeout=2400,
             env={"TMPDIR": w / "tmp", "NO_COLOR": "1"}, core_h=6.0)
    _save_log(w, "aeneas", p)
    if p.returncode in (124, 137) or b"[job timed out]" in (p.stderr or b""):
        return {"stage": "aeneas", "harness": True, "message": f"aeneas killed by the harness (exit {p.returncode})"}
    out = "\n".join(l for l in (_text(p.stdout) + _text(p.stderr)).splitlines() if "[Info" not in l)
    gen = w / "gen" / MOD
    if p.returncode != 0 or "[Error" in out or not (gen / "Funs.lean").exists():
        return {"stage": "aeneas", "message": "Aeneas (Rust to Lean) rejects the crate:\n" + out.strip()[:6000]}
    ext = sorted(gen.glob("*External_Template.lean"))
    if ext:
        names = sorted(set(re.findall(r"^(?:axiom|def|opaque)\s+(\S+)", "\n".join(e.read_text() for e in ext), re.M)))
        return {"stage": "aeneas", "message": "the crate uses functions or types that Aeneas does not model: "
                + ", ".join(names[:40])}
    err = _check_interface((gen / "Types.lean").read_text() if (gen / "Types.lean").exists() else "",
                           (gen / "Funs.lean").read_text())
    if err:
        return {"stage": "interface", "message": err}
    for mod in ("Types", "Funs"):
        src = gen / f"{mod}.lean"
        if not src.exists():
            continue
        p = _lean(w, src, olean=True, timeout=1800)
        _save_log(w, f"lean_{mod}", p)
        errs = [d for d in _messages(p.stdout)
                if d.get("severity") == "error" or "declaration uses 'sorry'" in d.get("data", "")]
        if errs or p.returncode != 0:
            lines = src.read_text().splitlines()
            shown = [f"{mod}.lean:{(d.get('pos') or {}).get('line', 0)}: {d.get('data', '')[:800]}"
                     f"{_rust_source_of(lines, (d.get('pos') or {}).get('line', 0))}" for d in errs[:5]]
            return {"stage": "lean", "message": "Lean rejects the Aeneas extraction of the crate:\n" + "\n".join(shown)
                    if shown else f"Lean fails on the Aeneas extraction (exit {p.returncode}): "
                    f"{_text(p.stderr)[-1500:]}"}
    return None


def _norm(s: str) -> str:
    return " ".join(s.replace("«", "").replace("»", "").split())


def _check_interface(types_lean: str, funs_lean: str) -> str | None:
    """The extraction must have the agreed interface (equiv-lean's statement is written against it)."""
    t, f = _norm(types_lean), _norm(funs_lean)
    want_types = [
        (r"structure RegexObj where kind : Std\.U8 ch : Std\.U8 ccl : Std\.Usize", "struct RegexObj"),
        (r"structure Regex where objs : Array RegexObj 30#usize ccl_buf : Array Std\.U8 40#usize", "struct Regex"),
    ]
    want_funs = [
        (r"def re_compile \(pattern : Slice Std\.U8\) : Result \(Option Regex\)", "re_compile"),
        (r"def re_matchp \(pattern : Option Regex\) \(text : Slice Std\.U8\) : Result \(Std\.I32 × Std\.I32\)",
         "re_matchp"),
        (r"def re_match \(pattern : Slice Std\.U8\) \(text : Slice Std\.U8\) : Result \(Std\.I32 × Std\.I32\)",
         "re_match"),
    ]
    probs = [name for rx, name in want_types if not re.search(rx, t)]
    probs += [name for rx, name in want_funs if not re.search(rx, f)]
    if not probs:
        return None
    return ("the crate does not have the agreed interface. Expected:\n" + INTERFACE + "\n\nbut the extraction differs "
            "for: " + ", ".join(probs))


_LEAN_HELPERS = r'''
def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87

def ofHex : List Char → List Std.U8
  | a :: b :: rest => ⟨BitVec.ofNat 8 (hexVal a * 16 + hexVal b)⟩ :: ofHex rest
  | _ => []

def bs (s : String) : Slice Std.U8 := slice (ofHex s.toList)

def resM (k : Nat) (r : Result (Std.I32 × Std.I32)) : String :=
  match r.match with
  | .ok (a, b) => "VORES " ++ toString k ++ " ok m " ++ toString a.val ++ " " ++ toString b.val
  | .div => "VORES " ++ toString k ++ " div"
  | .vis (.fail e) _ => "VORES " ++ toString k ++ " fail " ++ reprStr e

def resC (k : Nat) (r : Result (Option %(crate)s.Regex)) : String :=
  match r.match with
  | .ok none => "VORES " ++ toString k ++ " ok c 0"
  | .ok (some re) =>
    let objs := re.objs.val.map fun o =>
      toString o.kind.val ++ " " ++ toString o.ch.val ++ " " ++ toString o.ccl.val
    let buf := re.ccl_buf.val.map fun b => toString b.val
    "VORES " ++ toString k ++ " ok c 1 " ++ String.intercalate " " (objs ++ buf)
  | .div => "VORES " ++ toString k ++ " div"
  | .vis (.fail e) _ => "VORES " ++ toString k ++ " fail " ++ reprStr e
'''


def _lean_module(jobs: list[tuple[int, dict]], limit_ms: int, out: Path) -> tuple[str, dict[int, int]]:
    parts = [_LEAN_PRELUDE % {"mod": MOD}, _LEAN_HELPERS % {"crate": CRATE}, "end VoEval\n"]
    evals = []
    for k, j in jobs:
        call = (f'VoEval.resM {k} ({CRATE}.re_match (VoEval.bs "{j["pattern"]}") (VoEval.bs "{j["text"]}"))'
                if j["kind"] == "m" else f'VoEval.resC {k} ({CRATE}.re_compile (VoEval.bs "{j["pattern"]}"))')
        evals.append(f'#eval VoEval.evalCase "{out}" {k} {limit_ms} fun _ => {call}')
    text = "\n".join(parts) + "\n" + "\n".join(evals) + "\n"
    at = [i + 1 for i, line in enumerate(text.splitlines()) if line.startswith("#eval ")]
    return text, {k: line for (k, _), line in zip(jobs, at)}


def _lean_batch(w: Path, jobs: list[dict], skip: set[int], lean_seconds: int) -> list[dict]:
    n = len(jobs)
    res = {k: {"skipped": "native timeout"} for k in skip}
    todo = [k for k in range(n) if k not in res]
    rnd = 0
    while todo:
        src = w / "gen" / MOD / f"Eval{rnd}.lean"
        out = w / "batch" / f"lean{rnd}.txt"
        out.parent.mkdir(exist_ok=True)
        out.write_text("")
        text, at = _lean_module([(k, jobs[k]) for k in todo], lean_seconds * 1000, out)
        src.write_text(text)
        p = _lean(w, src, olean=False, timeout=900 + len(todo) * 2 + lean_seconds)
        _save_log(w, f"lean_eval{rnd}", p)
        started, new = [], 0
        for line in out.read_text().splitlines():
            f = line.split(" ")
            if len(f) < 2 or f[0] not in ("VOSTART", "VORES", "VOTIMEOUT") or not f[1].isdigit():
                continue
            k = int(f[1])
            if f[0] == "VOSTART":
                started.append(k)
                continue
            new += 1
            if f[0] == "VOTIMEOUT":
                res[k] = {"timeout": True}
            elif f[2] == "ok":
                res[k] = {"m": [int(f[4]), int(f[5])]} if f[3] == "m" else {"c": _parse_dump(f[4:])}
            elif f[2] == "div":
                res[k] = {"div": True}
            else:
                res[k] = {"fail": " ".join(f[3:])[:300]}
        case_at = {line: k for k, line in at.items()}
        for d in _messages(p.stdout):
            if d.get("severity") != "error":
                continue
            k = case_at.get((d.get("pos") or {}).get("line"))
            if k is None:
                raise RuntimeError(f"Lean evaluation module {src} does not elaborate: {d.get('data', '')[:2000]}")
            if k not in res:
                res[k], new = {"runner_error": "Lean: " + d.get("data", "")[:800]}, new + 1
        hung = [k for k in started if k not in res]
        tail = (_text(p.stderr) + _text(p.stdout))[-800:]
        if hung:
            res[hung[0]] = {"crash": f"the Lean evaluation died (exit {p.returncode}): {tail}"}
        elif not new:
            for k in todo:
                res.setdefault(k, {"runner_error": f"Lean evaluation fails (exit {p.returncode}): {tail}"})
        todo = [k for k in todo if k not in res]
        rnd += 1
    return [res[k] for k in range(n)]


def run_batch(src_dir, jobs: list[dict], *, lean: bool = True, case_seconds: int = CASE_SECONDS,
              lean_seconds: int = LEAN_CASE_SECONDS) -> list[dict]:
    src_dir = Path(src_dir)
    w = workdir(src_dir)
    with _locked(w / "lock"):
        key = hashlib.sha256(json.dumps([jobs, lean, case_seconds, lean_seconds], sort_keys=True).encode())
        cache = w / "results" / f"{key.hexdigest()[:20]}.json"
        if cache.exists():
            return json.loads(cache.read_text())
        err = _once(w, "native_build", lambda: _native_build(w, src_dir))
        if err:
            st = "runner_error" if err.get("harness") else "compile_error"
            return [{"status": st, "stage": err["stage"], "message": err["message"]}]
        xerr = _once(w, "extract", lambda: _extract(w)) if lean else None
        nat = _native_batch(w, jobs, case_seconds)
        if xerr:        # the crate builds but is outside the verifier's language: the native results are kept
            st = "runner_error" if xerr.get("harness") else "compile_error"
            return [{"status": st, "stage": xerr["stage"], "message": xerr["message"], "native": nat}]
        if lean:
            skip = {k for k, r in enumerate(nat) if r.get("timeout")}
            out = [{"native": a, "aeneas": b} for a, b in zip(nat, _lean_batch(w, jobs, skip, lean_seconds))]
        else:
            out = [{"native": a} for a in nat]
        if not any("runner_error" in r.get("native", {}) or "runner_error" in r.get("aeneas", {}) for r in out):
            cache.parent.mkdir(exist_ok=True)
            cache.write_text(json.dumps(out))
        return out
