"""Rust runner for item A (certified modernization of CardDemo batch programs).

INTERFACES.md defines the test case, the outcome, the runner contract and the naive-arm I/O contract;
styleguide_rust.md the guided arm's crate; mapping.py the mapping (runs/modernize/<PROG>/mapping.json).

Every entry point takes the translation directory, test-case JSON dicts and the mapping dict:
* `run_guided_batch(trans_dir, cases, mapping)`, `run_guided(trans_dir, case, mapping)`: `<trans_dir>/rust/` is
  the library crate of the style guide. Every case runs twice:
  - native: cargo builds the crate and a generated driver crate that depends on it by path. ONE driver process
    reads all cases from a data file, builds the input records (files, linkage items, clock), calls `run` on each
    case (a panic is caught per case; a watchdog ends a case that runs too long) and prints each outcome as
    canonical JSON;
  - Lean: Charon and Aeneas extract the crate, Lean compiles the extraction, and ONE generated module `#eval`s the
    extracted `run` on every case (each on its own thread, with a time limit) and prints the same JSON.
  A process that ends early (time limit, crash) is started again after the case it was on. An OCCURS field is an
  array (`[i64; k]`, `[[u8; n]; k]`) and a JSON list of k values; a VARYING file's writes are `Vec<Vec<u8>>`,
  reported as {"<record written FROM>": "<text>"} like cobol.decode_varying.
* `run_naive_batch(trans_dir, cases, mapping)`, `run_naive(trans_dir, case, mapping)`: `<trans_dir>/rust/` is a
  binary crate following the naive I/O contract. Each case runs in its own directory holding the input files under
  their ASSIGN names, one record per line, UTF-8: the record image of the INTO record with every EBCDIC byte shown
  as its CP037 character (zoned digits as digits; a signed field's last digit overpunched '{', 'A'-'I' (+) or
  '}', 'J'-'R' (-), or a separate '+'/'-' for SIGN SEPARATE). The clock is in COBOL_CURRENT_DATE, the linkage
  record's text fields are argv[1]. stdout lines are the displays; the files left under the ASSIGN names of the
  output files are the writes; exit status 999 (231 as a POSIX status) is an abend; when the program sets
  RETURN-CODE, the exit status is the return code. For a file the program reads and also writes back, the writes
  are the records whose key is new and the rewrites the records that changed, in file order (a REWRITE that
  leaves a record as it was cannot be seen). All cases run inside one run1.sh job.

Results (the contract of loop.py):
* a version that does not build gives ONE element, [{"status": "compile_error", "message": str, "stage": str}]: cargo
  on the crate, cargo on the driver (the crate lacks the style guide's interface), Charon, Aeneas (also when the
  crate calls functions Aeneas does not model), the interface check on the extraction, or Lean's elaboration of it;
* otherwise one dict per case, in order: {"executions": {"native": R, "aeneas": R}, "agree": bool | None,
  "disagreement": str | None} (naive: native only, plus `files_after`: every file the program writes or rewrites,
  as it left it, decoded by the record it REWRITEs or WRITEs FROM; a file it did not leave is absent). R is
  {"outcome": <canonical outcome>} or {"status": "runtime_error", "message": str} (+ "timeout": true); native R may
  add `stdout` (lines the translation printed itself). An execution that could not run (Lean after a native timeout,
  or a runner failure) is left out and named in `not_run`. `agree` says whether the two executions gave the same
  result.

Only the translation's `src/**/*.rs` is used: the runner writes its own Cargo.toml (crate name from the mapping, no
dependencies, no build script; overflow checks on, as in Aeneas's semantics). Every cargo, Charon, Aeneas, Lean and
program job goes through scripts/run1.sh. Work directories are `<work_dir>/<arm>-<key>` (default work_dir
scratch/modernize_rust/work/<PROG>), keyed by the sources, the mapping and RUNNER_VERSION: later batches on the
same version reuse the builds, and guided results are cached per batch (`run` is a pure function).
"""
from __future__ import annotations

import contextlib
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

VO_ROOT = Path(os.environ.get("VO_ROOT", "/home/user/veriforch"))
RUN1 = VO_ROOT / "scripts" / "run1.sh"
WORK = VO_ROOT / "scratch" / "modernize_rust" / "work"
HOME = Path.home()
CARGO = HOME / ".cargo" / "bin" / "cargo"
AENEAS_BIN = HOME / "equivlean_work" / "dl" / "rel" / "aeneas_bin"
AENEAS_LEAN = HOME / "equivlean_work" / "dl" / "aeneas" / "backends" / "lean"
# Aeneas's Lean library was built inside equiv-lean's workspace: its dependencies (mathlib, ...) are equiv-lean's
# packages, at the revisions of Aeneas's own manifest (checked in `_lean_path`)
LEAN_PACKAGES = HOME / "equivlean" / ".lake" / "packages"
LEAN_BIN = HOME / ".elan" / "toolchains" / "leanprover--lean4---v4.35.0" / "bin" / "lean"
RUNNER_VERSION = "rustrun-7"
ABEND_STATUS = 999 & 0xFF          # exit(999) as the parent process sees it
CASE_SECONDS = 10                  # per-case limit of a native run
LEAN_CASE_SECONDS = 60             # per-case limit of a Lean evaluation
OUTPUT_CAP = 64 << 20              # bytes of an outcome / of stdout or an output file read back, per case
MOD = "VoRust"                     # Lean module prefix of the extraction (one per work directory)
LEAN_TSTACK_KB = 4 << 20           # stack of Lean's threads (KiB)


# -- jobs ---------------------------------------------------------------------------------------------------------

def _job(cmd: list, cwd: Path, *, mem_gib: int, timeout: int, env: dict | None = None,
         core_h: float | None = None) -> subprocess.CompletedProcess:
    """One job under scripts/run1.sh (address-space cap, wall-clock timeout, core-hour guard). Aeneas runs on
    several OCaml domains (CBACT04C: 4.3 min wall, ~7 cores, 0.5 core-h), so it gets an explicit core-hour cap."""
    core_h = core_h if core_h is not None else max(0.25, 1.25 * timeout / 3600)
    full = [str(RUN1), "-t", str(timeout), "-m", str(mem_gib), "-c", f"{core_h:.2f}", "-l", str(WORK / "guard.log"),
            "--"]
    if env:
        full += ["env"] + [f"{k}={v}" for k, v in env.items()]
    full += [str(c) for c in cmd]
    try:
        return subprocess.run(full, cwd=cwd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, timeout=timeout + 200)
    except subprocess.TimeoutExpired as e:
        return subprocess.CompletedProcess(full, 124, e.stdout or b"", (e.stderr or b"") + b"\n[job timed out]")


def _text(b: bytes | str | None) -> str:
    s = b.decode("utf-8", "replace") if isinstance(b, bytes) else (b or "")
    return re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", s)


def _save_log(w: Path, name: str, p: subprocess.CompletedProcess) -> None:
    (w / "logs").mkdir(exist_ok=True)
    (w / "logs" / f"{name}.txt").write_text(f"$ {' '.join(map(str, p.args))}\nexit {p.returncode}\n--- stdout\n"
                                            f"{_text(p.stdout)}\n--- stderr\n{_text(p.stderr)}\n")


def _cargo_errors(text, limit: int = 8000) -> str:
    """cargo's error diagnostics (warnings dropped), at most `limit` characters."""
    blocks = re.split(r"\n(?=(?:error|warning)(?:\[\w+\])?: )", "\n" + _text(text))
    errs = [b.strip() for b in blocks if b.lstrip().startswith("error")]
    return ("\n\n".join(errs) or _text(text).strip()[-limit:])[:limit]


def _cargo_env(w: Path) -> dict:
    return {"CARGO_TARGET_DIR": w / "target", "TMPDIR": w / "tmp", "RUSTUP_TOOLCHAIN": "stable",
            "CARGO_TERM_COLOR": "never", "CARGO_NET_OFFLINE": "true", "CARGO_INCREMENTAL": "0"}


@contextlib.contextmanager
def _locked(path: Path):
    with open(path, "w") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)


def _load(x) -> dict:
    """A JSON object given as a dict, a JSON text or a path."""
    if isinstance(x, dict):
        return x
    if isinstance(x, Path) or (isinstance(x, str) and not x.lstrip().startswith("{")):
        return json.loads(Path(x).read_text())
    return json.loads(x)


# -- mapping and cases --------------------------------------------------------------------------------------------

def _inputs(m: dict) -> list[dict]:
    """The files that are parameters of `run`, in SELECT order."""
    return [f for f in m["files"] if f["input"]]


def _linkage(m: dict) -> list[dict]:
    """The PROCEDURE DIVISION USING items, in order: a group has `record`, an elementary item `field`."""
    return m.get("linkage") or []


def _outputs(m: dict) -> list[tuple[str, dict, str, str]]:
    """(writes | rewrites, file, record written FROM, Rust field of Output) for every written file."""
    out = []
    for kind in ("write", "rewrite"):
        for f in m["files"]:
            if f.get(f"{kind}_from"):
                out.append((kind + "s", f, f[f"{kind}_from"], f[f"rust_{kind}s"]))
    return out


def _records_used(m: dict) -> tuple[list[str], list[str]]:
    """The records `run` takes (input files, linkage groups) and the records Output holds as structs (a VARYING
    file's writes are bytes)."""
    ins = [f["record"] for f in _inputs(m)] + [lk["record"] for lk in _linkage(m) if "record" in lk]
    return (list(dict.fromkeys(ins)),
            list(dict.fromkeys(r for _, f, r, _ in _outputs(m) if not f.get("varying"))))


def _check_value(fl: dict, v, where: str) -> None:
    if fl.get("occurs"):
        if not isinstance(v, list) or len(v) != fl["occurs"]:
            raise ValueError(f"{where}: {fl['cobol']} needs a list of {fl['occurs']} values")
        for x in v:
            _check_scalar(fl, x, where)
    else:
        _check_scalar(fl, v, where)


def _check_scalar(fl: dict, v, where: str) -> None:
    if fl["kind"] == "alnum":
        if not isinstance(v, str) or len(v) != fl["len"] or any(ord(c) > 0xFF for c in v):
            raise ValueError(f"{where}: {fl['cobol']} must be {fl['len']} Latin-1 characters")
    elif (not isinstance(v, int) or isinstance(v, bool) or abs(v) >= 10 ** fl["digits"]
          or (v < 0 and not fl["signed"])):
        raise ValueError(f"{where}: {fl['cobol']} = {v!r} does not fit its PIC")


def _check_record(rec: dict, r: dict, where: str) -> None:
    for fl in rec["fields"]:
        if fl["cobol"] not in r:
            raise ValueError(f"{where}: no value for {fl['cobol']}")
        _check_value(fl, r[fl["cobol"]], where)


def _check_case(m: dict, case: dict) -> None:
    """Refuse a test case that does not fit the mapping (an input-generator error, not the translation's)."""
    for f in _inputs(m):
        spec = case.get("files", {}).get(f["fd"], {"records": []})
        if spec.get("record", f["record"]) != f["record"]:
            raise ValueError(f"case file {f['fd']} has record {spec.get('record')}, the mapping {f['record']}")
        for i, r in enumerate(spec["records"]):
            _check_record(m["records"][f["record"]], r, f"{f['fd']} record {i}")
    for lk in _linkage(m):
        v = case.get("linkage", {}).get(lk["name"])
        if v is None:
            raise ValueError(f"case lacks linkage item {lk['name']}")
        if "record" in lk:
            _check_record(m["records"][lk["record"]], v, f"linkage {lk['name']}")
        else:
            _check_value(lk["field"], v, f"linkage {lk['name']}")
    if m["clock"]:
        c = case.get("clock")
        if not isinstance(c, str) or len(c) != 21 or any(ord(ch) > 0xFF for ch in c):
            raise ValueError("the program reads the clock: the case needs a 21-character clock")


def _case_records(case: dict, f: dict) -> list[dict]:
    return case.get("files", {}).get(f["fd"], {"records": []})["records"]


def _rust_type(fl: dict) -> str:
    t = f"[u8; {fl['len']}]" if fl["kind"] == "alnum" else "i64"
    return f"[{t}; {fl['occurs']}]" if fl.get("occurs") else t


def _expected_interface(m: dict) -> str:
    """The crate interface the style guide asks for, in Rust (part of every interface error message)."""
    ins, outs = _records_used(m)
    lines = []
    for name in dict.fromkeys(ins + outs):
        rec = m["records"][name]
        fields = ", ".join(f"pub {fl['rust']}: {_rust_type(fl)}" for fl in rec["fields"])
        lines.append(f"#[derive(Clone, Copy)] pub struct {rec['class']} {{ {fields} }}")
    of = ["pub displays: Vec<Vec<u8>>"]
    of += [f"pub {fld}: Vec<Vec<u8>>" if f.get("varying") else f"pub {fld}: Vec<{m['records'][r]['class']}>"
           for _, f, r, fld in _outputs(m)]
    of += (["pub return_code: i64"] if m.get("return_code") else []) + ["pub abended: bool"]
    lines.append(f"pub struct Output {{ {', '.join(of)} }}")
    params = [f"{f['rust_param']}: &[{m['records'][f['record']]['class']}]" for f in _inputs(m)]
    params += [f"{lk['rust_param']}: &{m['records'][lk['record']]['class']}" if "record" in lk else
               f"{lk['rust_param']}: {_rust_type(lk['field'])}" for lk in _linkage(m)]
    params += ["clock: &[u8; 21]"] if m["clock"] else []
    lines.append(f"pub fn run({', '.join(params)}) -> Output")
    return "\n".join(lines)


def _ident(name: str) -> str:
    return re.sub(r"[^a-z0-9]", "_", name.lower())


# -- work directories and builds ----------------------------------------------------------------------------------

def _workdir(arm: str, trans_dir: Path, m: dict, work_dir) -> Path:
    if not re.fullmatch(r"[A-Z0-9-]+", m["program"]) or not re.fullmatch(r"[a-z0-9_]+", m["rust_crate"]):
        raise ValueError(f"bad program / crate name in the mapping: {m['program']} {m['rust_crate']}")
    h = hashlib.sha256(f"{RUNNER_VERSION}\n{arm}\n{json.dumps(m, sort_keys=True)}\n".encode())
    src = Path(trans_dir) / "rust" / "src"
    files = sorted(p for p in src.rglob("*.rs") if p.is_file() and not p.is_symlink()) if src.is_dir() else []
    for p in files:
        h.update(b"\0" + p.relative_to(src).as_posix().encode() + b"\0" + p.read_bytes())
    w = (Path(work_dir) if work_dir else WORK / m["program"]) / f"{arm}-{h.hexdigest()[:16]}"
    (w / "tmp").mkdir(parents=True, exist_ok=True)
    return w


_PROFILE = """[profile.dev]
opt-level = 1
debug = false
overflow-checks = true
debug-assertions = true
incremental = false
"""


def _prepare_crate(trans_dir: Path, m: dict, kind: str, dest: Path) -> dict | None:
    """Copy the translation's src/**/*.rs into `dest` and write the runner's Cargo.toml."""
    src = Path(trans_dir) / "rust" / "src"
    root = "lib.rs" if kind == "lib" else "main.rs"
    if not (src / root).is_file():
        return {"stage": "setup", "message": f"the crate has no src/{root}"}
    if not (dest / "Cargo.toml").exists():          # the work directory is keyed by these sources: copy once
        for p in sorted(src.rglob("*.rs")):
            if p.is_file() and not p.is_symlink():
                out = dest / "src" / p.relative_to(src)
                out.parent.mkdir(parents=True, exist_ok=True)
                out.write_bytes(p.read_bytes())
        crate = m["rust_crate"]
        target = ('[lib]\npath = "src/lib.rs"\n' if kind == "lib" else
                  f'[[bin]]\nname = "{crate}"\npath = "src/main.rs"\n')
        (dest / "Cargo.toml").write_text(
            f'[package]\nname = "{crate}"\nversion = "0.1.0"\nedition = "2021"\nbuild = false\nautobins = false\n'
            f'autoexamples = false\nautotests = false\nautobenches = false\n\n{target}\n[dependencies]\n\n'
            + _PROFILE + "\n[workspace]\n")
    return None


def _once(w: Path, name: str, fn) -> dict | None:
    """Run a build step once per work directory. Success is kept in a stamp file; errors are not, so a transient
    failure does not stick to the version."""
    p = w / f"{name}.ok"
    if p.exists():
        return None
    err = fn()
    if err is None:
        p.write_text("ok\n")
    return err


def _cargo_build(w: Path, crate_dir: Path, log: str) -> subprocess.CompletedProcess:
    p = _job([CARGO, "build", "-j", "1", "--offline"], crate_dir, mem_gib=64, timeout=900, env=_cargo_env(w))
    _save_log(w, log, p)
    return p


# -- results ------------------------------------------------------------------------------------------------------

def _exe(status: str, outcome: dict | None = None, message: str | None = None, timeout: bool = False) -> dict:
    """An execution's result: {"outcome": ...}, or {"status": runtime_error | skipped | runner_error, "message"}."""
    if status == "outcome":
        return {"outcome": outcome}
    return {"status": status, "message": message, **({"timeout": True} if timeout else {})}


def _status(r: dict) -> str:
    return "outcome" if "outcome" in r else r["status"]


def _same(a: dict, b: dict) -> bool:
    return _status(a) == _status(b) and ("outcome" not in a or a["outcome"] == b["outcome"])


def _disagreement(a: dict, b: dict) -> str:
    if _status(a) != _status(b):
        return f"native {_status(a)}, aeneas {_status(b)}: {(a.get('message') or b.get('message') or '')[:300]}"
    x, y = a["outcome"], b["outcome"]
    for k in ("end", "return_code", "writes", "rewrites"):
        if x.get(k) != y.get(k):
            return f"{k}: native {json.dumps(x.get(k))[:300]}, aeneas {json.dumps(y.get(k))[:300]}"
    dx, dy = x["displays"], y["displays"]
    for i in range(max(len(dx), len(dy))):
        u, v = (dx[i] if i < len(dx) else None), (dy[i] if i < len(dy) else None)
        if u != v:
            return f"display {i}: native {json.dumps(u)}, aeneas {json.dumps(v)}"
    return "runtime errors with different messages"


def _result(native: dict, lean: dict | None = None) -> dict:
    out = {"executions": {"native": native}, "agree": None, "disagreement": None}
    if lean is not None:
        if lean.get("status") in ("skipped", "runner_error"):
            out["not_run"] = {"aeneas": lean["message"]}
        else:
            out["executions"]["aeneas"] = lean
            out["agree"] = _same(native, lean)
            out["disagreement"] = None if out["agree"] else _disagreement(native, lean)
    return out


def _compile_error(err: dict) -> list[dict]:
    """The whole version does not build: one element, whatever the number of cases. A tool the harness killed
    (time or core-hour cap) is a runner error, not the translation's fault."""
    if err.get("harness"):
        return [{"status": "runner_error", "message": err["message"], "stage": err["stage"]}]
    return [{"status": "compile_error", "message": err["message"], "stage": err["stage"]}]


# -- guided arm: native driver ------------------------------------------------------------------------------------

_DRIVER_PRELUDE = r'''#![allow(unused)]
use std::io::Write;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

static CURRENT: AtomicUsize = AtomicUsize::new(usize::MAX);
static STARTED: AtomicU64 = AtomicU64::new(0);
const OUTPUT_CAP: usize = %(cap)d;

fn now_ms() -> u64 {
    match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => d.as_millis() as u64,
        Err(_) => 0,
    }
}

/// One marker line; the leading newline ends a line the translation may have left open.
fn emit(line: &str) {
    let out = std::io::stdout();
    let mut lock = out.lock();
    let _ = lock.write_all(b"\n");
    let _ = lock.write_all(line.as_bytes());
    let _ = lock.write_all(b"\n");
    let _ = lock.flush();
}

struct Tok<'a> {
    it: std::str::SplitAsciiWhitespace<'a>,
}

impl<'a> Tok<'a> {
    fn word(&mut self) -> &'a str {
        self.it.next().expect("vo-driver: truncated case file")
    }
    fn count(&mut self) -> usize {
        self.word().parse().expect("vo-driver: bad count")
    }
    fn num(&mut self) -> i64 {
        self.word().parse().expect("vo-driver: bad number")
    }
    fn alnum<const N: usize>(&mut self) -> [u8; N] {
        let w = self.word().as_bytes();
        assert!(w.len() == 2 * N, "vo-driver: bad alphanumeric");
        let mut a = [0u8; N];
        for i in 0..N {
            a[i] = (hex(w[2 * i]) << 4) | hex(w[2 * i + 1]);
        }
        a
    }
    fn nums<const K: usize>(&mut self) -> [i64; K] {
        let mut a = [0i64; K];
        for i in 0..K {
            a[i] = self.num();
        }
        a
    }
    fn alnums<const K: usize, const N: usize>(&mut self) -> [[u8; N]; K] {
        let mut a = [[0u8; N]; K];
        for i in 0..K {
            a[i] = self.alnum::<N>();
        }
        a
    }
}

fn hex(c: u8) -> u8 {
    match c {
        b'0'..=b'9' => c - b'0',
        b'a'..=b'f' => c - b'a' + 10,
        _ => panic!("vo-driver: bad hex digit"),
    }
}

/// A JSON string of Latin-1 bytes (one character per byte).
fn jstr(o: &mut String, b: &[u8]) {
    o.push('"');
    for &c in b {
        match c {
            b'"' => o.push_str("\\\""),
            b'\\' => o.push_str("\\\\"),
            0x20..=0x7e => o.push(c as char),
            _ => o.push_str(&format!("\\u{:04x}", c)),
        }
    }
    o.push('"');
}

/// A JSON list of numbers (an OCCURS numeric field).
fn jnums(o: &mut String, a: &[i64]) {
    o.push('[');
    for (i, x) in a.iter().enumerate() {
        if i > 0 {
            o.push_str(", ");
        }
        o.push_str(&x.to_string());
    }
    o.push(']');
}

/// A JSON list of strings (an OCCURS alphanumeric field).
fn jstrs<const N: usize>(o: &mut String, a: &[[u8; N]]) {
    o.push('[');
    for (i, x) in a.iter().enumerate() {
        if i > 0 {
            o.push_str(", ");
        }
        jstr(o, x);
    }
    o.push(']');
}
'''

_DRIVER_MAIN = r'''
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let data = std::fs::read_to_string(&args[1]).expect("vo-driver: case file");
    let first: usize = args[2].parse().expect("vo-driver: first case");
    let limit_ms: u64 = args[3].parse().expect("vo-driver: time limit");
    let mut t = Tok { it: data.split_ascii_whitespace() };
    let n = t.count();
    let mut cases = Vec::new();
    for _ in 0..n {
        cases.push(read_case(&mut t));
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
            Some(l) => format!(" ({}:{})", l.file(), l.line()),
            None => String::new(),
        };
        let mut o = String::new();
        jstr(&mut o, format!("{}{}", msg, at).as_bytes());
        emit(&format!("VOPANIC {} {}", CURRENT.load(Ordering::SeqCst), o));
    }));
    std::thread::spawn(move || loop {
        std::thread::sleep(std::time::Duration::from_millis(20));
        let k = CURRENT.load(Ordering::SeqCst);
        if k != usize::MAX && now_ms().saturating_sub(STARTED.load(Ordering::SeqCst)) > limit_ms {
            emit(&format!("VOTIMEOUT {}", k));
            std::process::exit(3);
        }
    });
    // a large stack: deep recursion in a translation should not end the batch
    let worker = std::thread::Builder::new().stack_size(1 << 28).spawn(move || {
        for k in first..cases.len() {
            STARTED.store(now_ms(), Ordering::SeqCst);
            CURRENT.store(k, Ordering::SeqCst);
            emit(&format!("VOSTART {}", k));
            let c = &cases[k];
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| %(crate)s::run(%(args)s)));
            CURRENT.store(usize::MAX, Ordering::SeqCst);
            if let Ok(out) = r {
                let mut o = String::new();
                json_output(&mut o, &out);
                if o.len() > OUTPUT_CAP {
                    emit(&format!("VOBIG {}", k));
                } else {
                    emit(&format!("VOCASE {} {}", k, o));
                }
            }
        }
    });
    let _ = worker.expect("vo-driver: thread").join();
}
'''


def _rs_read(fl: dict) -> str:
    """The driver's expression reading one field's tokens."""
    if fl.get("occurs"):
        return f"t.alnums::<{fl['occurs']}, {fl['len']}>()" if fl["kind"] == "alnum" else f"t.nums::<{fl['occurs']}>()"
    return f"t.alnum::<{fl['len']}>()" if fl["kind"] == "alnum" else "t.num()"


def _rs_json(fl: dict, place: str) -> str:
    """The driver's statement printing one field's value as JSON."""
    if fl.get("occurs"):
        return f"jstrs(o, &{place});" if fl["kind"] == "alnum" else f"jnums(o, &{place});"
    return f"jstr(o, &{place});" if fl["kind"] == "alnum" else f"o.push_str(&{place}.to_string());"


def _driver_source(m: dict) -> str:
    crate, recs = m["rust_crate"], m["records"]
    ins, outs = _records_used(m)
    parts = [_DRIVER_PRELUDE % {"cap": OUTPUT_CAP}]
    for name in ins:
        rec = recs[name]
        inits = ", ".join(f"{fl['rust']}: {_rs_read(fl)}" for fl in rec["fields"])
        parts.append(f"fn read_{_ident(name)}(t: &mut Tok) -> {crate}::{rec['class']} {{\n"
                     f"    {crate}::{rec['class']} {{ {inits} }}\n}}\n")
    for name in outs:
        rec = recs[name]
        body = []
        for i, fl in enumerate(rec["fields"]):
            body.append(f'    o.push_str("{", " if i else "{"}\\"{fl["cobol"]}\\": ");')
            body.append(f"    {_rs_json(fl, 'r.' + fl['rust'])}")
        parts.append(f"fn json_{_ident(name)}(o: &mut String, r: &{crate}::{rec['class']}) {{\n" + "\n".join(body)
                     + "\n    o.push('}');\n}\n")
    fields, body, args = [], [], []
    for i, f in enumerate(_inputs(m)):
        fields.append(f"    f{i}: Vec<{crate}::{recs[f['record']]['class']}>,")
        body.append(f"    let mut f{i} = Vec::new();\n    for _ in 0..t.count() {{\n"
                    f"        f{i}.push(read_{_ident(f['record'])}(t));\n    }}")
        args.append(f"&c.f{i}")
    for i, lk in enumerate(_linkage(m)):
        if "record" in lk:
            fields.append(f"    l{i}: {crate}::{recs[lk['record']]['class']},")
            body.append(f"    let l{i} = read_{_ident(lk['record'])}(t);")
            args.append(f"&c.l{i}")
        else:
            fl = lk["field"]
            fields.append(f"    l{i}: {_rust_type(fl)},")
            body.append(f"    let l{i} = {_rs_read(fl)};")
            args.append(f"c.l{i}")
    if m["clock"]:
        fields.append("    clock: [u8; 21],")
        body.append("    let clock = t.alnum::<21>();")
        args.append("&c.clock")
    names = [re.match(r"\s*(\w+):", x).group(1) for x in fields]
    parts.append("struct Case {\n" + "\n".join(fields) + "\n}\n")
    parts.append("fn read_case(t: &mut Tok) -> Case {\n" + "\n".join(body)
                 + f"\n    Case {{ {', '.join(names)} }}\n}}\n")
    body = ['    o.push_str("{\\"end\\": ");',
            '    o.push_str(if out.abended { "\\"abend\\"" } else { "\\"normal\\"" });',
            '    o.push_str(", \\"displays\\": [");',
            "    for (i, d) in out.displays.iter().enumerate() {",
            '        if i > 0 {\n            o.push_str(", ");\n        }',
            "        jstr(o, d);",
            "    }",
            "    o.push(']');"]
    for kind in ("writes", "rewrites"):
        body += [f'    o.push_str(", \\"{kind}\\": {{");', "    let mut first = true;"]
        for k, f, r, fld in _outputs(m):
            if k != kind:
                continue
            body += [f"    if !out.{fld}.is_empty() {{",
                     '        if !first {\n            o.push_str(", ");\n        }',
                     "        first = false;",
                     f'        o.push_str("\\"{f["fd"]}\\": [");',
                     f"        for (i, r) in out.{fld}.iter().enumerate() {{",
                     '            if i > 0 {\n                o.push_str(", ");\n            }',
                     f'            o.push_str("{{\\"{r}\\": ");\n            jstr(o, r);\n            o.push(\'}}\');'
                     if f.get("varying") else f"            json_{_ident(r)}(o, r);",
                     "        }",
                     "        o.push(']');",
                     "    }"]
        body.append("    o.push('}');")
    body.append('    o.push_str(", \\"return_code\\": ");')
    body.append("    o.push_str(&out.return_code.to_string());" if m.get("return_code") else '    o.push_str("null");')
    body.append("    o.push('}');")
    parts.append(f"fn json_output(o: &mut String, out: &{crate}::Output) {{\n" + "\n".join(body) + "\n}\n")
    parts.append(_DRIVER_MAIN % {"crate": crate, "args": ", ".join(args)})
    return "\n".join(parts)


def _token(fl: dict, v) -> str:
    return v.encode("latin-1").hex() if fl["kind"] == "alnum" else str(v)


def _tokens(rec: dict, r: dict) -> str:
    out = []
    for fl in rec["fields"]:
        v = r[fl["cobol"]]
        out += [_token(fl, x) for x in v] if fl.get("occurs") else [_token(fl, v)]
    return " ".join(out)


def _case_data(m: dict, cases: list[dict]) -> str:
    """The driver's input: whitespace-separated tokens (numbers in decimal, alphanumerics as hex of Latin-1)."""
    out = [str(len(cases))]
    for case in cases:
        for f in _inputs(m):
            rs = _case_records(case, f)
            out += [str(len(rs))] + [_tokens(m["records"][f["record"]], r) for r in rs]
        for lk in _linkage(m):
            v = case["linkage"][lk["name"]]
            out.append(_tokens(m["records"][lk["record"]], v) if "record" in lk else
                       _tokens({"fields": [lk["field"]]}, {lk["field"]["cobol"]: v}))
        if m["clock"]:
            out.append(case["clock"].encode("latin-1").hex())
    return "\n".join(out) + "\n"


def _native_build(w: Path, trans_dir: Path, m: dict) -> dict | None:
    err = _prepare_crate(trans_dir, m, "lib", w / "crate")
    if err:
        return err
    p = _cargo_build(w, w / "crate", "cargo_lib")
    if p.returncode != 0:
        return {"stage": "cargo", "message": _cargo_errors(p.stderr)}
    d = w / "driver"
    (d / "src").mkdir(parents=True, exist_ok=True)
    (d / "Cargo.toml").write_text(
        f'[package]\nname = "vo_driver"\nversion = "0.1.0"\nedition = "2021"\nbuild = false\n\n'
        f'[dependencies]\n{m["rust_crate"]} = {{ path = "../crate" }}\n\n' + _PROFILE + "\n[workspace]\n")
    (d / "src" / "main.rs").write_text(_driver_source(m))
    p = _cargo_build(w, d, "cargo_driver")
    if p.returncode != 0:
        return {"stage": "driver", "message": "the crate does not have the interface of styleguide_rust.md. "
                "Expected:\n" + _expected_interface(m) + "\n\nCompiling a caller of that interface against the crate "
                "fails:\n" + _cargo_errors(p.stderr, 5000)}
    return None


def _native_batch(w: Path, m: dict, cases: list[dict], case_seconds: int) -> list[dict]:
    """Run the driver on all cases; a case that crashes the driver (abort, stack overflow) is a runtime error and
    the driver restarts after it."""
    n = len(cases)
    data = w / "batch" / "cases.txt"
    data.parent.mkdir(exist_ok=True)
    data.write_text(_case_data(m, cases))
    exe = w / "target" / "debug" / "vo_driver"
    res: dict[int, dict] = {}
    printed: dict[int, list[str]] = {}
    first = 0
    while first < n:
        p = _job([exe, data, first, case_seconds * 1000], w, mem_gib=64,
                 timeout=60 + (n - first) * (case_seconds + 2), env={"RUST_BACKTRACE": "0"})
        started, timeout_of, cur = [], None, None
        for line in _text(p.stdout).splitlines():
            tag, _, rest = line.partition(" ")
            k_s, _, payload = rest.partition(" ")
            if tag not in ("VOSTART", "VOCASE", "VOPANIC", "VOTIMEOUT", "VOBIG") or not k_s.isdigit():
                if line and cur is not None and len(printed.setdefault(cur, [])) < 50:
                    printed[cur].append(line[:500])     # printed by the translation itself
                continue
            k = int(k_s)
            if tag == "VOSTART":
                started.append(k)
                cur = k
            elif tag == "VOCASE":
                res[k] = _exe("outcome", json.loads(payload))
            elif tag == "VOPANIC" and k not in res:
                res[k] = _exe("runtime_error", message="panic: " + json.loads(payload))
            elif tag == "VOTIMEOUT":
                timeout_of = k
                if k not in res:
                    res[k] = _exe("runtime_error", message=f"timeout: the case ran longer than {case_seconds} s",
                                  timeout=True)
            elif tag == "VOBIG":
                res[k] = _exe("runtime_error", message=f"the outcome is larger than {OUTPUT_CAP} bytes")
        hung = [k for k in started if k not in res]
        if hung and timeout_of is None:
            res[hung[0]] = _exe("runtime_error", message=f"the program crashed (exit {p.returncode}): "
                                + _text(p.stderr).strip()[-1500:])
        if not started:
            for k in range(first, n):
                res[k] = _exe("runner_error", message=f"driver failed (exit {p.returncode}): {_text(p.stderr)[-1500:]}")
        first = min([k for k in range(first, n) if k not in res], default=n)
    for k, lines in printed.items():
        res[k]["stdout"] = lines
    for r in res.values():
        if r.get("message"):
            r["message"] = r["message"].replace(f"{w / 'crate'}/", "")
    return [res[k] for k in range(n)]


# -- guided arm: extraction and Lean ------------------------------------------------------------------------------

def _lean_path(w: Path) -> str:
    manifest = json.loads((AENEAS_LEAN / "lake-manifest.json").read_text())
    theirs = {p["name"]: p.get("rev") for p in json.loads((LEAN_PACKAGES.parent.parent / "lake-manifest.json")
                                                          .read_text())["packages"]}
    dirs = []
    for p in manifest["packages"]:
        if theirs.get(p["name"]) != p.get("rev"):
            raise RuntimeError(f"Lean package {p['name']}: equiv-lean has {theirs.get(p['name'])}, Aeneas wants "
                               f"{p.get('rev')}")
        dirs.append(LEAN_PACKAGES / p["name"] / ".lake" / "build" / "lib" / "lean")
    dirs += [AENEAS_LEAN / ".lake" / "build" / "lib" / "lean", w / "build"]
    return ":".join(map(str, dirs))


def _lean(w: Path, src: Path, *, olean: bool, timeout: int) -> subprocess.CompletedProcess:
    cmd = [LEAN_BIN, "-R", w / "gen"]
    if olean:
        out = w / "build" / src.relative_to(w / "gen").with_suffix("")
        out.parent.mkdir(parents=True, exist_ok=True)
        cmd += ["-o", out.with_suffix(".olean"), "-i", out.with_suffix(".ilean")]
    # a large thread stack: evaluated, Aeneas's `loop` recurses once per iteration (no tail calls)
    cmd += ["--json", "-j", "1", "-DElab.async=false", f"--tstack={LEAN_TSTACK_KB}", src]
    return _job(cmd, w, mem_gib=128, timeout=timeout, env={"LEAN_PATH": _lean_path(w), "TMPDIR": w / "tmp"})


def _messages(stdout) -> list[dict]:
    out = []
    for line in _text(stdout).splitlines():
        if line.startswith("{"):
            try:
                out.append(json.loads(line))
            except ValueError:
                pass
    return out


def _rust_source_of(lines: list[str], line: int) -> str:
    """The Rust source span Aeneas noted in the doc comment of the definition around `line` (1-based)."""
    for i in range(min(line, len(lines)) - 1, -1, -1):
        mo = re.search(r"Source: '([^']+)', lines (\S+)", lines[i])
        if mo:
            return f" (Rust source {mo.group(1)}, lines {mo.group(2)})"
    return ""


def _extract(w: Path, m: dict) -> dict | None:
    """Charon + Aeneas, the interface check, and Lean's compilation of the extraction."""
    crate = m["rust_crate"]
    env = {"CARGO_TARGET_DIR": w / "target_charon", "TMPDIR": w / "tmp", "CARGO_TERM_COLOR": "never",
           "NO_COLOR": "1", "CARGO_NET_OFFLINE": "true"}
    p = _job([AENEAS_BIN / "charon", "cargo", "--preset=aeneas", "--", "-j1"], w / "crate", mem_gib=64, timeout=900,
             env=env, core_h=1.5)
    if p.returncode in (124, 137) or b"[job timed out]" in (p.stderr or b""):
        return {"stage": "charon", "harness": True, "message": f"charon killed by the harness (exit {p.returncode})"}
    _save_log(w, "charon", p)
    llbc = w / "crate" / f"{crate}.llbc"
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
        return {"stage": "aeneas", "message": "the crate uses functions or types that Aeneas does not model (keep to "
                "the style guide's code restrictions): " + ", ".join(names[:40])}
    types = (gen / "Types.lean").read_text() if (gen / "Types.lean").exists() else ""
    err = _check_interface(m, types, (gen / "Funs.lean").read_text())
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


def _lean_type(fl: dict) -> str:
    """Aeneas's Lean type of the style guide's Rust type of a field."""
    t = f"Array Std.U8 {fl['len']}#usize" if fl["kind"] == "alnum" else "Std.I64"
    if fl.get("occurs"):
        t = f"Array ({t}) {fl['occurs']}#usize" if " " in t else f"Array {t} {fl['occurs']}#usize"
    return t


def _rust_of_lean(t: str) -> str:
    t = re.sub(r"\bStd\.([IU])(\d+|size)\b", lambda mo: mo.group(1).lower() + mo.group(2), t)
    prev = None
    while prev != t:                    # innermost arrays first: Array (Array u8 2#usize) 5#usize -> [[u8; 2]; 5]
        prev = t
        t = re.sub(r"Array \(([^()]*)\) (\d+)#usize", r"[\1; \2]", t)
        t = re.sub(r"Array ([^\s()]+) (\d+)#usize", r"[\1; \2]", t)
    t = re.sub(r"\bSlice (\S+)", r"&[\1]", t)
    t = re.sub(r"alloc\.vec\.Vec \((.*)\)", r"Vec<\1>", t)
    t = re.sub(r"alloc\.vec\.Vec (\S+)", r"Vec<\1>", t)
    return t.replace("Bool", "bool")


def _structures(types_lean: str) -> dict[str, list[tuple[str, str]]]:
    """structure name -> [(field, type)] of Aeneas's Types.lean (field lines indented 2, continuations deeper)."""
    out, cur = {}, None
    for line in types_lean.splitlines():
        mo = re.match(r"structure (\S+) where\s*$", line)
        if mo:
            cur = out.setdefault(mo.group(1), [])
            continue
        if cur is None:
            continue
        if re.match(r"  \S", line) and " : " in line:
            name, _, ty = line.strip().partition(" : ")
            cur.append((name.strip("«»"), ty.strip()))
        elif line.startswith("    ") and cur:
            cur[-1] = (cur[-1][0], cur[-1][1] + " " + line.strip())
        else:
            cur = None
    return out


def _signature(funs_lean: str, name: str = "run") -> tuple[list[tuple[str, str]], str] | None:
    """([(param, type)], return type) of `def <name>` in Aeneas's Funs.lean."""
    mo = re.search(rf"^def {name}\s(.*?):=", funs_lean, re.S | re.M)
    if not mo:
        return None
    rest = " ".join(mo.group(1).split())
    params = []
    while rest.startswith(("(", "{", "[")):
        depth = 0
        for i, ch in enumerate(rest):
            depth += (ch in "({[") - (ch in ")}]")
            if depth == 0:
                break
        inner, rest = rest[1:i], rest[i + 1:].lstrip()
        pname, _, ty = inner.partition(" : ")
        params.append((pname.strip().strip("«»"), ty.strip()))
    return params, rest[1:].strip() if rest.startswith(":") else rest


def _check_interface(m: dict, types_lean: str, funs_lean: str) -> str | None:
    """The extraction must have the style guide's interface (the proof's field relations rely on it)."""
    structs = _structures(types_lean)
    probs = []
    ins, outs = _records_used(m)
    for name in dict.fromkeys(ins + outs):
        rec = m["records"][name]
        have = structs.get(rec["class"])
        if have is None:
            probs.append(f"no struct {rec['class']} (record {name})")
        elif have != [(fl["rust"], _lean_type(fl)) for fl in rec["fields"]]:
            probs.append(f"struct {rec['class']} has fields " + ", ".join(f"{n}: {_rust_of_lean(t)}" for n, t in have))
    out = structs.get("Output")
    if out is None:
        probs.append("no struct Output")
    else:
        want = {"displays": "alloc.vec.Vec (alloc.vec.Vec Std.U8)", "abended": "Bool"}
        want.update({fld: "alloc.vec.Vec (alloc.vec.Vec Std.U8)" if f.get("varying") else
                     f"alloc.vec.Vec {m['records'][r]['class']}" for _, f, r, fld in _outputs(m)})
        if m.get("return_code"):
            want["return_code"] = "Std.I64"
        if any(dict(out).get(f) != t for f, t in want.items()):
            probs.append("struct Output has fields " + ", ".join(f"{n}: {_rust_of_lean(t)}" for n, t in out))
    want_params = [(f["rust_param"], f"Slice {m['records'][f['record']]['class']}") for f in _inputs(m)]
    want_params += [(lk["rust_param"], m["records"][lk["record"]]["class"] if "record" in lk else
                     _lean_type(lk["field"])) for lk in _linkage(m)]
    want_params += [("clock", "Array Std.U8 21#usize")] if m["clock"] else []
    sig = _signature(funs_lean)
    if sig is None:
        probs.append("no function run")
    elif sig != (want_params, "Result Output"):
        ps = ", ".join(f"{n}: {_rust_of_lean(t)}" for n, t in sig[0])
        probs.append(f"run is fn run({ps}) -> {_rust_of_lean(sig[1].removeprefix('Result '))}")
    if not probs:
        return None
    return ("the crate does not have the interface of styleguide_rust.md. Expected:\n" + _expected_interface(m)
            + "\n\nbut " + ";\n".join(probs))


_LEAN_PRELUDE = r'''import Aeneas
import %(mod)s.Funs
open Aeneas Aeneas.Std

namespace VoEval

def mkI {ty : IScalarTy} (v : Int) : IScalar ty := ⟨BitVec.ofInt ty.numBits v⟩

/-- The bytes of a string of Latin-1 characters (lengths are checked before the module is generated). -/
def arr {n : Std.Usize} (s : String) : Array Std.U8 n :=
  let l : List Std.U8 := s.toList.map fun c => ⟨BitVec.ofNat 8 c.toNat⟩
  if h : l.length = n.val then Array.make n l h else Array.repeat n ⟨BitVec.ofNat 8 0⟩

/-- An array of `k` elements from a list (an OCCURS field; lengths are checked before the module is generated). -/
def arrOf {α : Type} {k : Std.Usize} (d : α) (l : List α) : Array α k :=
  if h : l.length = k.val then Array.make k l h else Array.repeat k d

def slice {α : Type} (l : List α) : Slice α :=
  if h : l.length ≤ Usize.max then Slice.from l h else Slice.new α

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def jchar (n : Nat) : String :=
  if n == 34 then "\\\"" else if n == 92 then "\\\\"
  else if n < 32 || n ≥ 127 then "\\u00" ++ (hexDigit (n / 16)).toString ++ (hexDigit (n %% 16)).toString
  else (Char.ofNat n).toString

def jbytes (l : List Std.U8) : String := "\"" ++ String.join (l.map fun b => jchar b.val) ++ "\""

def jlist {α : Type} (l : List α) (f : α → String) : String := "[" ++ String.intercalate ", " (l.map f) ++ "]"

def jobj (fields : List String) : String := "{" ++ String.intercalate ", " fields ++ "}"

partial def waitTask (t : Task String) (start limit : Nat) : IO (Option String) := do
  if ← IO.hasFinished t then return some t.get
  if (← IO.monoMsNow) - start > limit then return none
  IO.sleep 20
  waitTask t start limit

/-- Results go to a file, flushed line by line: messages on stdout are lost when the process dies. -/
def emit (path line : String) : IO Unit := do
  let h ← IO.FS.Handle.mk path .append
  h.putStrLn line
  h.flush

/-- Evaluate one case on a dedicated thread; past the time limit, end the process (the runner restarts after
the case). -/
def evalCase (path : String) (k limit : Nat) (f : Unit → String) : IO Unit := do
  emit path s!"VOSTART {k}"
  let start ← IO.monoMsNow
  let t := Task.spawn f .dedicated
  match ← waitTask t start limit with
  | some s => emit path s
  | none => emit path s!"VOTIMEOUT {k}"; IO.Process.exit 3
'''


def _lean_str(s: str) -> str:
    out = []
    for ch in s:
        o = ord(ch)
        out.append('\\"' if ch == '"' else "\\\\" if ch == "\\" else ch if 0x20 <= o < 0x7F else f"\\x{o:02x}")
    return '"' + "".join(out) + '"'


def _lean_value(fl: dict, v) -> str:
    """A field's value as an argument of its `mk_` function: String / Int, or a list of them for OCCURS."""
    one = (lambda x: _lean_str(x)) if fl["kind"] == "alnum" else (lambda x: f"({x})")
    return f"[{', '.join(one(x) for x in v)}]" if fl.get("occurs") else one(v)


def _lean_arg_type(fl: dict) -> str:
    t = "String" if fl["kind"] == "alnum" else "Int"
    return f"(List {t})" if fl.get("occurs") else t


def _lean_conv(fl: dict, a: str, ns: str = "") -> str:
    """The Lean term turning the value `a` (see _lean_value) into the field's Aeneas value (`ns`: the helpers'
    namespace prefix outside `VoEval`)."""
    if fl.get("occurs"):
        return (f'{ns}arrOf ({ns}arr "") ({a}.map {ns}arr)' if fl["kind"] == "alnum" else
                f"{ns}arrOf ({ns}mkI 0) ({a}.map {ns}mkI)")
    return f"{ns}arr {a}" if fl["kind"] == "alnum" else f"{ns}mkI {a}"


def _lean_json(fl: dict, place: str) -> str:
    """The Lean term printing a field's value as JSON (a list for OCCURS)."""
    if fl.get("occurs"):
        return (f"jlist {place}.val (fun x => jbytes x.val)" if fl["kind"] == "alnum" else
                f"jlist {place}.val (fun x => toString x.val)")
    return f"jbytes {place}.val" if fl["kind"] == "alnum" else f"toString {place}.val"


def _lean_module(m: dict, cases: list[tuple[int, dict]], limit_ms: int, out: Path) -> tuple[str, dict[int, int]]:
    """The evaluation module for `cases` [(index, case)], writing results to `out`, and the line of each case's
    #eval."""
    crate, recs = m["rust_crate"], m["records"]
    ins, outs = _records_used(m)
    parts = [_LEAN_PRELUDE % {"mod": MOD}]
    for name in ins:
        rec = recs[name]
        args = " ".join(f"(a{i} : {_lean_arg_type(fl)})" for i, fl in enumerate(rec["fields"]))
        inits = ", ".join(f"{fl['rust']} := {_lean_conv(fl, f'a{i}')}" for i, fl in enumerate(rec["fields"]))
        parts.append(f"def mk_{_ident(name)} {args} : {crate}.{rec['class']} :=\n  {{ {inits} }}\n")
    for name in outs:
        rec = recs[name]
        fields = ", ".join(_lean_str(f'"{fl["cobol"]}": ') + " ++ " + _lean_json(fl, f"r.{fl['rust']}")
                           for fl in rec["fields"])
        parts.append(f"def js_{_ident(name)} (r : {crate}.{rec['class']}) : String :=\n  jobj [{fields}]\n")
    groups = []
    for kind in ("writes", "rewrites"):
        items = [f"(if o.{fld}.val.isEmpty then [] else [{_lean_str(chr(34) + f['fd'] + chr(34) + ': ')} ++ "
                 + (f"jlist o.{fld}.val (fun v => jobj [{_lean_str(chr(34) + r + chr(34) + ': ')} ++ jbytes v.val])])"
                    if f.get("varying") else f"jlist o.{fld}.val js_{_ident(r)}])")
                 for k, f, r, fld in _outputs(m) if k == kind]
        groups.append(f'"\\"{kind}\\": " ++ jobj ({" ++ ".join(items + ["([] : List String)"])})')
    rc = "toString o.return_code.val" if m.get("return_code") else '"null"'
    parts.append(
        f"def js_out (o : {crate}.Output) : String :=\n  jobj [\n"
        f'    "\\"end\\": " ++ (if o.abended then "\\"abend\\"" else "\\"normal\\""),\n'
        f'    "\\"displays\\": " ++ jlist o.displays.val (fun v => jbytes v.val),\n'
        f"    {groups[0]},\n    {groups[1]},\n"
        f'    "\\"return_code\\": " ++ {rc}]\n')
    parts.append(
        f"def res (k : Nat) (r : Result {crate}.Output) : String :=\n  match r.match with\n"
        f'  | .ok o => "VORES " ++ toString k ++ " ok " ++ js_out o\n'
        f'  | .div => "VORES " ++ toString k ++ " div"\n'
        f'  | .vis (.fail e) _ => "VORES " ++ toString k ++ " fail " ++ reprStr e\n')
    parts.append("end VoEval\n")
    evals = []
    for k, case in cases:
        args = []
        for f in _inputs(m):
            rec = recs[f["record"]]
            items = [f"VoEval.mk_{_ident(f['record'])} " + " ".join(_lean_value(fl, r[fl["cobol"]])
                                                                       for fl in rec["fields"])
                     for r in _case_records(case, f)]
            args.append(f"(VoEval.slice [{', '.join(items)}])")
        for lk in _linkage(m):
            v = case["linkage"][lk["name"]]
            if "record" in lk:
                args.append(f"(VoEval.mk_{_ident(lk['record'])} "
                            + " ".join(_lean_value(fl, v[fl["cobol"]]) for fl in recs[lk["record"]]["fields"]) + ")")
            else:
                args.append(f"({_lean_conv(lk['field'], _lean_value(lk['field'], v), 'VoEval.')})")
        if m["clock"]:
            args.append(f"(VoEval.arr {_lean_str(case['clock'])})")
        evals.append(f"#eval VoEval.evalCase {_lean_str(str(out))} {k} {limit_ms} fun _ => "
                     f"VoEval.res {k} ({crate}.run {' '.join(args)})")
    text = "\n".join(parts) + "\n" + "\n".join(evals) + "\n"
    at = [i + 1 for i, line in enumerate(text.splitlines()) if line.startswith("#eval ")]
    return text, {k: line for (k, _), line in zip(cases, at)}


def _lean_batch(w: Path, m: dict, cases: list[dict], skip: set[int], lean_seconds: int) -> list[dict]:
    """Evaluate the extracted `run` on the cases in one Lean process. A case that crashes Lean or passes the time
    limit is a runtime error, and the evaluation restarts after it."""
    n = len(cases)
    res = {k: _exe("skipped", message="not evaluated: the native run timed out") for k in skip}
    todo = [k for k in range(n) if k not in res]
    rnd = 0
    while todo:
        src = w / "gen" / MOD / f"Eval{rnd}.lean"
        out = w / "batch" / f"lean{rnd}.txt"
        out.parent.mkdir(exist_ok=True)
        out.write_text("")
        text, at = _lean_module(m, [(k, cases[k]) for k in todo], lean_seconds * 1000, out)
        src.write_text(text)
        p = _lean(w, src, olean=False, timeout=600 + len(todo) * (lean_seconds + 5))
        _save_log(w, f"lean_eval{rnd}", p)
        started, new = [], 0
        for line in out.read_text().splitlines():
            mo = re.match(r"(VOSTART|VORES|VOTIMEOUT) (\d+) ?(ok|div|fail)? ?(.*)", line)
            if not mo:
                continue
            k, tag = int(mo.group(2)), mo.group(1)
            if tag == "VOSTART":
                started.append(k)
            elif tag == "VOTIMEOUT":
                res[k] = _exe("runtime_error", message=f"timeout: the Lean evaluation of the case ran longer than "
                              f"{lean_seconds} s", timeout=True)
            else:
                res[k] = (_exe("outcome", json.loads(mo.group(4))) if mo.group(3) == "ok" else
                          _exe("runtime_error", message="Aeneas: diverges") if mo.group(3) == "div" else
                          _exe("runtime_error", message="Aeneas: fail " + mo.group(4).strip()))
            new += tag != "VOSTART"
        case_at = {line: k for k, line in at.items()}
        for d in _messages(p.stdout):
            if d.get("severity") != "error":
                continue
            k = case_at.get((d.get("pos") or {}).get("line"))
            if k is None:           # the generated module itself is wrong: a runner bug
                raise RuntimeError(f"Lean evaluation module {src} does not elaborate: {d.get('data', '')[:2000]}")
            if k not in res:
                res[k], new = _exe("runner_error", message="Lean: " + d.get("data", "")[:1500]), new + 1
        hung = [k for k in started if k not in res]
        tail = (_text(p.stderr) + _text(p.stdout))[-1500:]
        if hung:
            res[hung[0]] = _exe("runtime_error", message=f"the Lean evaluation crashed (exit {p.returncode}): {tail}",
                                timeout=p.returncode in (124, 137))
        elif not new:               # Lean failed without starting a case: not the translation's fault
            for k in todo:
                res.setdefault(k, _exe("runner_error", message=f"Lean evaluation fails (exit {p.returncode}): {tail}"))
        todo = [k for k in todo if k not in res]
        rnd += 1
    return [res[k] for k in range(n)]


def run_guided_batch(trans_dir, cases: list, mapping, *, work_dir=None, case_seconds: int = CASE_SECONDS,
                     lean_seconds: int = LEAN_CASE_SECONDS, lean: bool = True) -> list[dict]:
    """Run the guided arm's crate on every case, natively and as Aeneas's extraction in Lean (see module doc)."""
    m = _load(mapping)
    cases = [_load(c) for c in cases]
    for c in cases:
        _check_case(m, c)
    w = _workdir("guided", Path(trans_dir), m, work_dir)
    with _locked(w / "lock"):
        key = hashlib.sha256(json.dumps([cases, case_seconds, lean_seconds, lean], sort_keys=True).encode())
        cache = w / "results" / f"{key.hexdigest()[:20]}.json"
        if cache.exists():                      # `run` is pure: same version and cases, same results
            return json.loads(cache.read_text())
        err = (_once(w, "native_build", lambda: _native_build(w, Path(trans_dir), m))
               or (_once(w, "extract", lambda: _extract(w, m)) if lean else None))
        if err:
            return _compile_error(err)
        native = _native_batch(w, m, cases, case_seconds)
        if lean:
            skip = {k for k, r in enumerate(native) if r.get("timeout")}
            out = [_result(a, b) for a, b in zip(native, _lean_batch(w, m, cases, skip, lean_seconds))]
        else:
            out = [_result(a) for a in native]
        if not any("not_run" in r or r["executions"]["native"].get("status") == "runner_error" for r in out):
            cache.parent.mkdir(exist_ok=True)
            cache.write_text(json.dumps(out))
        return out


def run_guided(trans_dir, case, mapping, **kw) -> dict:
    return run_guided_batch(trans_dir, [case], mapping, **kw)[0]


# -- naive arm ----------------------------------------------------------------------------------------------------

def _zoned_text(fl: dict, v: int) -> str:
    """A zoned DISPLAY numeric as text: the CP037 reading of its EBCDIC bytes (overpunch C0..C9 / D0..D9)."""
    if fl.get("usage", "display") != "display":
        raise NotImplementedError(f"{fl['cobol']}: {fl['usage']} numeric in a record")
    ds = str(abs(v)).rjust(fl["digits"], "0")
    if not fl["signed"]:
        return ds
    if fl.get("sign_separate"):
        sign = "-" if v < 0 else "+"
        return sign + ds if fl.get("sign_leading") else ds + sign
    i = 0 if fl.get("sign_leading") else len(ds) - 1
    return ds[:i] + ("}JKLMNOPQR" if v < 0 else "{ABCDEFGHI")[int(ds[i])] + ds[i + 1:]


def _image(rec: dict, values: dict) -> str:
    out = [" "] * rec["size"]
    for fl in rec["fields"]:
        v = values[fl["cobol"]]
        for i, x in enumerate(v if fl.get("occurs") else [v]):
            t = x if fl["kind"] == "alnum" else _zoned_text(fl, x)
            if len(t) != fl["len"]:
                raise ValueError(f"{fl['cobol']}: {len(t)} characters for a field of {fl['len']}")
            o = fl["offset"] + i * fl.get("stride", 0)
            out[o:o + fl["len"]] = list(t)
    return "".join(out)


def _lines(data: bytes) -> list[str]:
    """Text lines of a program's output: UTF-8, or Latin-1 where a line is not UTF-8; CR LF counts as LF."""
    parts = data.split(b"\n")
    if parts and parts[-1] == b"":
        parts.pop()
    out = []
    for b in parts:
        b = b[:-1] if b.endswith(b"\r") else b
        try:
            out.append(b.decode("utf-8"))
        except UnicodeDecodeError:
            out.append(b.decode("latin-1"))
    return out


def _decode_line(rec: dict, line: str) -> dict:
    from .cobol import decode_record     # the COBOL side's decoding, so both outcomes read records alike
    return decode_record(rec, list(line.encode("cp037", "replace")))


def _file_diff(before: list[str], final: list[str], size: int, key_span) -> tuple[list[str], list[str]]:
    """The records of `final` that are new and those that changed, in file order: by record key for an indexed
    file, by position otherwise (line-sequential writers may drop trailing spaces)."""
    before = [l.ljust(size) for l in before]
    final = [l.ljust(size) for l in final]
    if key_span:
        o, n = key_span
        old = {l[o:o + n]: l for l in before}
        return ([l for l in final if l[o:o + n] not in old],
                [l for l in final if l[o:o + n] in old and l != old[l[o:o + n]]])
    return final[len(before):], [l for l, b in zip(final, before) if l != b]


def _naive_build(w: Path, trans_dir: Path, m: dict) -> dict | None:
    err = _prepare_crate(trans_dir, m, "bin", w / "crate")
    if err:
        return err
    p = _cargo_build(w, w / "crate", "cargo_bin")
    if p.returncode != 0:
        return {"stage": "cargo", "message": _cargo_errors(p.stderr)}
    return None


# runs every case of a batch in one run1.sh job: the program in its case directory, with a per-case time limit
# and a cap on the size of every file it writes (stdout goes to a file, so the cap covers it too)
_NAIVE_EXEC = r"""
import json, os, resource, subprocess, sys, time
spec = json.load(open(sys.argv[1]))
def limits():
    resource.setrlimit(resource.RLIMIT_FSIZE, (spec["fsize"], spec["fsize"]))
res = []
for c in spec["cases"]:
    d = c["dir"]
    t0 = time.time()
    with open(os.path.join(d, ".vo_stdout"), "wb") as so, open(os.path.join(d, ".vo_stderr"), "wb") as se:
        try:
            p = subprocess.run([spec["binary"]] + c["args"], cwd=d, stdin=subprocess.DEVNULL, stdout=so, stderr=se,
                               timeout=spec["timeout"], preexec_fn=limits,
                               env=dict(spec["env"], HOME=d, TMPDIR=d, **c["env"]))
            rc, to = p.returncode, False
        except subprocess.TimeoutExpired:
            rc, to = None, True
    res.append({"rc": rc, "timeout": to, "seconds": round(time.time() - t0, 3)})
json.dump(res, open(sys.argv[2], "w"))
"""


def _naive_outcome(m: dict, case: dict, d: Path, status: int) -> tuple[dict, dict]:
    """The canonical outcome of a naive run that ended normally or abended, and the written files as it left them."""
    displays = _lines((d / ".vo_stdout").read_bytes()[:OUTPUT_CAP])
    writes, rewrites, after = {}, {}, {}
    for f in m["files"]:
        wf, rf = f.get("write_from"), f.get("rewrite_from")
        path = d / f["assign"]
        if not (wf or rf) or not path.is_file():
            continue
        final = _lines(path.read_bytes()[:OUTPUT_CAP])
        # decoded like loop.py's naive view reads them back: by the record the program REWRITEs or WRITEs FROM
        after[f["fd"]] = [_decode_line(m["records"][rf or wf], l) for l in final]
        if not f["input"]:                  # OPEN OUTPUT: every record in the file was written by this run
            new, changed = final, []
        else:
            before = [_image(m["records"][f["record"]], r) for r in _case_records(case, f)]
            new, changed = _file_diff(before, final, m["records"][f["record"]]["size"], f.get("key_span"))
        if wf and new:
            writes[f["fd"]] = [_decode_line(m["records"][wf], l) for l in new]
        if rf and changed:
            rewrites[f["fd"]] = [_decode_line(m["records"][rf], l) for l in changed]
    abend = status == ABEND_STATUS
    out = {"end": "abend" if abend else "normal", "displays": displays, "writes": writes, "rewrites": rewrites,
           "return_code": status if m.get("return_code") and not abend else None}
    return out, after


def _parm_text(m: dict, case: dict) -> list[str]:
    """argv for a program with PROCEDURE DIVISION USING: the text fields of the linkage items, joined."""
    if not _linkage(m):
        return []
    text = ""
    for lk in _linkage(m):
        v = case["linkage"][lk["name"]]
        if "record" in lk:
            text += "".join(v[fl["cobol"]] for fl in m["records"][lk["record"]]["fields"] if fl["kind"] == "alnum")
        elif lk["field"]["kind"] == "alnum":
            text += v
    return [text]


def run_naive_batch(trans_dir, cases: list, mapping, *, work_dir=None, case_seconds: int = CASE_SECONDS) -> list[dict]:
    """Run the naive arm's binary on every case, each in its own directory (see module doc)."""
    m = _load(mapping)
    cases = [_load(c) for c in cases]
    for c in cases:
        _check_case(m, c)
    w = _workdir("naive", Path(trans_dir), m, work_dir)
    with _locked(w / "lock"):
        err = _once(w, "native_build", lambda: _naive_build(w, Path(trans_dir), m))
        if err:
            return _compile_error(err)
        b = w / "batches" / str(time.time_ns())
        specs, res = [], {}
        for k, case in enumerate(cases):
            d = b / f"c{k}"
            d.mkdir(parents=True)
            for f in _inputs(m):
                lines = [_image(m["records"][f["record"]], r) for r in _case_records(case, f)]
                if any("\n" in l or "\r" in l for l in lines):
                    res[k] = _exe("runner_error", message=f"{f['fd']}: a record holds a line break, which a "
                                  "line-sequential file cannot carry")
                (d / f["assign"]).write_text("".join(l + "\n" for l in lines), encoding="utf-8")
            specs.append({"dir": str(d), "args": _parm_text(m, case),
                          "env": {"COBOL_CURRENT_DATE": case["clock"]} if m["clock"] else {}})
        (b / "exec.py").write_text(_NAIVE_EXEC)
        (b / "spec.json").write_text(json.dumps({
            "binary": str(w / "target" / "debug" / m["rust_crate"]), "cases": specs, "timeout": case_seconds,
            "fsize": OUTPUT_CAP, "env": {"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8", "RUST_BACKTRACE": "0"}}))
        p = _job([sys.executable, "-I", "-B", b / "exec.py", b / "spec.json", b / "runs.json"], b, mem_gib=64,
                 timeout=60 + len(cases) * (case_seconds + 2))
        _save_log(w, "naive_exec", p)
        if not (b / "runs.json").exists():
            return [_result(_exe("runner_error", message=f"naive executor failed (exit {p.returncode}): "
                                 + _text(p.stderr)[-1500:])) for _ in cases]
        out = []
        for k, (case, r) in enumerate(zip(cases, json.loads((b / "runs.json").read_text()))):
            d = b / f"c{k}"
            err_text = _text((d / ".vo_stderr").read_bytes()[-4000:]).strip()[-1500:]
            status = r["rc"]
            if k in res:
                ex = res[k]
            elif r["timeout"]:
                ex = _exe("runtime_error", message=f"timeout: the program ran longer than {case_seconds} s",
                          timeout=True)
            elif status < 0:
                ex = _exe("runtime_error", message=f"killed by signal {-status}: {err_text}")
            elif status == 101:
                ex = _exe("runtime_error", message="panic: " + err_text)
            elif status in (0, ABEND_STATUS) or m.get("return_code"):
                outcome, after = _naive_outcome(m, case, d, status)
                out.append(dict(_result(_exe("outcome", outcome)), files_after=after))
                continue
            else:
                ex = _exe("runtime_error", message=f"exit status {status}: {err_text}")
            out.append(_result(ex))
        return out


def run_naive(trans_dir, case, mapping, **kw) -> dict:
    return run_naive_batch(trans_dir, [case], mapping, **kw)[0]


def main(argv: list[str]) -> int:
    """python -m veriforch.modernize.rustrun guided|naive <trans_dir> <mapping.json> <case.json>..."""
    if len(argv) < 4 or argv[0] not in ("guided", "naive"):
        print(main.__doc__, file=sys.stderr)
        return 2
    fn = run_guided_batch if argv[0] == "guided" else run_naive_batch
    print(json.dumps(fn(argv[1], argv[3:], argv[2]), indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
