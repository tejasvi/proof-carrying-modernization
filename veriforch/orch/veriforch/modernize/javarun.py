"""Java runner for item A, certified modernization of CardDemo batch programs (INTERFACES.md, "Runner contract").

Every entry point takes the translation directory, test-case JSON dicts and the mapping (the dict of
runs/modernize/<PROG>/mapping.json, written by mapping.py):
* `run_guided_batch(trans_dir, cases, mapping)`, `run_guided(trans_dir, case, mapping)`: the translation
  `trans_dir/java/<java_class>.java` follows styleguide_java.md. Per case, a driver class generated from the mapping
  builds the input records from the case's field values, calls `<java_class>.run` and turns the Result into the
  outcome JSON (COBOL field names): an OCCURS field is an array (a JSON list), and the writes of a variable-length
  file (RECORD IS VARYING) are the records' texts, `{<write_from record>: text}` as in cobol.py. Every case runs
  twice: on the JVM, and on JimpleLean's interpreter over the Jimple that Soot makes of the same class files.
* `run_naive_batch(trans_dir, cases, mapping)`, `run_naive(trans_dir, case, mapping)`: the program follows only the
  naive I/O contract (INTERFACES.md): main class `<java_class>` in the default package; each input file under its
  ASSIGN name in the working directory, as UTF-8 text with one record image per line (copybook layout, every EBCDIC
  byte as its CP037 character: zoned digits, a signed field's overpunched last digit `{`, `A`-`I` positive, `}`,
  `J`-`R` negative, or a separate `+`/`-` for SIGN SEPARATE); the clock in the environment variable
  COBOL_CURRENT_DATE; the text fields of the USING record joined as the first argument (the JCL PARM). Stdout lines
  are the displays, the files the program leaves under the ASSIGN names of its output files the writes, exit status
  999 (231 as a POSIX status) an abend, and, when the program sets RETURN-CODE, the exit status the return code.
  A line-sequential file keeps no REWRITE log: the rewrites of an I-O file are the records that differ from the
  input, in file order (`notes` says so). JVM only.

Results follow loop.py: a version that does not build gives ONE element, {"status": "compile_error", "message":
the tool's own text, "stage": "javac" | "driver" | "soot" | "jimple-import" | "setup"}; "driver" means javac
rejected the generated driver, i.e. the translation lacks the style guide's interface (names, field types,
constructors). Otherwise there is one element per case, in order:
    {"executions": {"jvm": R, "jimple": R}, "produced_by": [...], "agree": bool | None, "disagreement": str | None}
with R = {"outcome": <canonical outcome>, "stdout": what the translation printed itself} or {"status":
"runtime_error", "message": ..., "timeout": bool, "stuck": bool, "stdout": ...}. `stuck` is JimpleLean's interpreter
going `wrong` (e.g. an unmodelled library call such as String.format). `produced_by` lists the executions that gave
the JVM's result, `agree` says whether the interpreter did, and `disagreement` locates the first difference. A case
whose JVM run hits the time limit is not interpreted ("skipped"). Naive cases have only "jvm" (with the exit status
`rc`), plus `notes` and `files_after` (every written or rewritten file as the program left it).

A batch makes one javac and one Soot run for the translation (cached in `work_dir` by the hash of its sources), one
of each for all the drivers, ONE JVM for all cases (each case in a fresh class loader, so static fields start over,
and in its own thread with a time limit) and ONE interpreter process: `vo-jbatch`, built once from the pinned
JimpleLean, calls `runMain` for every case from the initial state, which is what `jimple-run DIRS CLASS` does, and
prints each result as soon as it has it. A process that ends early (time limit, crash) is started again after the
case it was on. The naive arm runs every case in its own JVM and working directory, all inside one run1.sh job.

Every javac, Soot, JVM and Lean job goes through scripts/run1.sh. Work files go to `work_dir` (default
`<trans_dir>/javarun`).
"""
from __future__ import annotations

import fcntl
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import uuid
from pathlib import Path

from ..adapters.jimple.build import JDK, JFLAGS, JIMPLELEAN, SOOT
from ..lean import LEAN_BIN, RUN1, VO_ROOT, kill_session

TMP = VO_ROOT / "scratch" / "tmp"          # run1.sh's TMPDIR: the JVM ignores TMPDIR, so it gets java.io.tmpdir
CACHE = Path(os.environ.get("VO_JAVARUN_CACHE", str(VO_ROOT / "runs" / "javarun_cache")))
MARK = "@@VO-JAVARUN-OUTCOME@@"
ABEND_STATUS = (999, 999 % 256)
CHUNK = 40                                 # input records per driver method (a method's bytecode is at most 64 KiB)
JAVAC = [str(JDK / "javac"), *("-J" + f for f in JFLAGS), f"-J-Djava.io.tmpdir={TMP}", "--release", "17",
         "-proc:none", "-g", "-encoding", "UTF-8", "-nowarn", "-Xmaxerrs", "30"]
JAVA = [str(JDK / "java"), *JFLAGS, f"-Djava.io.tmpdir={TMP}"]
JAVA_RUN = [*JAVA, "-XX:TieredStopAtLevel=1"]
JAVA_NAIVE = [*JAVA_RUN, "-Dfile.encoding=UTF-8", "-Dsun.stdout.encoding=UTF-8", "-Dsun.stderr.encoding=UTF-8"]
# translations run with an empty environment (no API keys or tokens for model-written code to read)
CLEAN_ENV = ["env", "-i", "PATH=/usr/bin:/bin", "LC_ALL=C.UTF-8", f"TMPDIR={TMP}"]
_POS, _NEG = "{ABCDEFGHI", "}JKLMNOPQR"    # CP037 text of the zoned digits 0-9 with a C (+) and a D (-) zone


# ---------------------------------------------------------------------------------------------------------------
# jobs


def _run1(cmd: list[str], cwd: Path, timeout: int, mem: int, log: Path) -> tuple[int, bytes, bytes]:
    """One job under scripts/run1.sh (time limit, address-space cap in GiB, core-hour guard), in its own session,
    killed whole if run1.sh itself overruns. Returns (exit code, stdout, stderr); 124 is the time limit."""
    core_h = round((1.5 * timeout + 60) / 3600, 4)
    full = [str(RUN1), "-t", str(timeout), "-m", str(mem), "-c", str(core_h), "-l", str(log), "--", *cmd]
    proc = subprocess.Popen(full, cwd=cwd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            env=dict(os.environ, VO_ROOT=str(VO_ROOT)), start_new_session=True)
    try:
        out, err = proc.communicate(timeout=timeout + 180)
        return proc.returncode, out, err
    except subprocess.TimeoutExpired:
        kill_session(proc.pid)
        try:
            out, err = proc.communicate(timeout=30)
        except subprocess.TimeoutExpired:
            out, err = b"", b""
        return 124, out or b"", err or b""


def _tail(b: bytes, n: int = 4000) -> str:
    s = b.decode("utf-8", "replace").strip()
    return s if len(s) <= n else "...\n" + s[-n:]


def _rmtree_own(p: Path, parent: Path, prefixes: tuple[str, ...]) -> None:
    """Delete a directory this module made: a direct child of `parent` whose name has one of `prefixes`."""
    if p.is_symlink() or p.resolve().parent != parent.resolve() or not p.name.startswith(prefixes):
        raise RuntimeError(f"javarun: refusing to delete {p}")
    shutil.rmtree(p)


def _soot(proc_dir: Path, cp: str, out: Path, cwd: Path, log: Path) -> str | None:
    """Jimple of the classes in `proc_dir` into `out` (classes on `cp` resolve); the error text, or None."""
    rc, o, e = _run1([*JAVA, "-cp", str(SOOT), "soot.Main", "-pp", "-allow-phantom-refs", "-cp", cp,
                      "-process-dir", str(proc_dir), "-f", "J", "-d", str(out)], cwd, 300, 64, log)
    if rc != 0 or not any(out.glob("*.jimple")):
        lines = [ln for ln in (o + e).decode("utf-8", "replace").splitlines() if len(ln) < 400]   # not its issue URL
        return f"Soot could not turn the class files into Jimple (exit {rc}):\n" + "\n".join(lines[-40:])
    return None


# ---------------------------------------------------------------------------------------------------------------
# vo-jbatch: JimpleLean's interpreter over many main classes in one process

JB_LEAN = r'''/-
  Generated by veriforch (modernize/javarun.py): `vo-jbatch`, the batch form of JimpleLean's `jimple-run`.

    vo-jbatch DIRS FUEL CLASS...

  Parses the `*.jimple` files of `DIRS` (`:`-separated, each in file-name order) once, as `jimple-run` does, then
  runs `CLASS.main(new String[0])` for every CLASS with `runMain` from the initial state (empty heap, no class
  initialized): each run is the one `jimple-run DIRS CLASS --fuel FUEL` makes. Per run it prints and flushes the
  frame `@@VO-JB <i> <status> <output bytes> <message bytes>`, a newline, the output, the message and a newline;
  status is normal, exc (uncaught exception), wrong (stuck) or fuel (out of fuel). Exit code 2: bad usage or a
  parse error.
-/
import Jimple.Parser
import Jimple.Interp

open Jimple

def voLoad (dirs : List System.FilePath) : IO (Except String Program) := do
  let mut cs : Array ClassDecl := #[]
  for dir in dirs do
    let es ← dir.readDir
    let fs := (es.filter (·.fileName.endsWith ".jimple")).qsort (·.fileName < ·.fileName)
    for e in fs do
      match Parser.parseClass (← IO.FS.readFile e.path) with
      | .ok c => cs := cs.push c
      | .error msg => return .error s!"{e.path}: {msg}"
  return .ok { classes := cs.toList }

/-- `java.lang.Foo: message`, as `jimple-run` (and the JVM) print an uncaught exception. -/
def voExcText (σ : State) (e : Addr) : String :=
  match σ.heap e with
  | some (.plain c fs) =>
    match Fields.get fs ("java.lang.Throwable", "detailMessage") with
    | some m => match strOf σ m with
      | some s => s!"{c}: {JStr.toLean s}"
      | none => c
    | none => c
  | some o => match o.ty with
    | .cls c => c
    | _ => "?"
  | none => "?"

def voFrame (i : Nat) (status out msg : String) : String :=
  s!"@@VO-JB {i} {status} {out.utf8ByteSize} {msg.utf8ByteSize}\n{out}{msg}\n"

def main (args : List String) : IO UInt32 := do
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  match args with
  | dir :: fuelArg :: classes =>
    let some fuel := fuelArg.toNat? | stderr.putStrLn "vo-jbatch: FUEL must be a number"; return 2
    match ← voLoad ((dir.splitOn ":").map System.FilePath.mk) with
    | .error msg =>
      stderr.putStrLn s!"vo-jbatch: parse error: {msg}"
      return 2
    | .ok P =>
      let mut i := 0
      for cls in classes do
        let f := match runMain P cls fuel with
          | some (.normal _ σ) => voFrame i "normal" (JStr.toLean σ.out) ""
          | some (.exc e σ) => voFrame i "exc" (JStr.toLean σ.out) s!"Exception in thread \"main\" {voExcText σ e}"
          | some (.wrong m) => voFrame i "wrong" "" s!"{m}"
          | none => voFrame i "fuel" "" s!"out of fuel ({fuel} steps)"
        stdout.putStr f
        stdout.flush
        i := i + 1
      return 0
  | _ =>
    stderr.putStrLn "usage: vo-jbatch DIRS FUEL CLASS..."
    return 2
'''

JB_LAKEFILE = '''name = "vo_jbatch"
version = "0.1.0"
defaultTargets = ["vo-jbatch"]

[[require]]
name = "JimpleLean"
path = "{jimplelean}"

[[lean_exe]]
name = "vo-jbatch"
root = "VoJBatch"
moreLeanArgs = ["-DElab.async=false"]
'''


def jbatch() -> Path:
    """`vo-jbatch`, built once per JimpleLean pin into CACHE (a Lean package requiring the pinned JimpleLean by
    path; the pin's compiled modules are reused, only VoJBatch.lean is compiled and linked)."""
    lakefile = JB_LAKEFILE.format(jimplelean=JIMPLELEAN)
    toolchain = (JIMPLELEAN / "lean-toolchain").read_text()
    d = CACHE / f"jbatch-{hashlib.sha256((JB_LEAN + lakefile + toolchain).encode()).hexdigest()[:12]}"
    exe = d / ".lake" / "build" / "bin" / "vo-jbatch"
    if exe.is_file():
        return exe
    CACHE.mkdir(parents=True, exist_ok=True)
    with open(CACHE / "jbatch.lock", "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if not exe.is_file():
            d.mkdir(parents=True, exist_ok=True)
            (d / "VoJBatch.lean").write_text(JB_LEAN)
            (d / "lakefile.toml").write_text(lakefile)
            (d / "lean-toolchain").write_text(toolchain)
            rc, o, e = _run1([str(LEAN_BIN.parent / "lake"), "build", "vo-jbatch"], d, 1800, 128, CACHE / "guard.log")
            if rc != 0 or not exe.is_file():
                raise RuntimeError(f"javarun: building vo-jbatch failed (exit {rc}):\n{_tail(o + e)}")
    return exe


# ---------------------------------------------------------------------------------------------------------------
# cases and the mapping


def _check(fd: dict, v, where: str) -> None:
    if fd.get("occurs"):
        if not isinstance(v, list) or len(v) != fd["occurs"]:
            raise ValueError(f"{where}: needs a list of {fd['occurs']} values, got {v!r}")
        for j, x in enumerate(v):
            _check({**fd, "occurs": None}, x, f"{where}[{j}]")
        return
    if fd["kind"] == "alnum":
        ok = isinstance(v, str) and len(v) == fd["len"] and all(ord(c) < 0x100 for c in v)
        need = f"a string of {fd['len']} characters in U+0000..U+00FF"
    else:
        ok = (isinstance(v, int) and not isinstance(v, bool) and abs(v) < 10 ** fd["digits"]
              and (v >= 0 or fd["signed"]))
        need = f"an integer of at most {fd['digits']} digits" + ("" if fd["signed"] else ", not negative")
    if not ok:
        raise ValueError(f"{where}: needs {need}, got {v!r}")


def _inputs(case: dict, mapping: dict) -> list[tuple[dict, str, list]]:
    """(file, record, rows) per input file in SELECT order, every value checked against the record layout, as are
    the values of PROCEDURE DIVISION USING parameters (`case["linkage"]`: a record per group item, by its name, or
    a value per elementary item) and the clock."""
    out = []
    for f in mapping["files"]:
        if not f["input"]:
            continue
        cf = (case.get("files") or {}).get(f["fd"])
        if cf is None:
            raise ValueError(f"the case has no records for input file {f['fd']}")
        rec = cf.get("record", f["record"])
        if rec != f["record"]:
            raise ValueError(f"{f['fd']}: the case's record {rec} is not the mapping's {f['record']}")
        rows = cf.get("records") or []
        for i, row in enumerate(rows):
            for fd in mapping["records"][rec]["fields"]:
                _check(fd, row.get(fd["cobol"]), f"{f['fd']} record {i} {fd['cobol']}")
        out.append((f, rec, rows))
    for lk in mapping.get("linkage") or []:
        v = (case.get("linkage") or {}).get(lk["name"])
        if "record" in lk:
            if not isinstance(v, dict):
                raise ValueError(f"the case has no record for the USING parameter {lk['name']} (`linkage`)")
            for fd in mapping["records"][lk["record"]]["fields"]:
                _check(fd, v.get(fd["cobol"]), f"USING {lk['name']} {fd['cobol']}")
        else:
            _check(lk["field"], v, f"USING {lk['name']}")
    if mapping.get("clock") and not (isinstance(case.get("clock"), str) and len(case["clock"]) == 21):
        raise ValueError("the program reads the clock: the case needs a 21-character `clock`")
    return out


def _outputs(mapping: dict) -> list[tuple[str, dict, str, str]]:
    """(outcome key, file, Result field, record) per written and per rewritten file, in SELECT order."""
    return [(key, f, f[attr], f[frm]) for key, attr, frm in (("writes", "java_writes", "write_from"),
                                                             ("rewrites", "java_rewrites", "rewrite_from"))
            for f in mapping["files"] if f.get(attr)]


def _outcome(d: dict) -> dict:
    """The driver's JSON as the canonical outcome."""
    return {"end": "abend" if d["abended"] else "normal", "displays": d["displays"], "writes": d["writes"],
            "rewrites": d["rewrites"], "return_code": d["return_code"]}


# ---------------------------------------------------------------------------------------------------------------
# guided arm: drivers


def _jstr(s: str) -> str:
    """Java string literal. Octal escapes up to U+00FF: a \\uXXXX escape is expanded before lexing, so \\u000a
    would end the line."""
    out = ['"']
    for c in s:
        o = ord(c)
        if c in '"\\':
            out.append("\\" + c)
        elif 0x20 <= o < 0x7F:
            out.append(c)
        elif o < 0x100:
            out.append("\\%03o" % o)
        else:
            out.append("\\u%04x" % o)
    out.append('"')
    return "".join(out)


def _lit(fd: dict, v) -> str:
    if fd.get("occurs"):
        return f"new {_jtype(fd)[:-2]}[]{{{', '.join(_lit({**fd, 'occurs': None}, x) for x in v)}}}"
    return _jstr(v) if fd["kind"] == "alnum" else f"{v}L"


def _jtype(fd: dict) -> str:
    """The style guide's Java type of a field (any USAGE: numerics are long)."""
    return ("String" if fd["kind"] == "alnum" else "long") + ("[]" if fd.get("occurs") else "")


def _ident(name: str) -> str:
    return re.sub(r"\W", "_", name)


OUT_SRC = r"""/* Generated by veriforch (modernize/javarun.py): JSON text for the drivers, in printable ASCII. */
final class VoJrOut {
    static void str(StringBuilder sb, String s) {
        if (s == null) {
            sb.append("null");
            return;
        }
        String hex = "0123456789abcdef";
        sb.append('"');
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c >= 32 && c < 127 && c != '"' && c != '\\') {
                sb.append(c);
            } else {
                sb.append("\\u");
                sb.append(hex.charAt((c >> 12) & 15));
                sb.append(hex.charAt((c >> 8) & 15));
                sb.append(hex.charAt((c >> 4) & 15));
                sb.append(hex.charAt(c & 15));
            }
        }
        sb.append('"');
    }

    static void strs(StringBuilder sb, java.util.List<?> l) {
        sb.append('[');
        for (int i = 0; i < l.size(); i++) {
            if (i > 0) {
                sb.append(',');
            }
            str(sb, (String) l.get(i));
        }
        sb.append(']');
    }

    static void longArr(StringBuilder sb, long[] a) {
        if (a == null) {
            sb.append("null");
            return;
        }
        sb.append('[');
        for (int i = 0; i < a.length; i++) {
            if (i > 0) {
                sb.append(',');
            }
            sb.append(a[i]);
        }
        sb.append(']');
    }

    static void strArr(StringBuilder sb, String[] a) {
        if (a == null) {
            sb.append("null");
            return;
        }
        sb.append('[');
        for (int i = 0; i < a.length; i++) {
            if (i > 0) {
                sb.append(',');
            }
            str(sb, a[i]);
        }
        sb.append(']');
    }

    /* The writes of a variable-length file: each record as {"<record name>": "<text>"}. */
    static void texts(StringBuilder sb, String key, java.util.List<?> l) {
        sb.append('[');
        for (int i = 0; i < l.size(); i++) {
            if (i > 0) {
                sb.append(',');
            }
            sb.append('{');
            str(sb, key);
            sb.append(':');
            str(sb, (String) l.get(i));
            sb.append('}');
        }
        sb.append(']');
    }
}
"""

JVM_SRC = r"""/* Generated by veriforch (modernize/javarun.py): runs the drivers VoJrCase<k> given as arguments, each in a
   fresh class loader (the translation's static fields start over) and in its own thread with a time limit, and
   prints one frame per case: "@@VO-JV <i> <normal|exc|timeout> <n1> <n2>\n", then n1 bytes (the outcome JSON or
   the exception) and n2 bytes (what the case printed itself), then "\n". After a timeout it halts. */
import java.io.ByteArrayOutputStream;
import java.io.FileDescriptor;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Paths;

public final class VoJrJvm {
    static final class Job implements Runnable {
        final ClassLoader loader;
        final String cls;
        String json;
        Throwable error;

        Job(ClassLoader loader, String cls) {
            this.loader = loader;
            this.cls = cls;
        }

        public void run() {
            try {
                json = (String) Class.forName(cls, true, loader).getMethod("json").invoke(null);
            } catch (InvocationTargetException e) {
                error = e.getCause();
            } catch (Throwable e) {
                error = e;
            }
        }
    }

    static void frame(OutputStream out, int i, String status, byte[] a, byte[] b) throws java.io.IOException {
        String head = "@@VO-JV " + i + " " + status + " " + a.length + " " + b.length + "\n";
        out.write(head.getBytes(StandardCharsets.US_ASCII));
        out.write(a);
        out.write(b);
        out.write('\n');
        out.flush();
    }

    static String trace(Throwable e) {
        StringBuilder sb = new StringBuilder("Exception in thread \"main\" ").append(e);
        int n = 0;
        for (StackTraceElement f : e.getStackTrace()) {
            String c = f.getClassName();
            if (n == 12 || c.startsWith("jdk.internal.reflect.") || c.startsWith("java.lang.reflect.")) {
                break;
            }
            sb.append("\n\tat ").append(f);
            n++;
        }
        return sb.toString();
    }

    public static void main(String[] args) throws Exception {
        URL[] urls = {Paths.get(args[0]).toUri().toURL(), Paths.get(args[1]).toUri().toURL()};
        long ms = Long.parseLong(args[2]);
        OutputStream out = new FileOutputStream(FileDescriptor.out);
        PrintStream stdout = System.out;
        for (int i = 3; i < args.length; i++) {
            URLClassLoader loader = new URLClassLoader(urls, ClassLoader.getPlatformClassLoader());
            Job job = new Job(loader, args[i]);
            ByteArrayOutputStream cap = new ByteArrayOutputStream();
            System.setOut(new PrintStream(cap, true, "ISO-8859-1"));
            Thread t = new Thread(job);
            t.start();
            t.join(ms);
            System.setOut(stdout);
            byte[] own = cap.toByteArray();
            if (t.isAlive()) {
                frame(out, i - 3, "timeout", new byte[0], own);
                Runtime.getRuntime().halt(3);
            }
            if (job.error != null) {
                frame(out, i - 3, "exc", trace(job.error).getBytes(StandardCharsets.UTF_8), own);
            } else {
                frame(out, i - 3, "normal", String.valueOf(job.json).getBytes(StandardCharsets.UTF_8), own);
            }
            loader.close();
        }
    }
}
"""


def _driver(k: int, case: dict, mapping: dict, inputs: list[tuple[dict, str, list]]) -> str:
    """Java source of `VoJrCase<k>`: `json()` builds the case's input records, calls run and returns the outcome
    as JSON with COBOL field names; `main` prints it after MARK (the interpreter's entry point)."""
    jc, recs = mapping["java_class"], mapping["records"]
    L = [f"/* Generated by veriforch (modernize/javarun.py): case {k} for {jc}. */", f"public final class VoJrCase{k} {{"]
    args = []
    for n, (_f, rec, rows) in enumerate(inputs):
        cls, fields = f"{jc}.{recs[rec]['class']}", recs[rec]["fields"]
        L += [f"    private static {cls}[] in{n}() {{", f"        {cls}[] a = new {cls}[{len(rows)}];"]
        L += [f"        in{n}_{j // CHUNK}(a);" for j in range(0, len(rows), CHUNK)]
        L += ["        return a;", "    }"]
        for j in range(0, len(rows), CHUNK):
            L.append(f"    private static void in{n}_{j // CHUNK}({cls}[] a) {{")
            for i in range(j, min(j + CHUNK, len(rows))):
                L.append(f"        a[{i}] = new {cls}({', '.join(_lit(fd, rows[i][fd['cobol']]) for fd in fields)});")
            L.append("    }")
        args.append(f"in{n}()")
    for lk in mapping.get("linkage") or []:
        v = case["linkage"][lk["name"]]
        if "record" in lk:
            fields = recs[lk["record"]]["fields"]
            args.append(f"new {jc}.{recs[lk['record']]['class']}({', '.join(_lit(fd, v[fd['cobol']]) for fd in fields)})")
        else:
            args.append(_lit(lk["field"], v))
    if mapping.get("clock"):
        args.append(_jstr(case["clock"]))
    L += ["    public static String json() {",
          f"        {jc}.Result r = {jc}.run({', '.join(args)});",
          "        StringBuilder sb = new StringBuilder();",
          f"        sb.append({_jstr('{\"displays\":')});",
          "        VoJrOut.strs(sb, r.displays);"]
    outs = _outputs(mapping)
    for key in ("writes", "rewrites"):
        L.append(f"        sb.append({_jstr(',' + json.dumps(key) + ':{')});")
        for m, (_k, f, field, rec) in enumerate(o for o in outs if o[0] == key):
            if key == "writes" and f.get("varying"):
                # RECORD IS VARYING: Result holds the records as text (style guide)
                L += [f"        sb.append({_jstr((',' if m else '') + json.dumps(f['fd']) + ':')});",
                      f"        VoJrOut.texts(sb, {_jstr(rec)}, r.{field});"]
                continue
            L += [f"        sb.append({_jstr((',' if m else '') + json.dumps(f['fd']) + ':[')});",
                  f"        for (int i = 0; i < r.{field}.size(); i++) {{",
                  "            if (i > 0) {",
                  "                sb.append(',');",
                  "            }",
                  f"            rec_{_ident(rec)}(sb, ({jc}.{recs[rec]['class']}) r.{field}.get(i));",
                  "        }",
                  "        sb.append(']');"]
        L.append("        sb.append('}');")
    L += [f"        sb.append({_jstr(',\"return_code\":')});",
          "        sb.append(r.returnCode);" if mapping.get("return_code") else f"        sb.append({_jstr('null')});",
          f"        sb.append({_jstr(',\"abended\":')});",
          '        sb.append(r.abended ? "true" : "false");',
          "        sb.append('}');",
          "        return sb.toString();",
          "    }",
          "    public static void main(String[] args) {",
          "        String s = json();",
          f"        System.out.println({_jstr(MARK)});",
          "        System.out.println(s);",
          "    }"]
    outs = [o for o in outs if not (o[0] == "writes" and o[1].get("varying"))]   # records as objects
    for rec in sorted({o[3] for o in outs}):
        L += [f"    private static void rec_{_ident(rec)}(StringBuilder sb, {jc}.{recs[rec]['class']} x) {{",
              "        if (x == null) {",
              f"            sb.append({_jstr('null')});",
              "            return;",
              "        }",
              "        sb.append('{');"]
        for i, fd in enumerate(recs[rec]["fields"]):
            L.append(f"        sb.append({_jstr((',' if i else '') + json.dumps(fd['cobol']) + ':')});")
            if fd.get("occurs"):
                L.append(f"        VoJrOut.{'strArr' if fd['kind'] == 'alnum' else 'longArr'}(sb, x.{fd['java']});")
            else:
                L.append(f"        VoJrOut.str(sb, x.{fd['java']});" if fd["kind"] == "alnum"
                         else f"        sb.append(x.{fd['java']});")
        L += ["        sb.append('}');", "    }"]
    # never called: makes javac check every field's name and type in every record class the driver passes or reads
    used = {rec for _f, rec, _rows in inputs} | {o[3] for o in outs} | {
        lk["record"] for lk in mapping.get("linkage") or [] if "record" in lk}
    for rec in sorted(used):
        L.append(f"    private static void iface_{_ident(rec)}({jc}.{recs[rec]['class']} x) {{")
        L += [f"        {_jtype(fd)} f{i} = x.{fd['java']};" for i, fd in enumerate(recs[rec]["fields"])]
        L.append("    }")
    L.append("}")
    return "\n".join(L) + "\n"


# ---------------------------------------------------------------------------------------------------------------
# results


def _compile_error(stage: str, message: str) -> list[dict]:
    """The whole version's result when it does not build: one element, whatever the number of cases."""
    return [{"status": "compile_error", "message": message, "stage": stage}]


def _err(message: str, stdout: str = "", timeout: bool = False, stuck: bool = False) -> dict:
    return {"status": "runtime_error", "message": message, "timeout": timeout, "stuck": stuck, "stdout": stdout}


_FRAME = re.compile(rb"@@VO-J([VB]) (\d+) (\w+) (\d+) (\d+)\n")


def _frames(out: bytes) -> dict[int, tuple[str, bytes, bytes]]:
    """{i: (status, part 1, part 2)} from the frames `@@VO-JV|JB <i> <status> <n1> <n2>\\n<n1 bytes><n2 bytes>\\n`
    (a frame cut short by the end of the process is left out)."""
    res, pos = {}, 0
    while (m := _FRAME.search(out, pos)) is not None:
        a, n1, n2 = m.end(), int(m.group(4)), int(m.group(5))
        if a + n1 + n2 > len(out):
            break
        res[int(m.group(2))] = (m.group(3).decode(), out[a:a + n1], out[a + n1:a + n1 + n2])
        pos = a + n1 + n2
    return res


def _batch(run, todo: list[int]) -> dict[int, tuple[str, bytes, bytes]]:
    """Frames for the cases `todo` from `run(cases) -> ({position: frame}, why the process ended)`, started again
    after the first case without a frame (the process ended on it: that case gets a `died` frame) or after a
    `timeout` frame (the JVM halts after one), until every case has a frame."""
    got: dict[int, tuple[str, bytes, bytes]] = {}
    while todo:
        frames, why = run(todo)
        k = 0
        while k < len(todo) and k in frames:
            got[todo[k]] = frames[k]
            k += 1
        if k < len(todo) and not (k and frames[k - 1][0] == "timeout"):
            got[todo[k]] = ("died", b"", why.encode())
            k += 1
        todo = todo[k:]
    return got


def _jvm_exec(fr: tuple[str, bytes, bytes], limit: int) -> dict:
    st, a, b = fr
    if st == "died":
        return _err(b.decode("utf-8", "replace"))
    own = b.decode("latin-1")
    if st == "normal":
        try:
            return {"outcome": _outcome(json.loads(a)), "stdout": own}
        except (ValueError, KeyError, TypeError) as ex:
            return _err(f"unreadable driver output ({ex}): {a[:300]!r}", own)
    if st == "timeout":
        return _err(f"time limit ({limit} s)", own, timeout=True)
    return _err(a.decode("utf-8", "replace"), own)


def _jimple_exec(fr: tuple[str, bytes, bytes]) -> dict:
    st, a, b = fr
    out, msg = a.decode("utf-8", "replace"), b.decode("utf-8", "replace")
    if st == "normal":
        i = out.rfind(MARK + "\n")
        try:
            oc = _outcome(json.loads(out[i + len(MARK) + 1:].split("\n", 1)[0])) if i >= 0 else None
        except (ValueError, KeyError, TypeError):
            oc = None
        if oc is None:
            return _err("no outcome printed", out[-2000:])
        return {"outcome": oc, "stdout": out[:i]}
    if st == "wrong":
        return _err("JimpleLean's interpreter got stuck: the verifier's model of Java does not cover what the "
                    f"translation does here ({msg})", out, stuck=True)
    if st == "fuel":
        return _err(f"JimpleLean's interpreter ran {msg}", out, timeout=True)
    return _err(msg, out)


def _exc_class(msg: str | None) -> str | None:
    m = re.search(r'Exception in thread "main" ([\w.$]+)', msg or "")
    return m.group(1) if m else None


def _same(a: dict, b: dict) -> bool:
    if ("outcome" in a) != ("outcome" in b):
        return False
    if "outcome" in a:
        return a["outcome"] == b["outcome"]
    if a["timeout"] or b["timeout"] or a["stuck"] or b["stuck"]:
        return (a["timeout"], a["stuck"]) == (b["timeout"], b["stuck"])
    return _exc_class(a["message"]) == _exc_class(b["message"])


def _short(v) -> str:
    s = json.dumps(v, ensure_ascii=False)
    return s if len(s) <= 160 else s[:160] + "..."


def _diff(x, y, path: str) -> str:
    """The first place where two JSON values differ."""
    if isinstance(x, dict) and isinstance(y, dict):
        for k in list(x) + [k for k in y if k not in x]:
            if k not in x or k not in y:
                return f"{path}.{k}: only in {'jvm' if k in x else 'jimple'}"
            if x[k] != y[k]:
                return _diff(x[k], y[k], f"{path}.{k}")
    if isinstance(x, list) and isinstance(y, list):
        for i in range(min(len(x), len(y))):
            if x[i] != y[i]:
                return _diff(x[i], y[i], f"{path}[{i}]")
        if len(x) != len(y):
            return f"{path}: {len(x)} items on the JVM, {len(y)} in the interpreter"
    return f"{path}: JVM {_short(x)}, interpreter {_short(y)}"


def _describe(a: dict, b: dict) -> str:
    if "outcome" in a and "outcome" in b:
        return _diff(a["outcome"], b["outcome"], "outcome")

    def one(e):
        return "outcome" if "outcome" in e else f"runtime_error ({(e['message'].splitlines() or [''])[0][:300]})"
    return f"JVM: {one(a)}; interpreter: {one(b)}"


def _result(jv: dict, jb: dict | None) -> dict:
    """A guided case: both executions, which of them gave the reported (JVM) result, and whether they agree."""
    if jb is None:
        return {"executions": {"jvm": jv}, "produced_by": ["jvm"], "agree": None, "disagreement": None,
                "skipped": {"jimple": "not run: the JVM run hit its time limit"}}
    same = _same(jv, jb)
    return {"executions": {"jvm": jv, "jimple": jb}, "produced_by": ["jvm", "jimple"] if same else ["jvm"],
            "agree": same, "disagreement": None if same else _describe(jv, jb)}


# ---------------------------------------------------------------------------------------------------------------
# builds


def _build(trans_dir: Path, work: Path, arm: str, java_class: str) -> dict:
    """Compile the translation (guided: also Soot and JimpleLean's parser), cached in `work/build-<arm>-<hash>`.
    Returns {"ok": True, "dir": ...} or {"ok": False, "stage": ..., "message": ...}."""
    jd = trans_dir / "java"
    files = sorted(jd.rglob("*.java") if arm == "naive" else jd.glob("*.java")) if jd.is_dir() else []
    if arm == "guided" and not (jd / f"{java_class}.java").is_file():
        return {"ok": False, "stage": "javac", "message": f"the translation has no java/{java_class}.java"}
    if not files:
        return {"ok": False, "stage": "javac", "message": "the translation has no Java sources (java/*.java)"}
    h = hashlib.sha256(f"{arm}|release 17|{SOOT.name}|{JIMPLELEAN.name}".encode())
    for f in files:
        h.update(str(f.relative_to(jd)).encode() + b"\0" + f.read_bytes() + b"\0")
    final = work / f"build-{arm}-{h.hexdigest()[:20]}"
    if (final / "build.json").is_file():
        return {**json.loads((final / "build.json").read_text()), "dir": str(final)}
    tmp = work / f"tmp-build-{arm}-{os.getpid()}-{uuid.uuid4().hex[:8]}"
    (tmp / "classes").mkdir(parents=True)
    log = work / "guard.log"
    try:
        rc, o, e = _run1([*JAVAC, "-d", str(tmp / "classes"), *(str(f.relative_to(jd)) for f in files)], jd, 300, 64, log)
        if rc != 0:
            info = {"ok": False, "stage": "javac", "message": _tail(o + e), "transient": rc in (124, 137)}
        elif arm == "guided" and (err := _soot(tmp / "classes", str(tmp / "classes"), tmp / "jimple", tmp, log)):
            info = {"ok": False, "stage": "soot", "message": err, "transient": False}
        elif arm == "guided":
            # JimpleLean's parser on the translation's Jimple: vo-jbatch with no class to run only loads the program
            rc, o, e = _run1([str(jbatch()), str(tmp / "jimple"), "1"], tmp, 300, 128, log)
            info = ({"ok": True} if rc == 0 else
                    {"ok": False, "stage": "jimple-import", "message": _tail(o + e), "transient": rc != 2})
        else:
            info = {"ok": True}
        if info.pop("transient", False) or info.get("stage") in ("soot", "jimple-import"):
            return info                          # not cached: only successes and javac's verdicts follow from the sources
        (tmp / "build.json").write_text(json.dumps(info))
        try:
            tmp.rename(final)
        except OSError:                          # another process cached the same build first
            pass
        return {**info, "dir": str(final)}
    finally:
        if tmp.exists():
            _rmtree_own(tmp, work, ("tmp-build-",))


def _work(trans_dir: Path, work_dir: Path | None) -> tuple[Path, Path]:
    """(work dir, a fresh run dir in it)."""
    work = Path(work_dir).resolve() if work_dir else trans_dir / "javarun"
    run = work / f"run-{os.getpid()}-{uuid.uuid4().hex[:10]}"
    run.mkdir(parents=True)
    return work, run


# ---------------------------------------------------------------------------------------------------------------
# guided arm


def run_guided_batch(trans_dir, cases: list[dict], mapping: dict, *, work_dir=None, jvm_timeout: int = 60,
                     jimple_timeout: int = 300, fuel: int = 100_000_000, keep: bool = False) -> list[dict]:
    """Run a guided translation on every case (module doc): one result per case, in order. `jvm_timeout` and
    `jimple_timeout` are seconds per case, `fuel` the interpreter's steps per case; `keep` keeps the run dir."""
    trans_dir = Path(trans_dir).resolve()        # every job runs in its own directory: absolute paths only
    inputs = [_inputs(c, mapping) for c in cases]            # malformed cases are the caller's error: ValueError
    if not cases:
        return []
    work, run = _work(trans_dir, work_dir)
    log = work / "guard.log"
    try:
        b = _build(trans_dir, work, "guided", mapping["java_class"])
        if not b["ok"]:
            return _compile_error(b["stage"], b["message"])
        bclasses, bjimple = Path(b["dir"]) / "classes", Path(b["dir"]) / "jimple"
        src, drv, jvm = run / "src", run / "drv", run / "jvm"
        for d in (src, drv, jvm):
            d.mkdir()
        (src / "VoJrOut.java").write_text(OUT_SRC)
        for k, case in enumerate(cases):
            (src / f"VoJrCase{k}.java").write_text(_driver(k, case, mapping, inputs[k]))
        rc, o, e = _run1([*JAVAC, "-cp", str(bclasses), "-d", str(drv), *sorted(p.name for p in src.glob("*.java"))],
                         src, 300 + 2 * len(cases), 64, log)
        if rc != 0:
            # every driver has the same interface errors: javac on the first one alone gives them once
            rc, o1, e1 = _run1([*JAVAC, "-cp", str(bclasses), "-d", str(run), "VoJrOut.java", "VoJrCase0.java"], src,
                               300, 64, log)
            return _compile_error("driver", (
                "The test driver VoJrCase0.java, which calls run and reads Result and the record classes exactly as "
                "the style guide fixes them (names, field types, the all-fields constructors), does not compile "
                f"against the translation:\n{_tail(o1 + e1 if rc != 0 else o + e)}"))
        (jvm / "VoJrJvm.java").write_text(JVM_SRC)
        rc, o, e = _run1([*JAVAC, "-d", str(jvm), "VoJrJvm.java"], jvm, 300, 64, log)
        if rc != 0:
            raise RuntimeError(f"javarun: VoJrJvm does not compile:\n{_tail(o + e)}")
        err = _soot(drv, f"{bclasses}:{drv}", run / "jimple", run, log)
        if err:
            return _compile_error("soot", err)

        def jvm_run(todo):
            rc, o, e = _run1([*CLEAN_ENV, *JAVA_RUN, "-cp", str(jvm), "VoJrJvm", str(bclasses), str(drv),
                              str(jvm_timeout * 1000), *(f"VoJrCase{i}" for i in todo)],
                             run, jvm_timeout * len(todo) + 120, 64, log)
            return _frames(o), f"the JVM ended (exit {rc}) during this case: {_tail(e, 1500)}"

        jv = {i: _jvm_exec(fr, jvm_timeout) for i, fr in _batch(jvm_run, list(range(len(cases)))).items()}
        exe = jbatch()
        parse_error = []

        def jimple_run(todo):
            rc, o, e = _run1([str(exe), f"{bjimple}:{run / 'jimple'}", str(fuel), *(f"VoJrCase{i}" for i in todo)],
                             run, jimple_timeout * len(todo) + 120, 128, log)
            if rc == 2:
                parse_error.append(_tail(o + e))
                return {p: ("died", b"", b"") for p in range(len(todo))}, ""
            return _frames(o), f"the interpreter ended (exit {rc}) during this case: {_tail(e, 1500)}"

        # a case that hit the JVM's time limit does not terminate: the interpreter would only burn its fuel
        todo = [i for i in range(len(cases)) if not jv[i].get("timeout")]
        jb = {i: _jimple_exec(fr) for i, fr in _batch(jimple_run, todo).items()} if todo else {}
        if parse_error:
            return _compile_error("jimple-import", parse_error[0])
        return [_result(jv[i], jb.get(i)) for i in range(len(cases))]
    finally:
        if not keep:
            _rmtree_own(run, work, ("run-",))


def run_guided(trans_dir, case: dict, mapping: dict, **kw) -> dict:
    """`run_guided_batch` for one case."""
    return run_guided_batch(trans_dir, [case], mapping, **kw)[0]


# ---------------------------------------------------------------------------------------------------------------
# naive arm


def _zoned(fd: dict, v: int) -> str:
    s = str(abs(v)).zfill(fd["digits"])
    if not fd["signed"]:
        return s
    if fd.get("sign_separate"):
        return ("-" if v < 0 else "+") + s if fd.get("sign_leading") else s + ("-" if v < 0 else "+")
    zone = _NEG if v < 0 else _POS
    return zone[int(s[0])] + s[1:] if fd.get("sign_leading") else s[:-1] + zone[int(s[-1])]


def _unzoned(fd: dict, t: str):
    """The value a zoned field's text stands for, or the text itself when it is no valid image of the PIC (so it
    differs from every value COBOL can produce)."""
    s, neg = t, False
    if fd["signed"] and fd.get("sign_separate"):
        sign, s = (t[:1], t[1:]) if fd.get("sign_leading") else (t[-1:], t[:-1])
        if sign not in ("+", "-"):
            return t
        neg = sign == "-"
    elif fd["signed"]:
        j = 0 if fd.get("sign_leading") else len(t) - 1
        c = t[j:j + 1]
        if c and c in _POS + _NEG:
            neg, s = c in _NEG, t[:j] + str((_POS + _NEG).index(c) % 10) + t[j + 1:]
    if len(s) != fd["digits"] or not (s.isascii() and s.isdigit()):
        return t
    return -int(s) if neg else int(s)


def record_image(rec: dict, row: dict) -> str:
    """A record's text image in copybook layout (naive I/O contract)."""
    buf = [" "] * rec["size"]
    for fd in rec["fields"]:
        if fd.get("usage", "display") != "display":
            raise ValueError(f"{fd['cobol']}: USAGE {fd['usage']} has no text image (naive I/O contract)")
        vals = row[fd["cobol"]] if fd.get("occurs") else [row[fd["cobol"]]]
        for j, v in enumerate(vals):
            t = v if fd["kind"] == "alnum" else _zoned(fd, v)
            if len(t) != fd["len"]:
                raise ValueError(f"{fd['cobol']}: image {t!r} is not {fd['len']} characters long")
            o = fd["offset"] + j * fd.get("stride", 0)
            buf[o:o + fd["len"]] = t
    return "".join(buf)


def parse_image(rec: dict, line: str) -> dict:
    """A record from its text image. A short line is padded with spaces (line-sequential writers drop trailing
    spaces); text beyond the record goes to `_extra`, so that the record differs from any COBOL record."""
    row = {}
    padded = line.ljust(rec["size"])
    for fd in rec["fields"]:
        vals = []
        for j in range(fd.get("occurs") or 1):
            t = padded[fd["offset"] + j * fd.get("stride", 0):][:fd["len"]]
            vals.append(t if fd["kind"] == "alnum" else _unzoned(fd, t))
        row[fd["cobol"]] = vals if fd.get("occurs") else vals[0]
    if len(line) > rec["size"]:
        row["_extra"] = line[rec["size"]:]
    return row


def _lines(b: bytes) -> list[str]:
    """Lines of UTF-8 text (an invalid byte becomes U+FFFD, which is no CP037 character)."""
    text = b.decode("utf-8", "replace")
    if not text:
        return []
    lines = text.split("\n")
    if text.endswith("\n"):
        lines.pop()
    return [ln[:-1] if ln.endswith("\r") else ln for ln in lines]


def parm_text(case: dict, mapping: dict) -> str | None:
    """The JCL EXEC PARM text a naive program gets as its first argument: the text fields of the case's USING
    record, joined (None for a program without PROCEDURE DIVISION USING)."""
    lks = mapping.get("linkage") or []
    if not lks:
        return None
    if len(lks) > 1:
        raise ValueError("a naive program gets one PARM text, not one per PROCEDURE DIVISION USING item")
    lk, v = lks[0], case["linkage"][lks[0]["name"]]
    if "record" not in lk:
        return v if lk["field"]["kind"] == "alnum" else str(v)
    return "".join(v[fd["cobol"]] for fd in mapping["records"][lk["record"]]["fields"] if fd["kind"] == "alnum")


def _naive_case(rc: int, out: bytes, err: bytes, cdir: Path, mapping: dict, inputs: list, timeout: int) -> dict:
    err_t = err.decode("utf-8", "replace")
    if rc in (124, 137):
        jv = _err(f"time limit ({timeout} s)", timeout=True)
    elif "Exception in thread" in err_t or "Error: " in err_t[:200]:
        jv = _err(err_t.strip()[:4000])
    elif rc not in (0, *ABEND_STATUS) and not mapping.get("return_code"):
        jv = _err(f"exit status {rc}: {err_t.strip()[:2000]}")
    else:
        jv = None
    if jv is not None:
        return {"executions": {"jvm": {**jv, "rc": rc}}, "produced_by": ["jvm"], "agree": None, "disagreement": None}
    recs, notes = mapping["records"], []
    given = {f["fd"]: rows for f, _rec, rows in inputs}
    after, writes, rewrites = {}, {}, {}
    for key, f, _field, rec in _outputs(mapping):
        if f["fd"] not in after:
            p = cdir / f["assign"]
            if not p.is_file():
                notes.append(f"{f['fd']}: no file {f['assign']} after the run")
            lines = _lines(p.read_bytes()) if p.is_file() else []
            after[f["fd"]] = ([{rec: ln} for ln in lines] if f.get("varying") else
                              [parse_image(recs[rec], ln) for ln in lines])
        final, old = after[f["fd"]], given.get(f["fd"], [])
        if key == "writes" and not f["input"]:
            writes[f["fd"]] = final
        elif key == "writes":
            # the file also held input: its writes are the records of the final file that the input did not have
            pool, new = [dict(r) for r in old], []
            for r in final:
                if r in pool:
                    pool.remove(r)
                else:
                    new.append(r)
            writes[f["fd"]] = new
            notes.append(f"{f['fd']}: writes are the records of the final file that the input did not have")
        else:
            # a line-sequential file keeps no REWRITE log: the records that changed, in file order
            rewrites[f["fd"]] = [r for i, r in enumerate(final) if i >= len(old) or r != old[i]]
            notes.append(f"{f['fd']}: rewrites are the records that differ from the input, in file order")
    abend = rc in ABEND_STATUS
    oc = {"end": "abend" if abend else "normal", "displays": _lines(out), "writes": writes, "rewrites": rewrites,
          "return_code": rc if mapping.get("return_code") and not abend else None}
    return {"executions": {"jvm": {"outcome": oc, "rc": rc}}, "produced_by": ["jvm"], "agree": None,
            "disagreement": None, "notes": notes, "files_after": after}


def run_naive_batch(trans_dir, cases: list[dict], mapping: dict, *, work_dir=None, timeout: int = 60,
                    main_class: str | None = None, keep: bool = False) -> list[dict]:
    """Run a naive translation on every case (module doc): one result per case, in order. `timeout` is seconds per
    case; `main_class` overrides the contract's main class (`java_class`, default package)."""
    trans_dir = Path(trans_dir).resolve()        # every job runs in its own directory: absolute paths only
    inputs = [_inputs(c, mapping) for c in cases]
    parms = [parm_text(c, mapping) for c in cases]
    if not cases:
        return []
    work, run = _work(trans_dir, work_dir)
    log = work / "guard.log"
    try:
        b = _build(trans_dir, work, "naive", mapping["java_class"])
        if not b["ok"]:
            return _compile_error(b["stage"], b["message"])
        main = main_class or mapping["java_class"]
        if not (Path(b["dir"]) / "classes" / (main.replace(".", "/") + ".class")).is_file():
            return _compile_error("setup", f"There is no class {main} in the default package: the I/O contract "
                                           f"fixes the main class, {main}.")
        dirs = []
        for k, (case, inp) in enumerate(zip(cases, inputs)):
            cdir = run / f"c{k}"
            cdir.mkdir()
            for f, rec, rows in inp:
                text = "".join(record_image(mapping["records"][rec], r) + "\n" for r in rows)
                (cdir / f["assign"]).write_bytes(text.encode("utf-8"))
            if mapping.get("clock"):
                Path(f"{cdir}.clock").write_text(case["clock"])
            if parms[k] is not None:
                Path(f"{cdir}.parm").write_bytes(parms[k].encode("utf-8"))
            dirs.append(cdir)
        java = " ".join(shlex.quote(a) for a in [*JAVA_NAIVE, "-cp", str(Path(b["dir"]) / "classes"), main])
        env = " ".join(shlex.quote(a) for a in CLEAN_ENV)
        script = run / "naive.sh"
        script.write_text("\n".join([
            "#!/usr/bin/env bash",
            "# Generated by veriforch (modernize/javarun.py): one JVM per case, in the case's directory, with the",
            "# case's clock in COBOL_CURRENT_DATE and its PARM text as the first argument.",
            'for d in "$@"; do',
            '  cd "$d" || exit 3',
            "  clk=()",
            '  if [ -f "$d.clock" ]; then clk=("COBOL_CURRENT_DATE=$(cat "$d.clock")"); fi',
            '  if [ -f "$d.parm" ]; then',
            f'    timeout -k 5 {timeout} {env} "${{clk[@]}}" {java} "$(cat "$d.parm")" < /dev/null > "$d.out" 2> "$d.err"',
            "  else",
            f'    timeout -k 5 {timeout} {env} "${{clk[@]}}" {java} < /dev/null > "$d.out" 2> "$d.err"',
            "  fi",
            '  echo $? > "$d.rc"',
            "done", ""]))
        todo = list(range(len(cases)))
        while todo:
            rc, o, e = _run1(["bash", str(script), *(str(dirs[i]) for i in todo)], run,
                             (timeout + 15) * len(todo) + 60, 64, log)
            left = [i for i in todo if not Path(f"{dirs[i]}.rc").is_file()]
            if len(left) == len(todo):               # no progress: the job itself fails
                why = f"the batch job ended (exit {rc}) before this case: {_tail(o + e, 1500)}"
                Path(f"{dirs[left[0]]}.rc").write_text("-1\n")
                Path(f"{dirs[left[0]]}.err").write_bytes(why.encode())
                left = left[1:]
            todo = left
        res = []
        for k, d in enumerate(dirs):
            rc = int(Path(f"{d}.rc").read_text().strip() or -1)
            out = Path(f"{d}.out").read_bytes() if Path(f"{d}.out").is_file() else b""
            err = Path(f"{d}.err").read_bytes() if Path(f"{d}.err").is_file() else b""
            res.append(_naive_case(rc, out, err, d, mapping, inputs[k], timeout))
        return res
    finally:
        if not keep:
            _rmtree_own(run, work, ("run-",))


def run_naive(trans_dir, case: dict, mapping: dict, **kw) -> dict:
    """`run_naive_batch` for one case."""
    return run_naive_batch(trans_dir, [case], mapping, **kw)[0]


def main(argv: list[str]) -> int:
    """python -m veriforch.modernize.javarun guided|naive TRANS_DIR MAPPING.json CASE.json...: print the results."""
    if len(argv) < 5 or argv[1] not in ("guided", "naive"):
        print(main.__doc__, file=sys.stderr)
        return 2
    mapping = json.loads(Path(argv[3]).read_text())
    cases = [json.loads(Path(c).read_text()) for c in argv[4:]]
    run = run_guided_batch if argv[1] == "guided" else run_naive_batch
    print(json.dumps(run(argv[2], cases, mapping), indent=1, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
