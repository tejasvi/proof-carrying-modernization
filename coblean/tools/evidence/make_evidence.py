"""Build docs/EVIDENCE_carddemo.tsv (the source) and docs/EVIDENCE_carddemo.md (its rendering).

Every claim has a re-check command. The commands use four variables:
  C   the coblean snapshot root (the tree being described),
  CD  the CardDemo checkout (commit 59cc6c2fd7ebd7ef7925cad552a01a4b8b6e4d5e),
  OUT a fresh scratch directory: the commands write nothing anywhere else,
  TC  the Lean toolchain, $HOME/.elan/toolchains/leanprover--lean4---v4.35.0.
This script runs every command (1 core, no network) and records its output as the expected
value. A command whose output is not exactly one line stops the build of the files.

usage: python3 -I -B tools/evidence/make_evidence.py C CD OUT [--only PREFIX,...] [--skip PREFIX,...]
"""
import datetime
import json
import os
import re
import subprocess
import sys
import time

C, CD, OUT = (os.path.abspath(a) for a in sys.argv[1:4])
OPTS = dict(zip(sys.argv[4::2], sys.argv[5::2]))
ONLY = [p for p in OPTS.get("--only", "").split(",") if p]
SKIP = [p for p in OPTS.get("--skip", "").split(",") if p]
TC = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.35.0")
COLS = ["id", "section", "claim", "value", "source", "recheck_cmd", "expected", "checked_utc"]
rows = []


def utc():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def run(cmd, timeout):
    env = {"C": C, "CD": CD, "OUT": OUT, "TC": TC, "HOME": os.environ["HOME"],
           "PATH": "/usr/local/bin:/usr/bin:/bin", "LC_ALL": "C.UTF-8", "LEAN_NUM_THREADS": "1"}
    os.makedirs(OUT, exist_ok=True)
    t0 = time.time()
    p = subprocess.run(["bash", "-c", cmd], capture_output=True, text=True, env=env, timeout=timeout,
                       cwd=OUT)
    return p.stdout, p.stderr, time.time() - t0


def R(id_, section, claim, value, source, cmd, timeout=1800, must=None):
    """A claim. `value` may contain {out}, replaced by the command's output line."""
    rows.append(dict(id=id_, section=section, claim=claim, value=value, source=source,
                     recheck_cmd=cmd, timeout=timeout, must=must))


def norm(s):
    return re.sub(r"[\t\r\n]+", " ", s).strip()


def line_of(path, pattern):
    with open(os.path.join(C, path), encoding="utf-8") as fh:
        for i, l in enumerate(fh, 1):
            if re.match(pattern, l):
                return i
    raise SystemExit(f"{path}: no line matching {pattern}")


# ---------------------------------------------------------------- artifact
S = "artifact"
R("A1", S, "Lean toolchain named by the project", "{out}", "lean-toolchain:1", 'cat "$C/lean-toolchain"')
R("A2", S, "Lean version used for every check", "{out}", "$TC/bin/lean",
  '"$TC/bin/lean" --version')
R("A3", S, "CardDemo commit of the COBOL sources, copybooks and sample data", "{out}",
  "$CD (git checkout)", 'git -C "$CD" rev-parse HEAD')
R("A4", S, "CardDemo sources are unmodified at that commit (tracked files under app/ with changes)",
  "{out} files changed", "$CD (git checkout)",
  'git --no-optional-locks -C "$CD" status --porcelain --untracked-files=no -- app | wc -l')
R("A5", S, "GnuCOBOL version used by the differential tests", "{out}",
  "scripts/cobc.sh (<os-image> debs unpacked in third_party/gnucobol)",
  '"$C/scripts/cobc.sh" --version | head -n 1')

# ---------------------------------------------------------------- trust base
S = "trust"
R("T1", S, "Lean files in which the word bv_decide occurs (definition of the cobol_bv tactic, comments, uses); the theorems that depend on its native axiom are those whose axiom lines list a ._native.bv_decide axiom (section theorems)", "{out}",
  "grep over Cobol/ and Examples/",
  '/usr/bin/grep -rlw bv_decide "$C/Cobol" "$C/Examples" --include=*.lean | sed "s|^$C/||" | LC_ALL=C sort | tr "\\n" " "')
R("T2", S, "Lean files that use native_decide or Lean.ofReduceBool (separately, bv_decide adds its own native axiom to the theorems that call it: row T1 and the TH*.ax rows; only bincnt_equiv, row TH4.ax, depends on one)", "{out} files",
  "grep over Cobol/ and Examples/",
  '/usr/bin/grep -rlE "native_decide|ofReduceBool" "$C/Cobol" "$C/Examples" --include=*.lean | wc -l')
R("T3", S, "Proof files in which the word sorry occurs (theorems with sorry would also show sorryAx in their axiom lines, section theorems)",
  "{out} files", "grep over Cobol/ and Examples/",
  '/usr/bin/grep -rlw sorry "$C/Cobol" "$C/Examples" --include=*.lean | wc -l')
R("T4", S, "Trusted: the semantics definitions that the theorem statements refer to (IR, storage, data formats, statements, files, the COBDATFT model), non-blank non-comment lines",
  "{out} lines", "Cobol/IR.lean Cobol/Mem.lean Cobol/Codec.lean Cobol/Data.lean Cobol/Config.lean Cobol/Round.lean Cobol/Digits.lean Cobol/Edit.lean Cobol/Layout.lean Cobol/Sem/*.lean Cobol/Ext/CardDemo.lean Cobol/Spec.lean",
  'cd "$C" && awk -f tools/evidence/lean_lines.awk Cobol/IR.lean Cobol/Mem.lean Cobol/Codec.lean Cobol/Data.lean Cobol/Config.lean Cobol/Round.lean Cobol/Digits.lean Cobol/Edit.lean Cobol/Layout.lean Cobol/Sem/*.lean Cobol/Ext/CardDemo.lean Cobol/Spec.lean')
R("T5", S, "Trusted: the loader that turns an IR JSON file into the Program constant a theorem is about (cobol_program), non-blank non-comment lines",
  "{out} lines", "Cobol/Frontend/Surface.lean Cobol/Frontend/Resolve.lean Cobol/Frontend/Load.lean",
  'cd "$C" && awk -f tools/evidence/lean_lines.awk Cobol/Frontend/Surface.lean Cobol/Frontend/Resolve.lean Cobol/Frontend/Load.lean')
R("T6", S, "Not trusted, checked by the kernel: proof automation (symbolic execution, simprocs, tactics), non-blank non-comment lines",
  "{out} lines", "Cobol/Logic/*.lean",
  'cd "$C" && awk -f tools/evidence/lean_lines.awk Cobol/Logic/*.lean')
R("T7", S, "Not trusted by any proof: the Python front end that writes the IR JSON files (validated, sections theorems and validation), lines that are neither blank nor # comments",
  "{out} lines", "tools/cobolfe/*.py",
  'cd "$C" && cat tools/cobolfe/*.py | /usr/bin/grep -cv "^[[:space:]]*\\(#.*\\)\\?$"')
R("T8", S, "Not trusted by any proof: cobolrun, the compiled interpreter used only to run programs in the differential tests and sample-data runs",
  "{out}", "CobolRun.lean", 'ls "$C/.lake/build/bin/cobolrun" | sed "s|^$C/||"')
R("T9", S, "cobolrun (run time) and cobol_program (elaboration, the Program constants of the theorems) turn an IR JSON file into a Program with the same function, programOfJson; lines that call it",
  "{out}", "Cobol/Frontend/Load.lean",
  "/usr/bin/grep -n 'programOfJson j' \"$C/Cobol/Frontend/Load.lean\" | cut -d: -f1 | tr '\\n' ' '")

# ---------------------------------------------------------------- semantics scope
S = "semantics"
R("S1", S, "Statement forms of the IR (constructors of Cobol.Stmt)", "{out}", "Cobol/IR.lean",
  "awk '/^inductive Stmt/,/deriving/' \"$C/Cobol/IR.lean\" | /usr/bin/grep '^  | ' | /usr/bin/grep -oE '\\| [a-zA-Z]+' | wc -l")
R("S2", S, "README section listing what is not modelled or is reported as unsupported (sha256 of the section)",
  "{out}", "README.md, section **Not modelled, or reported as `unsupported`:**",
  "awk '/^\\*\\*Not modelled, or reported as `unsupported`:\\*\\*/{on=1} on && /^\\*\\*Proof-side limits/{on=0} on' \"$C/README.md\" | sha256sum | cut -c1-64")
R("S3", S, "Fuel monotonicity: a run that ends with a signal other than outOfFuel ends the same way with any larger fuel (statement, sha256 of its one-line form)",
  "{out}", f"Cobol.Program.run_mono, Cobol/Logic/FuelMono.lean:{line_of('Cobol/Logic/FuelMono.lean', '^theorem Program.run_mono')}",
  "awk -v name=Program.run_mono -f \"$C/tools/evidence/sig.awk\" \"$C/Cobol/Logic/FuelMono.lean\" | sha256sum | cut -c1-64")
R("S4", S, "Kernel-checked library theorems: axioms of Program.run_mono and loopUntil_list_exit",
  "{out}", "docs/evidence_axioms.lean",
  "\"$C/scripts/recheck_lean.sh\" docs/evidence_axioms.lean 2>&1 | tr '\\n' ' '",
  must=r"^(?!.*sorryAx)'Cobol\.Program\.run_mono' depends on axioms: \[[^]]*\] 'Cobol\.loopUntil_list_exit' depends on axioms: \[[^]]*\]\s*$")

# ---------------------------------------------------------------- theorems
S = "theorems"
THMS = [  # (fully qualified name, file, program, IR file)
    ("acctint_equiv", "Examples/AcctInt.lean", "ACCTINT (examples/acctint, not CardDemo)", "examples/acctint/acctint.ir.json"),
    ("acctint_equiv_lowvalues", "Examples/AcctInt.lean", "ACCTINT (examples/acctint, not CardDemo)", "examples/acctint/acctint.ir.json"),
    ("acctint_rust_equiv", "Examples/AcctIntRust.lean", "ACCTINT (examples/acctint, not CardDemo)", "examples/acctint/acctint.ir.json"),
    ("bincnt_equiv", "Examples/Binary.lean", "BINCNT (examples/binary, not CardDemo)", "examples/binary/bincnt.ir.json"),
    ("recsum_equiv", "Examples/RecSum.lean", "RECSUM (examples/recsum, not CardDemo)", "examples/recsum/recsum.ir.json"),
    ("CardDemo.Cbact01c.cbact01c_extracts", "Examples/Cbact01c.lean", "CBACT01C", "examples/carddemo/cbact01c.ir.json"),
    ("CardDemo.Cbact02c.cbact02c_lists", "Examples/Cbact02c.lean", "CBACT02C", "examples/carddemo/cbact02c.ir.json"),
    ("CardDemo.Cbact02c.cbact02c_lists'", "Examples/Cbact02cSum.lean", "CBACT02C", "examples/carddemo/cbact02c.ir.json"),
    ("CardDemo.Cbact03c.cbact03c_lists", "Examples/Cbact03c.lean", "CBACT03C", "examples/carddemo/cbact03c.ir.json"),
    ("CardDemo.Cbcus01c.cbcus01c_lists", "Examples/Cbcus01c.lean", "CBCUS01C", "examples/carddemo/cbcus01c.ir.json"),
    ("CardDemo.Cbact04c.cbact04c_last_account_not_updated", "Examples/Cbact04c.lean", "CBACT04C", "examples/carddemo/cbact04c.ir.json"),
    ("CardDemo.Cbact04c.cbact04c_last_account_not_updated'", "Examples/Cbact04cSum.lean", "CBACT04C", "examples/carddemo/cbact04c.ir.json"),
    ("CardDemo.Cbact04c.cbact04c_two_accounts", "Examples/Cbact04c2.lean", "CBACT04C", "examples/carddemo/cbact04c.ir.json"),
    ("CardDemo.Cbact04c.cbact04c_one_account", "Examples/Cbact04cAny.lean", "CBACT04C", "examples/carddemo/cbact04c.ir.json"),
    ("CardDemo.Cbact04c.cbact04c_all", "Examples/Cbact04cAll.lean", "CBACT04C", "examples/carddemo/cbact04c.ir.json"),
    ("CardDemo.Cbact04c.cbact04c_events", "Examples/Cbact04cEvents.lean", "CBACT04C", "examples/carddemo/cbact04c.ir.json"),
    ("CardDemo.Cbtrn01c.cbtrn01c_verifies", "Examples/Cbtrn01c.lean", "CBTRN01C", "examples/carddemo/cbtrn01c.ir.json"),
    ("CardDemo.Cbtrn01c.cbtrn01c_verifies_all", "Examples/Cbtrn01c.lean", "CBTRN01C", "examples/carddemo/cbtrn01c.ir.json"),
    ("CardDemo.Cbtrn02c.cbtrn02c_posts", "Examples/Cbtrn02c.lean", "CBTRN02C", "examples/carddemo/cbtrn02c.ir.json"),
    ("CardDemo.Cbtrn02c.cbtrn02c_any", "Examples/Cbtrn02cDup.lean", "CBTRN02C", "examples/carddemo/cbtrn02c.ir.json"),
    ("CardDemo.Cbtrn03c.cbtrn03c_report", "Examples/Cbtrn03c.lean", "CBTRN03C", "examples/carddemo/cbtrn03c.ir.json"),
    ("CardDemo.Cbtrn03c.cbtrn03c_stops", "Examples/Cbtrn03cStop.lean", "CBTRN03C", "examples/carddemo/cbtrn03c.ir.json"),
    ("CardDemo.Cbtrn03c.cbtrn03c_any", "Examples/Cbtrn03cAny.lean", "CBTRN03C", "examples/carddemo/cbtrn03c.ir.json"),
    ("CardDemo.Cbtrn03c.cbtrn03c_every", "Examples/Cbtrn03cEvery.lean", "CBTRN03C", "examples/carddemo/cbtrn03c.ir.json"),
    ("CardDemo.Cbact04c.cbact04c_every", "Examples/Cbact04cEvery.lean", "CBACT04C", "examples/carddemo/cbact04c.ir.json"),
]
R("TH0", S, "Full rebuild from source in a copy under $OUT (library, all proof files, cobolrun): build result, theorems with exactly the axioms [propext, Classical.choice, Quot.sound], theorems with a bv_decide axiom; wall time about 20 min on 1 core (17 min measured at a machine load of about 250)",
  "{out}", "scripts/recheck_build.sh",
  "\"$C/scripts/recheck_build.sh\" | awk '/Build completed/ {b = $0} /depends on axioms: \\[propext, Classical.choice, Quot.sound\\]$/ {s++} /bv_decide/ {v++} END {print b \" | standard: \" s + 0 \" | bv_decide: \" v + 0}'",
  timeout=7200, must=r"Build completed successfully")
done_ir = set()
for k, (fq, f, prog, ir) in enumerate(THMS, 1):
    short = fq.split(".")[-1]
    tl = line_of(f, rf"^theorem {re.escape(short)}( |$)")
    src = f"{fq}, {f}:{tl}"
    tid = f"TH{k}"
    R(f"{tid}.ax", S, f"{fq} is kernel-checked; the axioms it depends on ({prog})", "{out}", src,
      f"\"$C/scripts/recheck_lean.sh\" {f} 2>&1 | /usr/bin/grep -F \"'{fq}' depends on axioms\" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'", must=r"^'.+' depends on axioms: \[(?!.*sorryAx)")
    R(f"{tid}.st", S, f"{fq}: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256",
      "{sig}", src,
      f"awk -v name=\"{short}\" -f \"$C/tools/evidence/sig.awk\" \"$C/{f}\" | sha256sum | cut -c1-64")
    rows[-1]["sig_file"], rows[-1]["sig_name"] = f, short
    if ir not in done_ir:
        done_ir.add(ir)
        R(f"IR.{os.path.basename(ir).split('.')[0]}", S, f"IR file loaded by the {prog} proofs (cobol_program), sha256",
          "{out}", ir, f"sha256sum < \"$C/{ir}\" | cut -c1-64")

# the CardDemo IR files are the front end's output on the unmodified sources
for prog in ["CBACT01C", "CBACT02C", "CBACT03C", "CBACT04C", "CBCUS01C", "CBTRN01C", "CBTRN02C", "CBTRN03C"]:
    low = prog.lower()
    R(f"IRFE.{low}", S, f"examples/carddemo/{low}.ir.json is the front end's output on $CD/app/cbl/{prog}.cbl (same JSON after key sorting)",
      "{out}", f"tools/cobolfe/cobolfe.py; examples/carddemo/{low}.ir.json",
      f"mkdir -p \"$OUT/irfe\" && python3 -I -B \"$C/tools/cobolfe/cobolfe.py\" \"$CD/app/cbl/{prog}.cbl\" -I \"$CD/app/cpy\" --tab-width 4 -o \"$OUT/irfe/{low}.json\" && "
      f"[ \"$(jq -S . \"$OUT/irfe/{low}.json\" | sha256sum)\" = \"$(jq -S . \"$C/examples/carddemo/{low}.ir.json\" | sha256sum)\" ] && echo same || echo DIFFERENT", must=r"^same$")
R("IRFE.cbstm03ab", S, "examples/carddemo/cbstm03ab.ir.json is CBSTM03A with CBSTM03B linked in by tools/cobolfe/link.py, from the unmodified sources (same JSON after key sorting)",
  "{out}", "tools/cobolfe/cobolfe.py, tools/cobolfe/link.py; examples/carddemo/cbstm03ab.ir.json",
  "mkdir -p \"$OUT/irfe\" && cd \"$OUT/irfe\" && python3 -I -B \"$C/tools/cobolfe/cobolfe.py\" \"$CD/app/cbl/CBSTM03A.CBL\" -I \"$CD/app/cpy\" --tab-width 4 -o a.json && "
  "python3 -I -B \"$C/tools/cobolfe/cobolfe.py\" \"$CD/app/cbl/CBSTM03B.CBL\" -I \"$CD/app/cpy\" --tab-width 4 -o b.json && "
  "python3 -I -B \"$C/tools/cobolfe/link.py\" a.json b.json -o ab.json > /dev/null && "
  "[ \"$(jq -S . ab.json | sha256sum)\" = \"$(jq -S . \"$C/examples/carddemo/cbstm03ab.ir.json\" | sha256sum)\" ] && echo same || echo DIFFERENT", must=r"^same$")
IRB_FILES = ["acctint/acctint.ir.json", "acctint/acctint.gnucobol.ir.json", "binary/bincnt.ir.json",
             "binary/bincnt.gnucobol.ir.json", "recsum/recsum.ir.json", "recsum/recsum.gnucobol.ir.json"]
R("IRB.examples", S, "The IR files of ACCTINT, BINCNT and RECSUM (IBM and GnuCOBOL configurations) are what examples/*/build_ir.py writes: the scripts, run from a copy in $OUT, produce byte-identical files",
  "{out}", "examples/{acctint,binary,recsum}/build_ir.py, tools/irjson.py",
  "mkdir -p \"$OUT/irb/tools\" && cp \"$C/tools/irjson.py\" \"$OUT/irb/tools/\" && "
  "for d in acctint binary recsum; do mkdir -p \"$OUT/irb/examples/$d\" && cp \"$C/examples/$d/build_ir.py\" \"$OUT/irb/examples/$d/\" || exit 1; done && "
  "python3 -I -B \"$OUT/irb/examples/acctint/build_ir.py\" > /dev/null && python3 -I -B \"$OUT/irb/examples/acctint/build_ir.py\" --ascii > /dev/null && "
  "python3 -I -B \"$OUT/irb/examples/binary/build_ir.py\" > /dev/null && python3 -I -B \"$OUT/irb/examples/recsum/build_ir.py\" > /dev/null && "
  "n=0 && for f in " + " ".join(IRB_FILES) + "; do if cmp -s \"$OUT/irb/examples/$f\" \"$C/examples/$f\"; then n=$((n + 1)); fi; done; "
  "echo \"$n of " + str(len(IRB_FILES)) + " IR files rebuilt identical\"",
  must=r"^6 of 6 IR files rebuilt identical$")

# ---------------------------------------------------------------- coverage (all 44 programs)
S = "coverage"
DIRS = ["app/cbl", "app/app-authorization-ims-db2-mq/cbl", "app/app-transaction-type-db2/cbl",
        "app/app-vsam-mq/cbl"]
progs = []
for d in DIRS:
    for fn in sorted(os.listdir(os.path.join(CD, d))):
        if fn.upper().endswith(".CBL"):
            progs.append(f"{d}/{fn}")
THM_OF = {}
for fq, f, prog, ir in THMS:
    THM_OF.setdefault(prog, []).append(fq.split(".")[-1])
R("CV0", S, "Programs in the CardDemo checkout (app/cbl and the three optional modules)", "{out} programs",
  "$CD/app/*/cbl, $CD/app/cbl",
  "ls \"$CD\"/app/cbl/ \"$CD\"/app/app-*/cbl/ | /usr/bin/grep -ciE '\\.cbl$'")
for p in progs:
    name = os.path.splitext(os.path.basename(p))[0]
    th = ", ".join(THM_OF.get(name, [])) or "none"
    R(f"CV.{name}", S, f"{name}: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: {th}",
      "{out}", f"$CD/{p}",
      f"\"$C/tools/evidence/cov_one.sh\" \"$CD/{p}\"", must=r"^\S+ kind=")
R("CV.CBSTM03AB", S, "CBSTM03A with CBSTM03B linked in: outcome on CardDemo's data (section validation, V.stm*)", "{out}",
  "examples/carddemo/cbstm03ab.ir.json", "\"$C/tools/evidence/sample_runs.sh\" cbstm03ab")
R("CV.sum", S, "Summary over the 44 programs: programs per kind; kind batch with front end ok, with 0 unsupported statements, resolving; covered = kind batch, front end ok, 0 unsupported statements, resolves; CBSTM03A resolves alone but runs only when linked with CBSTM03B (row CV.CBSTM03AB)",
  "{out}", "tools/evidence/cov_one.sh over every program",
  "for p in \"$CD\"/app/cbl/*.[cC][bB][lL] \"$CD\"/app/app-*/cbl/*.[cC][bB][lL]; do \"$C/tools/evidence/cov_one.sh\" \"$p\"; done > \"$OUT/cov_all.txt\" && "
  "echo \"kinds: $(awk '{sub(/^kind=/, \"\", $2); print $2}' \"$OUT/cov_all.txt\" | LC_ALL=C sort | uniq -c | awk '{printf \"%s %s, \", $2, $1}')"
  "$(awk '$2 == \"kind=batch\" {b++; if ($4 == \"fe=ok\") fe++; if ($4 == \"fe=ok\" && $5 == \"unsupported=0\") u0++; if ($6 == \"resolves=yes\") rs++; "
  "if ($4 == \"fe=ok\" && $5 == \"unsupported=0\" && $6 == \"resolves=yes\") {cov++; split($3, a, \"=\"); ln += a[2]}} "
  "END {printf \"| batch %d: front end ok %d, 0 unsupported %d, resolve %d, covered %d (%d non-comment lines)\", b, fe, u0, rs, cov, ln}' \"$OUT/cov_all.txt\")\"",
  timeout=3600)
R("CV.lines", S, "Non-comment lines of the 14 programs of kind batch (copybooks not counted)", "{out} lines",
  "tools/evidence/cobol_lines.awk",
  "cd \"$CD/app/cbl\" && awk -f \"$C/tools/evidence/cobol_lines.awk\" CBACT01C.cbl CBACT02C.cbl CBACT03C.cbl CBACT04C.cbl CBCUS01C.cbl CBEXPORT.cbl CBIMPORT.cbl CBSTM03A.CBL CBSTM03B.CBL CBTRN01C.cbl CBTRN02C.cbl CBTRN03C.cbl COBSWAIT.cbl CSUTLDTC.cbl")

# ---------------------------------------------------------------- validation
S = "validation"
PRE = 'mkdir -p "$OUT/tmp" && export TMPDIR="$OUT/tmp" && cd "$OUT" && '
TALLY = "jq -s -c 'group_by(.status) | map({(.[0].status): length}) | add'"
R("V0", S, "GnuCOBOL flags of the semantics tests: TRUNC(STD) runs use -std=ibm -fbinary-truncate -fno-arithmetic-osvs; TRUNC(BIN) runs use -std=ibm -fno-arithmetic-osvs",
  "{out}", "tools/difftest/difftest.py (COBC_FLAGS)",
  "/usr/bin/grep -A1 '^COBC_FLAGS' \"$C/tools/difftest/difftest.py\" | tr -s ' ' | tr '\\n' ' '")
VAL = [  # (id, claim, command, result file, number of cases)
    ("V.dt_std", "Random programs (MOVE, COMPUTE, ADD/SUBTRACT, MULTIPLY, DIVIDE, IF on numeric and alphanumeric items), TRUNC(STD): the Lean semantics on the generated IR against GnuCOBOL on the generated COBOL, 200 programs, seed 11; every IF / ON SIZE ERROR / NOT ON SIZE ERROR outcome is also recorded in its statement's own byte (OTRACE), so no later statement hides it; status per program",
     'python3 -I -B "$C/tools/difftest/difftest.py" --n 200 --seed 11 --out "$OUT/dt_std" > "$OUT/dt_std.log"', "dt_std", 200),
    ("V.dt_bin", "The same generator, TRUNC(BIN): 200 programs, seed 12",
     'python3 -I -B "$C/tools/difftest/difftest.py" --n 200 --seed 12 --trunc bin --out "$OUT/dt_bin" > "$OUT/dt_bin.log"', "dt_bin", 200),
    ("V.ct", "Random control flow (PERFORM THRU, nested PERFORM, GO TO, EXIT, sections): 100 programs, seed 13",
     'python3 -I -B "$C/tools/difftest/ctrltest.py" --n 100 --seed 13 --out "$OUT/ct" > "$OUT/ct.log"', "ct", 100),
    ("V.dt_fe", "Front end: the IR that tools/cobolfe extracts from each generated COBOL program, run by the semantics, against GnuCOBOL and the generated IR: 100 programs, seed 14",
     'python3 -I -B "$C/tools/difftest/difftest.py" --n 100 --seed 14 --frontend --out "$OUT/dt_fe" > "$OUT/dt_fe.log"', "dt_fe", 100),
    ("V.ct_fe", "Front end on random control flow: 60 programs, seed 15",
     'python3 -I -B "$C/tools/difftest/ctrltest.py" --n 60 --seed 15 --frontend --out "$OUT/ct_fe" > "$OUT/ct_fe.log"', "ct_fe", 60),
    ("V.ft", "Files (sequential and indexed: OPEN, READ, WRITE, REWRITE, DELETE, FILE STATUS): 100 programs, seed 101; after every statement both sides DISPLAY its file status, phrase marker and record areas, compared line by line, also before an abend; generator classes for documented GnuCOBOL deviations are not generated (row V.ft_excl)",
     'python3 -I -B "$C/tools/difftest/filetest.py" --n 100 --seed 101 --out "$OUT/ft" > "$OUT/ft.log"', "ft", 100),
    ("V.us", "UNSTRING (25 statements per program; the counts and the tally start from non-zero values; every receiver, delimiter, count, the pointer, the tally and the overflow phrase are displayed): 60 programs, seed 1",
     'python3 -I -B "$C/tools/difftest/unstringtest.py" --n 60 --seed 1 --out "$OUT/us" > "$OUT/us.log"', "us", 60),
    ("V.in", "INSPECT (25 statements per program; the TALLYING counters start from non-zero values): 60 programs, seed 2; class G-lead not generated (row V.in_excl)",
     'python3 -I -B "$C/tools/difftest/inspecttest.py" --n 60 --seed 2 --out "$OUT/in" > "$OUT/in.log"', "in", 60),
    ("V.st", "STRING with value delimiters and POINTER (25 statements per program): 60 programs, seed 5",
     'python3 -I -B "$C/tools/difftest/stringtest.py" --n 60 --seed 5 --out "$OUT/st" > "$OUT/st.log"', "st", 60),
    ("V.ex_acctint", "ACCTINT: its IR against its COBOL source under GnuCOBOL, 100 random records",
     'python3 -I -B "$C/examples/acctint/validate.py" --n 100 --out "$OUT/ex_acctint" > "$OUT/ex_acctint.log"', "ex_acctint", 100),
    ("V.ex_binary", "BINCNT: its IR against its COBOL source under GnuCOBOL, 100 random inputs",
     'python3 -I -B "$C/examples/binary/validate.py" --n 100 --out "$OUT/ex_binary" > "$OUT/ex_binary.log"', "ex_binary", 100),
    ("V.ex_recsum", "RECSUM: its IR against its COBOL source under GnuCOBOL, 100 random files of 0 to 30 records (the output records; WS-COUNT is counted but never written, so no run observes it without changing the proved program)",
     'python3 -I -B "$C/examples/recsum/validate.py" --n 100 --out "$OUT/ex_recsum" > "$OUT/ex_recsum.log"', "ex_recsum", 100),
    ("V.tt", "Lean transcriptions of AcctInt.java and the Rust rewrite against the real Java (javac/java) and Rust (rustc, from $HOME/.cargo/bin) code: 500 random inputs",
     'PATH="$HOME/.cargo/bin:$PATH" python3 -I -B "$C/tools/targettest/targettest.py" --n 500 --out "$OUT/tt" > "$OUT/tt.log"', "tt", 500),
    ("V.pos", "Indexed files in dynamic access, the file position indicator: 20 hand-made scenarios of START, READ NEXT, keyed READ, WRITE and DELETE (after OPEN and START the record found is read next, after a READ the next higher key)",
     'python3 -I -B "$C/tools/difftest/pos_check.py" "$C" "$OUT/pos" > "$OUT/pos.log"', "pos", 20),
    ("V.fpos51", "Indexed files in dynamic access: random START, READ NEXT, keyed READ, WRITE, REWRITE and DELETE before, at and after the reading position (the M-pos class included): 100 programs, seed 51",
     'python3 -I -B "$C/tools/difftest/filetest2_pos.py" --root "$C" --out "$OUT/fpos51" --n 100 --seed 51 > "$OUT/fpos51.log"', "fpos51", 100),
    ("V.fpos52", "The same generator: 100 programs, seed 52",
     'python3 -I -B "$C/tools/difftest/filetest2_pos.py" --root "$C" --out "$OUT/fpos52" --n 100 --seed 52 > "$OUT/fpos52.log"', "fpos52", 100),
    ("V.c5", "Files whose record descriptions have different lengths (no RECORD clause; RECORD VARYING DEPENDING ON without bounds; RECORD CONTAINS m TO n with the shorter record first): 3 hand-written programs",
     'python3 -I -B "$C/tools/difftest/c5_check.py" --root "$C" --out "$OUT/c5" > "$OUT/c5.log"', "c5", 3),
    ("V.ins.s1", "INSPECT on signed numeric DISPLAY items (PIC S9(7) with a trailing or leading embedded sign or a trailing or leading separate sign, and PIC S9(5)V99): TALLYING, REPLACING and CONVERTING with digit patterns, BEFORE / AFTER INITIAL; the item is inspected without its sign and keeps it; 25 statements per program, counters from non-zero values; class G-convempty not generated: 60 programs, seed 1",
     'python3 -I -B "$C/tools/difftest/inspecttest_signed.py" --n 60 --seed 1 --out "$OUT/ins_s1" > "$OUT/ins_s1.log"', "ins_s1", 60),
    ("V.ins.s2", "The same generator: 60 programs, seed 2",
     'python3 -I -B "$C/tools/difftest/inspecttest_signed.py" --n 60 --seed 2 --out "$OUT/ins_s2" > "$OUT/ins_s2.log"', "ins_s2", 60),
] + [
    (f"V.cov.{name}.s{seed}", f"{desc}: 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/cov/cov_{tester}.py" --root "$C"{part} --n 60 --seed {seed} --out "$OUT/cov_{name}_s{seed}" > "$OUT/cov_{name}_s{seed}.log"',
     f"cov_{name}_s{seed}", 60)
    for name, tester, part, desc in [
        ("f1inp", "f1inp", "", "Interleaved input files read through the semantics' input streams (hand-built IR)"),
        ("f1multi", "f1multi", "", "Interleaved sequential files through the front end, reads past the end (10, 46)"),
        ("f2vary", "f2vary", "", "RECORD VARYING sequential and indexed files at the minimum, the maximum, between and below: READ, WRITE, REWRITE, DELETE"),
        ("f3round", "f3round", "", "ROUNDED and ROUNDED MODE (7 modes) on COMPUTE, ADD, SUBTRACT, MULTIPLY and DIVIDE"),
        ("f3prohib", "f3prohib", "", "ROUNDED MODE PROHIBITED against an exact-rational oracle (model only: GnuCOBOL raises the size error on every such statement)"),
        ("f4lit", "f4disp", " --part lit", "DISPLAY of unsigned numeric literals (GnuCOBOL -std=ibm: the digits without the decimal point)"),
        ("f4items", "f4disp", " --part items", "DISPLAY of unsigned COMP-3 and of unsigned and SIGN SEPARATE DISPLAY items"),
        ("f5str", "f5str", "", "STRING with every delimiter BY SIZE and no POINTER (the front end's static path)"),
    ]
    for seed in (1, 2)
] + [
    (f"V.fn.{name}.s{seed}", f"{desc}: 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/fntest_{name}.py" --root "$C" --n 60 --seed {seed} --out "$OUT/fn_{name}_s{seed}" > "$OUT/fn_{name}_s{seed}.log"',
     f"fn_{name}_s{seed}", 60)
    for name, desc in [
        ("num", "Intrinsic functions FACTORIAL (0 to 28), SUM and RANGE (1 to 5 integer and decimal arguments of mixed scales: items, table elements, literals) and sums of LENGTH values, in COMPUTE and on both sides of IF relations, TRUNC(STD); 20 statements per program, every result displayed"),
        ("date", "Integer-date functions INTEGER-OF-DATE, DATE-OF-INTEGER, INTEGER-OF-DAY and DAY-OF-INTEGER on literals and items inside their domains (1601-01-01 to 9999-12-31, weighted to month, year and century boundaries; integer dates 1 to 3067671), of a shifted INTEGER-OF-DATE, differences of integer dates and IF, TRUNC(STD); 20 statements per program, every result displayed"),
        ("alnum", "Intrinsic functions UPPER-CASE, LOWER-CASE and REVERSE of items, reference-modified items, literals and a nested function, moved to shorter, equal and longer receivers, displayed, in LENGTH and in IF comparisons, and WHEN-COMPILED (its length, its first two characters, equality with a copy), ASCII; 20 statements per program"),
    ]
    for seed in (1, 2)
] + [
    (f"V.{name}.s{seed}", f"{desc}: 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/{tester}.py" --n 60 --seed {seed} --out "$OUT/{name}_s{seed}" > "$OUT/{name}_s{seed}.log"',
     f"{name}_s{seed}", 60)
    for name, tester, desc in [
        ("after", "aftertest", "PERFORM VARYING ... AFTER with two and three levels, inline and out of line, WITH TEST BEFORE and AFTER, FROM and BY reading other levels' variables, UNTIL conditions on any level, 6 PERFORM statements per program: the variables in every iteration and after the loop; the 3-level TEST BEFORE case where GnuCOBOL departs from IBM (G-after3) is left out"),
        ("ae", "aetest", "MOVE and INITIALIZE into alphanumeric-edited items (PICTURE A, X, 9 with B, 0, / insertion): alphanumeric, numeric, figurative, group, edited, reference-modified, subscripted and function senders, several receivers, table elements and group members; 25 statements per program, every result displayed and compared"),
        ("decl", "decltest", "DECLARATIVES: 1 to 3 USE AFTER STANDARD EXCEPTION/ERROR PROCEDURE declaratives on file names or open modes over 1 to 3 sequential or indexed files (some without FILE STATUS), and 10 to 24 OPEN, CLOSE, READ, WRITE, REWRITE, DELETE and START statements per program, many ending with status 10, 22, 23 or 41 to 49, with and without AT END / INVALID KEY; every statement displays a trace number, the file status items and the number of declaratives run, and every declarative its own number and the same items, compared line by line, and both sides end the same way (normal end, or an abend with the same status); the cases where GnuCOBOL departs from IBM are left out: G-closedmode (an error on a file that is not open, with only an open-mode declarative) and G-readfail (READ NEXT after a failed keyed READ)"),
        ("opt", "opttest", "SELECT OPTIONAL: 1 to 3 sequential or indexed (ACCESS RANDOM, DYNAMIC, SEQUENTIAL) files, at least one OPTIONAL and absent when the program starts (cobolrun --absent), the others created with 0 to 4 records by a GnuCOBOL setup program (cobolrun --inputs), and 10 to 24 OPEN (every mode), CLOSE, READ, READ NEXT, keyed READ, START, WRITE, REWRITE and DELETE statements per program, then every file closed and read back (OPEN INPUT gives 00, or 05 for a file still absent); every statement displays a trace number, every file status and every record area, compared line by line, and both sides end normally; the cases where GnuCOBOL departs from IBM are left out: G-optkey (a keyed READ as the first READ of an absent OPTIONAL file opened INPUT gives 10, IBM 23) and G-readfail (READ NEXT after a failed keyed READ)"),
        ("nest", "nestedtest", "Nested and batched programs: a main program with 1 to 3 contained programs (some COMMON, some containing a program) and up to 2 further separately compiled programs (END PROGRAM), GLOBAL data, condition names, indexes and a GLOBAL file with a USE GLOBAL declarative, local names hiding global ones, one EXTERNAL record described differently in several programs, CALL by literal and identifier of every program IBM's naming rules let a program call, BY REFERENCE (the same item twice too) and BY CONTENT arguments, ON EXCEPTION / ON OVERFLOW / NOT ON EXCEPTION, INITIAL programs, CANCEL by literal and identifier, RETURN-CODE passed back by separately compiled programs; every program displays what it sees, compared line by line, and the model ends with STOP RUN; the cases where GnuCOBOL 3.2 departs from IBM (G-declcall, G-initialrc, G-cancelcommon) are left out"),
        ("alt", "alttest", "Alternate record keys and SAME RECORD AREA: 2 or 3 indexed files (ACCESS DYNAMIC with a unique and / or a WITH DUPLICATES alternate key; ACCESS SEQUENTIAL with a duplicates key, a unique one or none; ACCESS RANDOM with a duplicates and / or a unique key), created with 0 to 7 records by a GnuCOBOL setup program (cobolrun --inputs), some sharing a record area, and 15 to 35 START (=, >, >=, NOT < on the record key, an alternate key or a leading part of one), READ NEXT, keyed READ by every key, WRITE, REWRITE and DELETE statements per program, then every file read in the order of each of its keys; every statement displays a trace number, every file status and every record area, compared line by line, and both sides end normally; every status equals the tester's mirror of IBM's rules, 02 included, which GnuCOBOL never gives (G-dup02: the model's predicted 02 read as 00); left out where GnuCOBOL departs from IBM: G-rwalt (ACCESS SEQUENTIAL REWRITE with a unique alternate key fails with 22), G-rw21 (REWRITE of a missing record key gives 21), G-readfail (READ NEXT after a failed keyed READ)"),
        ("dyn", "dyntest", "Indexed files in ACCESS DYNAMIC around a failed keyed READ: 2 or 3 indexed files (F1 ACCESS DYNAMIC with no alternate key, a unique alternate key the program never names, or a WITH DUPLICATES alternate key; F2 ACCESS DYNAMIC; most programs F3 ACCESS SEQUENTIAL), created with 0 to 7 records by a GnuCOBOL setup program (cobolrun --inputs), and 15 to 35 START (=, >, >=, NOT < on the record key, value in the file or not), READ NEXT, keyed READ (key in the file or not), WRITE, REWRITE, DELETE and CLOSE + OPEN statements per program, READ NEXT weighted up after a failed keyed READ, then every file read in record-key order; every statement displays a trace number, every file status and every record area; every status equals the tester's mirror of IBM's rules (46 for a READ NEXT after a failed keyed READ, after a failed START and after the at-end condition) and every line equals GnuCOBOL's (the mirror's 02 read as 00, G-dup02), except the file status and record area of a READ NEXT after a failed keyed READ (G-readfail: GnuCOBOL continues where it was, repeats or skips records, or gives 46), compared with the mirror only"),
        ("reckey", "reckeytest", "RECORD KEY and ALTERNATE RECORD KEY clauses in every spelling IBM allows (RECORD [KEY] [IS] k: 4 spellings; ALTERNATE [RECORD] [KEY] [IS] a: 6) and RECORD DELIMITER on sequential files, in filetest.py's random file programs (keyed READs of every key value in the epilogue): trace lines and final storage, as V.ft"),
        ("rmexpr", "rmexprtest", "Reference modifiers written as integer arithmetic (+, -, *, parentheses, unary signs) on literals and at most one integer item (DISPLAY, COMP, COMP-3, MOVEd between statements), on an alphanumeric item, a numeric DISPLAY item, a group and a table element: DISPLAY of the substring, comparison with a literal, MOVE into the substring; 25 statements per program"),
        ("sw", "swtest", "Switches: 1 to 4 of UPSI-0 to UPSI-7 in random SPECIAL-NAMES spellings ([IS] mnemonic, ON / OFF [STATUS] [IS] in either order), condition names in IF (NOT, AND, OR) and EVALUATE, SET mnemonic-name ... TO ON / OFF with several names and phrases; start states as COB_SWITCH_n for GnuCOBOL and the same environment or --switch (against the opposite environment) for the front end; 20 statements per program"),
        ("initrepl", "initrepltest", "INITIALIZE ... REPLACING of 1 to 5 categories BY literals, figurative constants and items, plain INITIALIZE, and pairs where INITIALIZE X and INITIALIZE X REPLACING every category BY SPACES / ZERO must leave the same bytes, on groups with FILLER items, a REDEFINES child, a table, a redefined group and items of every category; the whole storage compared after each step; G-fillersep (GnuCOBOL initializes FILLER items with a separate sign) and negative zero left out"),
        ("ix", "indextest", "Index data items (USAGE INDEX) and index names: SET of index names and index data items (also elements of a table of index data items), SET UP / DOWN BY, comparisons of index data items with index names and with each other, table elements through index names, SEARCH VARYING an index data item, PERFORM VARYING index names (inline and out of line, TEST BEFORE and AFTER, with AFTER), a group MOVE with index data items at the same offsets, INITIALIZE of groups holding them, LENGTH OF and the field after an index data item; 20 steps per program, every index value displayed; each index data item meets one element length; the cases where GnuCOBOL departs from IBM (G-initindex, G-search-varying) are left out"),
        ("initptr", "initptrtest", "INITIALIZE on groups with POINTER items (next to other items, in a table, in a nested group, under a REDEFINES child, at the group's level), whose bytes are preset: plain INITIALIZE of 1 or 2 identifiers, REPLACING of 1 to 5 categories, and pairs plain / REPLACING every category BY SPACES or ZERO; the program with pointers against its twin with a FILLER PIC X(4) for each pointer (the same layout; FILLER items are not initialized either), the twin against GnuCOBOL: the whole storage and the DISPLAY lines (GnuCOBOL's pointers have 8 bytes, so the pointer program itself is not run there)"),
    ]
    for seed in (1, 2)
] + [
    (f"V.init.s{seed}", "INITIALIZE of reference-modified identifiers (alphanumeric, alphabetic, numeric, numeric-edited, alphanumeric-edited and group items, table elements; literal and data-name positions, with and without a length), of identifiers with a REDEFINES clause (elementary and group, levels 01 and 05, a table element, inside a redefining group), of items under a redefining item and of plain items, one to three identifiers per statement; 20 statements per program, every record displayed through alphanumeric views after each one and compared"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/inittest.py" --root "$C" --n 60 --seed {seed} --out "$OUT/init_s{seed}" > "$OUT/init_s{seed}.log"',
     f"init_s{seed}", 60)
    for seed in (1, 2)
] + [
    ("V.ix.mixed", "The index-data-item generator with one step per program that moves a value between an index data item and an index name of another element length (IBM keeps displacements, GnuCOBOL occurrence numbers): the model stops with unsupported at the first statement that touches the items exchanging values with it, and agrees with GnuCOBOL before: 60 programs, seed 3",
     'python3 -I -B "$C/tools/difftest/indextest.py" --n 60 --seed 3 --mixed --out "$OUT/ix_mixed" > "$OUT/ix_mixed.log"', "ix_mixed", 60),
] + [
    (f"V.coll.s{seed}", "PROGRAM COLLATING SEQUENCE and ALPHABET: most programs name an ALPHABET of literals (strings, THROUGH ranges either way, ALSO groups, HIGH-VALUE, LOW-VALUE, SPACE, QUOTE, ZERO, or ordinal numbers), the others are in native order (no PROGRAM COLLATING SEQUENCE, maybe an unused ALPHABET, or NATIVE, STANDARD-1, STANDARD-2); relation conditions between items of different lengths, reference-modified items, a group, literals, figurative constants and an unsigned numeric item, level-88 values and THRU ranges, EVALUATE THRU, serial SEARCH and PERFORM UNTIL conditions, MOVE / VALUE HIGH-VALUE and LOW-VALUE, alphanumeric MAX, MIN, ORD-MAX and ORD-MIN (ties included), numeric ORD-MAX and ORD-MIN, INSPECT of characters sharing a position, ORD and CHAR in native order; 20 statements per program, every outcome displayed; G-alsolit and G-ordchar left out"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/colltest.py" --root "$C" --n 60 --seed {seed} --out "$OUT/coll_s{seed}" > "$OUT/coll_s{seed}.log"',
     f"coll_s{seed}", 60)
    for seed in (1, 2)
] + [
    (f"V.class.s{seed}", "SPECIAL-NAMES CLASS and class conditions with a class name: 2 to 4 classes of alphanumeric and hexadecimal literals, THROUGH ranges either way (alphanumeric, hexadecimal, ordinal), ordinal positions and SPACE, ZERO, QUOTE, HIGH-VALUE, LOW-VALUE, some programs under PROGRAM COLLATING SEQUENCE NATIVE or STANDARD-1; tested on alphanumeric, alphabetic, unsigned, embedded-sign and separate-sign numeric DISPLAY, numeric-edited, group and member items, table elements (literal and data-name subscripts) and reference modifications (literal, data-name start, to the end), with NOT, AND, OR, NUMERIC, ALPHABETIC and relations, in IF, EVALUATE TRUE and PERFORM UNTIL; 20 steps per program, every outcome displayed"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/classtest.py" --root "$C" --n 60 --seed {seed} --out "$OUT/class_s{seed}" > "$OUT/class_s{seed}.log"',
     f"class_s{seed}", 60)
    for seed in (1, 2)
] + [
    (f"V.dpc.s{seed}", "DECIMAL-POINT IS COMMA, CURRENCY SIGN and BLANK WHEN ZERO on numeric items: programs with DECIMAL-POINT IS COMMA, CURRENCY SIGN IS one letter, both or neither; 8 random numeric-edited pictures written in the program's roles (fixed and floating $, + and -, Z, *, 9, the insertion symbols , and B, and 0 and / between 9s, . or V places, + - CR DB on the right, BLANK WHEN ZERO, repetition factors); MOVE of literals with decimal places (also ,5) and of items, COMPUTE and ADD ... GIVING into edited items, MOVE ZERO, IF with decimal literals, VALUE clauses with decimal literals, a 9(4) BLANK WHEN ZERO item; 20 steps per program; no truncation; G-ins0 left out"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/dpctest.py" --root "$C" --n 60 --seed {seed} --out "$OUT/dpc_s{seed}" > "$OUT/dpc_s{seed}.log"',
     f"dpc_s{seed}", 60)
    for seed in (1, 2)
] + [
    (f"V.sysin.s{seed}", "ACCEPT from the system input device (IBM format 1: records read until the receiving area is filled, the last one truncated; at the end of the input space padding after data, the area unchanged before any; no editing or checking): alphanumeric, alphabetic, unsigned numeric DISPLAY, group, table element (data-name and literal subscripts), reference-modified, JUSTIFIED, numeric-edited and alphanumeric-edited receivers and the COBSWAIT shape (X(8) moved to 9(8) COMP), with no FROM, FROM SYSIN, FROM SYSIPT and FROM mnemonic names of both; decks of fixed-length records (LRECL 80 or random, the lines padded) or variable-length records; programs ending at the end of the input, with a receiver longer than its record, or with a non-digit card in the COBSWAIT shape (the model stops with invalidData); every model line equals the IBM mirror computed by the tester; lines of the classes where GnuCOBOL departs from IBM (G-sysin-eof, G-sysin-long, G-sysin-num, G-sysin-edit, G-sysin-just) are checked against the mirror only, the others against GnuCOBOL (standard input = the deck)"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/sysintest.py" --root "$C" --n 60 --seed {seed} --out "$OUT/sysin_s{seed}" > "$OUT/sysin_s{seed}.log"',
     f"sysin_s{seed}", 60)
    for seed in (1, 2)
] + [
    (f"V.odo.{tag}", desc + f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/odotest.py" --root "$C" --n 60 --seed {seed}{flag} --out "$OUT/odo_{tag}" > "$OUT/odo_{tag}.log"',
     f"odo_{tag}", 60)
    for tag, seed, flag, desc in [
        (tag, seed, "", "OCCURS DEPENDING ON, against GnuCOBOL -std=ibm -fno-odoslide: two variable-occurrence tables per program, one whose object is a record of its own (a header and the table in a group, directly or one level down; elements of 1 to 3 characters with or without a PIC 99 field; integer-1 0 to 2) and one whose object lies in its group before the table (ASCENDING KEY, INDEXED BY), and in some programs a sequential file whose record holds such a table; 20 steps per program: MOVE to the objects, group MOVEs with the groups as senders and receivers (a receiver containing its object gets the maximum length), element MOVEs below and above the object, numeric statements on elements, comparisons, INSPECT, STRING, UNSTRING, DISPLAY and reference modification of the groups, serial SEARCH and SEARCH ALL, PERFORM VARYING over the current occurrences, WRITE and READ ... INTO of variable-length records; every step displays both groups whole; the cases where GnuCOBOL departs from IBM (G-odostring, G-odounstring: STRING / UNSTRING INTO a group containing its object fills the current length, IBM the maximum length) are left out")
        for tag, seed in (("s1", 1), ("s2", 2))
    ] + [("mixed", 3, " --mixed", "The OCCURS DEPENDING ON generator with one step per program that sets an object outside integer-1 to integer-2 and references its table (IBM: the behavior is undefined): the model stops with a range fault at that reference and agrees with GnuCOBOL before it")]
] + [
    (f"V.corr.s{seed}", "MOVE, ADD and SUBTRACT CORRESPONDING and level-66 RENAMES: records of random groups "
     "(three of them and a table element derived from one by dropped, added, renamed, retyped, reordered items, "
     "items made FILLER or OCCURS, moved one group level down; REDEFINES and USAGE INDEX items), CORRESPONDING "
     "between records, same-named groups and table elements (literal and data-name subscripts), ADD and SUBTRACT "
     "with and without ROUNDED, ON SIZE ERROR alone or with NOT ON SIZE ERROR, every elementary item of the "
     "receiver displayed after each statement; level-66 items (an elementary item, a group, THROUGH ranges) "
     "written by MOVE and ADD, read by MOVE and comparisons, their record displayed; 12 steps per program; the "
     "cases where GnuCOBOL departs from IBM (C1, G-corrindex, G-renusage, moves IBM's table forbids) are left out"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/corrtest.py" --root "$C" --n 60 --seed {seed} --k 12 --out "$OUT/corr_s{seed}" > "$OUT/corr_s{seed}.log"',
     f"corr_s{seed}", 60)
    for seed in (1, 2)
] + [
    (f"V.crepl.s{seed}", "COPY ... REPLACING, COPY ... OF / IN and REPLACE, programs of 2 to 5 units with their copybooks, GnuCOBOL -std=ibm -I the program's directory: :TAG: and (TAG) placeholders glued to the text on either side (also a copybook copied twice with two tags, and replaced by a REPLACE statement around the COPY), LEADING / TRAILING partial words (whole words, lower case) in COPY REPLACING and REPLACE, literal and numeric operands and operands that must not match (the other quotation mark, 07 for 7), qualified and subscripted identifier operands, pseudo-text of several words across lines with comment lines in the copybook and in the COPY statement and separator commas and semicolons between words, pictures and level numbers, REPLACE in the PROCEDURE DIVISION (matches across line breaks, a second REPLACE replacing the first, REPLACE OFF), COPY REPLACING under REPLACE (COPY first), nested COPY (outer or inner REPLACING), COPY OF / IN a library directory next to a copybook of the same name, COPY 'name', SUPPRESS, operand order and no re-comparison, a COPY statement inside a statement; every DISPLAY compared; the cases where GnuCOBOL departs from IBM (G-sepcomma, G-parencomma, G-litcase, G-dline, G-ptblank, G-pwblank, an empty partial-word-2) are left out"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/copyrepltest.py" --root "$C" --n 60 --seed {seed} --out "$OUT/crepl_s{seed}" > "$OUT/crepl_s{seed}.log"',
     f"crepl_s{seed}", 60)
    for seed in (1, 2)
] + [
    (f"V.deedit.s{seed}", "De-editing MOVE (IBM: a numeric-edited sender is de-edited and its unedited value moved to numeric and numeric-edited receivers; to other receivers it is alphanumeric): three numeric-edited senders and a table element with random pictures (fixed and floating $ + -, CR, DB, Z, *, B 0 / , insertion, . or V, BLANK WHEN ZERO); each step MOVEs a value into a sender, the sender to 1-3 receivers (signed and unsigned numeric DISPLAY, COMP-3, numeric-edited, with an alphanumeric item or a group in some steps; reference-modified senders to the alphanumeric item) and the expected value to twins of the receivers (the IBM mirror: the model's receivers equal the twins on every step); some programs end with content that no value edits to (the model stops with invalidData); 15 steps per program; where GnuCOBOL's de-editing departs from IBM (G-deedit-db, G-deedit-zero) the receivers are checked against the mirror only; pictures and values where GnuCOBOL's or the model's editing departs from IBM (G-edittrunc, G-editins, G-editsigncur, G-editfloatsign, M-editpoint, negative zero) are left out"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/deedittest.py" --root "$C" --n 60 --seed {seed} --out "$OUT/deedit_s{seed}" > "$OUT/deedit_s{seed}.log"',
     f"deedit_s{seed}", 60)
    for seed in (1, 2)
] + [
    (f"V.editpt.s{seed}", "Numeric editing with simple insertion characters around the decimal point (IBM: a B 0 / , within or to the immediate right of a zero-suppression or floating insertion string is part of the string; with a zero integer part one right before the decimal point is replaced and a floating symbol goes immediately left of the point): eight numeric-edited items with random pictures (a Z, * or floating $ + - integer part, mostly with no 9, B , 0 / inside it and right before the point, in a fifth of the pictures a B 0 / left of the string, which is not part of it, . or V, places 9 or Z / *, a 0 or / right after the point, B 0 / between places, a fixed $, + - CR DB, BLANK WHEN ZERO); each of 20 steps MOVEs a value, mostly with a zero integer part, into an item and displays it, some steps also MOVE the item to a numeric item (de-editing) and the value to its twin; an item with a 0 or / in or right after its string, which GnuCOBOL keeps where IBM replaces it (G-editins), is checked against the IBM mirror (a twin with ',' in those positions, which GnuCOBOL edits as IBM does); de-editing lines of G-deedit-zero and G-deedit-db steps are checked against the twin only; G-editptb, G-edittrunc, G-editsigncur, G-editfloatsign and negative zero are left out"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/editpttest.py" --root "$C" --n 60 --seed {seed} --out "$OUT/editpt_s{seed}" > "$OUT/editpt_s{seed}.log"',
     f"editpt_s{seed}", 60)
    for seed in (1, 2)
] + [
    (f"V.just.s{seed}", "MOVE into JUSTIFIED RIGHT items, group senders above all (IBM: a group move is treated as an alphanumeric-to-alphanumeric elementary move, so a JUSTIFIED receiver right-justifies a group and truncates it on the left; a group receiver is filled from the left whatever JUSTIFIED members it has): three groups of one to three alphanumeric or unsigned numeric members with VALUEs, JUSTIFIED RIGHT receivers PIC X(n) and A(n), a table of JUSTIFIED elements, a group with a JUSTIFIED member, an alphanumeric item without JUSTIFIED; each of 20 steps moves literals into group members, or a group to one to three receivers (JUSTIFIED items, table elements with literal and data-name subscripts, the member, the group, the plain item), or another sender (a reference modification of a group, a member, a literal, SPACE, ZERO, QUOTE, ALL literal) to a JUSTIFIED item, and displays every receiver"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/justtest.py" --root "$C" --n 60 --seed {seed} --out "$OUT/just_s{seed}" > "$OUT/just_s{seed}.log"',
     f"just_s{seed}", 60)
    for seed in (1, 2)
] + [
    (f"V.displit.s{seed}", "DISPLAY with numeric literal operands (IBM: a numeric literal's decimal point is an assumed one, not taking up a character position, and its size is the number of its digits, so an unsigned literal shows its digits as written: 1.5 as 15, 0.05 as 005, .5 as 5; IBM gives no form for a sign, so a DISPLAY of a signed numeric literal is unsupported): a few alphanumeric and unsigned numeric items with VALUEs; each of 15 steps DISPLAYs one to four operands among alphanumeric literals, unsigned numeric literals (integers and decimals with leading and trailing zeros and a leading point, up to 18 digits), the items, ZERO and SPACE; a quarter of the programs also DISPLAY a signed literal, which the front end must report as unsupported (ok-unsup)"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/displittest.py" --root "$C" --n 60 --seed {seed} --out "$OUT/displit_s{seed}" > "$OUT/displit_s{seed}.log"',
     f"displit_s{seed}", 60)
    for seed in (1, 2)
] + [
    (f"V.lc.s{seed}", "PICTURE character-strings that begin with a comma (IBM: the separator comma is a comma followed by a space, so a ',' right after PIC / PICTURE [IS] that a non-space follows begins the character-string: a simple insertion character left of every digit position, which is written, or under DECIMAL-POINT IS COMMA the decimal point): programs with six numeric-edited items whose pictures are ',' followed by 9s, a Z or * string or a floating $ + - string (with or without 9s after it), B or ',' between integer positions, . or V and places, a trailing + - CR DB, BLANK WHEN ZERO, the clause written PIC, PICTURE, PIC IS or PICTURE IS, each item with a twin without the comma (a quarter of the twins written PIC , body: a separator comma); a third of the programs under DECIMAL-POINT IS COMMA with pictures that begin with the decimal point (places 9, all Z, all *, B, a trailing sign, BLANK WHEN ZERO); each of 20 steps MOVEs a value into an item and its twin and displays both, some steps also MOVE the item to a numeric item (de-editing) and the value to its twin; every line equals GnuCOBOL's except where GnuCOBOL writes the leading ',' as a space (G-editlc), the model's line of an item with a twin equals the IBM mirror (the twin's GnuCOBOL line with ',' in front; a space or '*' when the whole item is blank or asterisks), and the de-edited value equals its twin"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/lctest.py" --root "$C" --n 60 --seed {seed} --out "$OUT/lc_s{seed}" > "$OUT/lc_s{seed}.log"',
     f"lc_s{seed}", 60)
    for seed in (1, 2)
] + [
    (f"V.close.s{seed}", "CLOSE ... REEL / UNIT [FOR REMOVAL | WITH NO REWIND], CLOSE ... WITH NO REWIND, CLOSE ... WITH LOCK and OPEN INPUT ... REVERSED (IBM: a disk file is a non-reel/unit file, so REEL / UNIT closes no volume: status 07, the file stays open and nothing else changes; WITH NO REWIND closes the file with 07; WITH LOCK closes a sequential or indexed file, 00, and every later OPEN of it gets 38; a file not open gives 42; a REWRITE right after REEL / UNIT gets 43; REVERSED does not apply to a direct-access device, so the model runs it only where that cannot matter: an OPEN that fails and a file of at most one record): 1 to 3 sequential files, most with a FILE STATUS item, some OPTIONAL and absent when the program starts (cobolrun --absent), in some programs an indexed file (ACCESS RANDOM), the others created with 0 to 4 records by a GnuCOBOL setup program (cobolrun --inputs), and 12 to 28 OPEN (every mode), OPEN INPUT ... REVERSED (files of 0 or 1 records, absent OPTIONAL, open and locked files), CLOSE, CLOSE ... REEL / UNIT in every spelling, CLOSE ... [WITH] NO REWIND, CLOSE ... [WITH] LOCK, READ (keyed for the indexed file), WRITE and REWRITE statements per program (a READ, a CLOSE ... REEL / UNIT and a REWRITE weighted up in I-O mode, and OPENs of a locked file), then every open file closed and every file read back (a locked one: OPEN INPUT, 38); files without FILE STATUS get only statements that succeed; every statement displays a trace number, every file status and every record area, compared line by line with GnuCOBOL, and every status the tester's IBM mirror predicts equals GnuCOBOL's; left out: G-lockclose (row V.close.gdep), G-open41 (filetest.py), CLOSE ... REEL / UNIT / NO REWIND of an absent OPTIONAL file opened INPUT and OPEN ... REVERSED of a file of two or more records (the model stops with unsupported, row V.close.unsup)"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/closetest.py" --root "$C" --n 60 --seed {seed} --out "$OUT/close_s{seed}" > "$OUT/close_s{seed}.log"',
     f"close_s{seed}", 60)
    for seed in (1, 2)
] + [
    (f"V.pow.s{seed}", "Exponentiation with an exponent that is an integral data item or expression, not a literal (IBM: fixed point, the power held with dmax decimal places, ir4; for a negative exponent 1 divided by ir4, again to dmax places, ir5; zero raised to a negative power a size error): COMPUTE into numeric receivers with 0 to 4 places of expressions with one or two such powers (bases: integer and decimal items, literals, sums, products, negations, a nested power; exponents: DISPLAY, COMP-3 and COMP items, sums, differences, negations, doubles), with ON SIZE ERROR / NOT ON SIZE ERROR, and IF relations and sign conditions with integer operands; each step sets its operands by MOVE; every line equals GnuCOBOL's line for the IBM mirror program (each power replaced by its IBM value computed by the tester) and GnuCOBOL's own line except in the classes where GnuCOBOL computes the power exactly (G-powtrunc, G-pownegdiv, G-pow0neg); a quarter of the programs end with a power the front end must keep unsupported (ROUNDED, a numeric-edited receiver, an exponent with decimal places or a division, a condition with a decimal operand, a function argument, a negative literal exponent, INTEGER of a decimal argument in the COMPUTE, a literal exponent over such a power: ok-unsup); 0 ** 0, exponents beyond 64 and intermediate results beyond 12 digits are left out"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/powtest.py" --root "$C" --n 60 --seed {seed} --out "$OUT/pow_s{seed}" > "$OUT/pow_s{seed}.log"',
     f"pow_s{seed}", 60)
    for seed in (1, 2)
] + [
    (f"V.dmax.{part}.s{seed}", desc + f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/dmaxtest.py" --part {part} --root "$C" --n 60 --seed {seed} --out "$OUT/dmax_{part}_s{seed}" > "$OUT/dmax_{part}_s{seed}.log"',
     f"dmax_{part}_s{seed}", 60)
    for part, desc in [
        ("all88", "Level-88 condition names with VALUE ALL literal (IBM: the figurative constant ALL literal, the literal repeated to the size of the conditional variable) next to literal values, THRU ranges, SPACE and ZERO, on alphanumeric items of 1, 4 and 7 characters, a group and a table element: IF, IF NOT, EVALUATE TRUE, SET ... TO TRUE (the item displayed after it) and relations with ALL literals; a fifth of the programs name a PROGRAM COLLATING SEQUENCE (an ALPHABET of the letters in reverse order); 20 steps per program; every model line and every GnuCOBOL line equals the line the tester computes from IBM's rules"),
        ("cond", "Arithmetic expressions with a division in conditions (IBM: an explicit relation takes as dmax the most decimal places of any operand of either comparand, divisors excluded, each relation of an abbreviated condition its own; a sign condition and an EVALUATE subject or object, which have no relational operator, the places of the expression's own operands; the quotient truncated): IF relations with the expression on either side (the other comparand a literal with places, a signed item or a sum), sign conditions, abbreviated relations, EVALUATE with the expression as the subject (literal and item objects, WHEN ... THRU, objects where the two readings part) or as an object; integer and decimal DISPLAY and COMP-3 items set by MOVE before each step; 20 steps per program; every model line equals the tester's IBM line, and every GnuCOBOL line (-std=ibm -fno-arithmetic-osvs: exact quotients) too, except in the class G-exactdiv (the outcome with exact quotients differs from IBM's)"),
        ("edited", "COMPUTE into a numeric-edited receiver (IBM: dmax counts the decimal places needed for the final result fields, a numeric-edited receiver's digit positions after the point included): edited pictures with 1 to 4 places, alone or with a numeric receiver of fewer places, expressions with a division (integer operands weighted), ROUNDED in a quarter of the steps, ON SIZE ERROR in some; each step sets its operands by MOVE; 20 steps per program; every model line equals GnuCOBOL's line for the IBM mirror program (each expression replaced by its IBM value computed by the tester) and GnuCOBOL's own line (-std=ibm -fno-arithmetic-osvs: exact quotients) except in the class G-exactdiv (a receiver stores another value with exact quotients)"),
        ("intfn", "COMPUTE with FUNCTION INTEGER or INTEGER-PART of a decimal item or sum, or MOD of integers, next to a division outside the function (IBM: an integer function contributes outer-dmax 0, its argument's places do not count), into receivers with 0 or 1 places (numeric, or numeric-edited); ROUNDED in a quarter of the steps, ON SIZE ERROR in some; each step sets its operands by MOVE; 20 steps per program; every model line equals GnuCOBOL's line for the IBM mirror program and GnuCOBOL's own line (-std=ibm -fno-arithmetic-osvs: exact quotients) except in the class G-exactdiv"),
        ("div", "COMPUTE with quotients carried by IBM's rule (\"(d2 - d1) or dmax, whichever is greater\" decimal places, d2 the dividend's and d1 the divisor's, one more with ROUNDED; truncated): a divisor with more places than dmax, a product as the dividend, nested quotients, a quotient by a sum, two quotients, a quotient alone (where the resolver keeps its old scale, which stores the same values), one or two numeric receivers with 0 to 4 places, in a fifth of the steps a numeric-edited one, operands and receivers with few places weighted (dmax below a divisor's places, where IBM's rule and the old one part), ROUNDED in a quarter of the steps, ON SIZE ERROR in some; each step sets its operands by MOVE; 20 steps per program; every model line equals GnuCOBOL's line for the IBM mirror program and GnuCOBOL's own line (-std=ibm -fno-arithmetic-osvs: exact quotients) except in the class G-exactdiv"),
        ("fnarg", "COMPUTE with a division inside a function argument (IBM: an argument expression is computed with the function's inner-dmax, the most decimal places of that function's arguments, 0 for MOD, never with the statement's receivers, its other operands or its ROUNDED phrase; Language Reference: \"function evaluation is not affected by operations or operands outside the function\"): MAX, MIN, SUM, RANGE, REM, ABS, INTEGER and INTEGER-PART of an argument with a quotient (alone, by a product, plus or times an operand), some with a nested function as another argument, alone or times, plus, divided by or subtracted from an operand, and MOD of INTEGER or INTEGER-PART of such an argument; receivers with 2 or 4 places weighted, in a fifth of the steps a numeric-edited one, ROUNDED in a quarter of the steps, ON SIZE ERROR in some; each step sets its operands by MOVE; 20 steps per program; every model line equals GnuCOBOL's line for the IBM mirror program and GnuCOBOL's own line (-std=ibm -fno-arithmetic-osvs: exact quotients) except in the class G-exactdiv"),
        ("fncond", "The conditions of the cond row with a division inside a function argument in place of the quotient (IBM: such an argument takes the function's inner-dmax in a condition too, where the resolver before inr-fix gave it the dmax 0): IF relations with the expression on either side, sign conditions, abbreviated relations, EVALUATE with the expression as the subject or as an object; integer and decimal DISPLAY and COMP-3 items set by MOVE before each step; 20 steps per program; every model line equals the tester's IBM line, and every GnuCOBOL line (-std=ibm -fno-arithmetic-osvs: exact quotients) too, except in the class G-exactdiv"),
        ("rmode", "ROUNDED MODE, which Enterprise COBOL does not have (the model follows COBOL 2014; plain ROUNDED and TRUNCATION, IBM's two, in a fifth of the receivers): a COMPUTE whose whole expression is one quotient, into one or two receivers, rounds the exact quotient once into each receiver, as DIVIDE ... GIVING and DIVIDE ... INTO do; ROUNDED MODE PROHIBITED with ON SIZE ERROR a size error when the exact quotient has more places than the receiver; a quotient inside a larger expression keeps IBM's intermediate (max(d2 - d1, dmax) + 1 places, truncated) and the mode rounds the final value; numeric receivers with 0 to 4 places, in a fifth of the receivers a numeric-edited one; each step sets its operands by MOVE; 20 steps per program; every model line equals GnuCOBOL's line for the IBM mirror program (each receiver given its expected value) and GnuCOBOL's own line (-std=ibm -fno-arithmetic-osvs: exact quotients) except in the classes G-exactdiv and G-prohibited (GnuCOBOL raises the size error under PROHIBITED whenever the quotient has more places than the receiver, even all zero; the model only when the value cannot be stored exactly)"),
    ]
    for seed in (1, 2)
] + [
    (f"V.ir30.s{seed}", "Fixed-point intermediate results that can need more than 30 digits (IBM, compatibility mode: beyond 30 digits an intermediate result keeps 30-d integer and d decimal places when d <= dmax, i integer and 30-i decimal places when d > dmax and i + dmax <= 30, else 30-dmax integer and dmax decimal places; a cut integer digit that is not 0 gives message IGZ0036W, where the model stops with unsupported, as it does where IBM's text leaves the places open, e.g. ROUNDED): COMPUTE with products of 15- to 18-digit integer and decimal items (DISPLAY and COMP-3, signed and unsigned) times, plus or minus items and literals, sums of products, quotients of products, products of quotients, into one receiver (its final result is no intermediate result) or two (it is), ROUNDED in some steps; COMPUTE (A * B) * C with every decimal place of A and B used and a moderate C, drawn until IBM's cut of the product's decimal places shows in the receiver; IF relations of such expressions; MULTIPLY GIVING two receivers; FUNCTION REM (FUNCTION REM (A, B), C) and FUNCTION SUM of large items; ON SIZE ERROR in most steps; each step sets its operands by MOVE; 12 steps per program; a third of the programs end with a step where IBM cuts a nonzero integer digit or leaves the places open (ok-stop: the model's unsupported text and its earlier lines checked); every model line equals the line of the IBM mirror program (receivers set to the tester's IBM values) and GnuCOBOL's own line (-std=ibm -fno-arithmetic-osvs: exact) except in the classes G-ir30 (IBM's cut changes the value) and G-exactdiv"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/ir30test.py" --root "$C" --n 60 --seed {seed} --out "$OUT/ir30_s{seed}" > "$OUT/ir30_s{seed}.log"',
     f"ir30_s{seed}", 60)
    for seed in (1, 2)
] + [
    (f"V.powlit.s{seed}", "Powers by a literal exponent whose places reach 30 digits (IBM's exponentiation table, compatibility mode: d = d1 * n, i = i1 * n or for a literal base the integer digits of its power; i + d below 30, or 30 with an odd number of digits in the base, carried exactly; otherwise held as for an integral data-name exponent, with dmax decimal and 30-dmax integer places, where the model stops with unsupported beyond 30 digits; under ROUNDED from 28 digits on the places are open, where the model stops too): COMPUTE of a power of a decimal or integer item (DISPLAY and COMP-3, 2 to 18 digits), a literal (1.5, 1.01, 12.5, 2, 3) or a sum of two items, by exponents 2 to 64 chosen around 30 digits (30 with an odd and an even number of digits in the base), alone, times an item or literal, plus or minus an item, divided by an item or plus another power, into one or two numeric receivers with 0 to 9 places, ROUNDED in some steps, ON SIZE ERROR in most; COMPUTE of such a power times an item or literal, values drawn until IBM's cut of the power's decimal places shows in the receiver; IF relations with such powers; each step sets its operands by MOVE; 12 steps per program; a third of the programs end with a step where the power held with dmax places exceeds 30 digits or the places are open (ok-stop: the model's unsupported text and its earlier lines checked); every model line equals the line of the IBM mirror program and GnuCOBOL's own line (-std=ibm -fno-arithmetic-osvs: exact powers) except in the classes G-powlit (IBM's dmax places change the value), G-litpow64 (GnuCOBOL folds an integer literal ** literal in 64-bit binary, wrapping from 2 ** 63 on) and those of V.ir30"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/ir30test.py" --part powlit --root "$C" --n 60 --seed {seed} --out "$OUT/powlit_s{seed}" > "$OUT/powlit_s{seed}.log"',
     f"powlit_s{seed}", 60)
    for seed in (1, 2)
] + [
    (f"V.pow0.s{seed}", "Powers by the literal exponent 0 (IBM, Language Reference, Arithmetic expressions: the exponent of a zero base must be greater than zero, otherwise the size error condition exists; SIZE ERROR phrases: zero raised to zero power runs the ON SIZE ERROR imperative, whose receivers are not altered, and without a SIZE ERROR phrase the value returned is 1, with a message the model does not give; NOT ON SIZE ERROR runs only when no size error condition exists): COMPUTE of B ** 0 alone, plus an item, times 3 or subtracted from an item, B an item set to 0 in two fifths of the steps, the literal 0, 7 or 1.5, the difference of an item and itself or a sum, into one or two receivers, ROUNDED in some steps, ON SIZE ERROR in most, NOT ON SIZE ERROR alone in some (a nonzero base: the value 1, the phrase runs); IF relations with such a power; each step sets its operands by MOVE; 12 steps per program; a third of the programs end with a zero base under NOT ON SIZE ERROR alone, where the size error skips the phrase while the value 1 is stored, which the model does not represent (ok-stop: the model's unsupported text and its earlier lines checked); every model line equals the line of the IBM mirror program and GnuCOBOL's own line except in the classes G-pow00 (GnuCOBOL runs ON SIZE ERROR for a zero data base but stores 1) and G-litpow00 (GnuCOBOL folds the literal 0 ** 0 to 1 with no size error)"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/ir30test.py" --part pow0 --root "$C" --n 60 --seed {seed} --out "$OUT/pow0_s{seed}" > "$OUT/pow0_s{seed}.log"',
     f"pow0_s{seed}", 60)
    for seed in (1, 2)
] + [
    (f"V.c30.s{seed}", "The composite of operands of ADD, SUBTRACT, MULTIPLY and DIVIDE (IBM, Language Reference, Arithmetic statement operands: the operands aligned at the decimal point and superimposed, for ADD and SUBTRACT all operands except those following GIVING, for MULTIPLY all receiving data items, for DIVIDE all receiving data items except the REMAINDER data item; with ARITH(COMPAT) at most 30 digits; the front end makes a statement beyond it unsupported): ADD TO, ADD GIVING, SUBTRACT FROM, SUBTRACT FROM GIVING, MULTIPLY BY, MULTIPLY GIVING, DIVIDE INTO and DIVIDE GIVING with items of 2 to 18 digits whose integer and decimal places add up to 30 or more and literals (digits as written), one or two receivers, no ROUNDED, ON SIZE ERROR in most steps, composites of at most 30 digits (30 in about a third); each step sets its operands by MOVE; 12 steps per program; a third of the programs end with a statement whose composite exceeds 30 digits (ok-stop: the front end's unsupported text with the composite's digits, the model's earlier lines checked); every model line equals GnuCOBOL's own line"
     f": 60 programs, seed {seed}",
     f'python3 -I -B "$C/tools/difftest/ir30test.py" --part c30 --root "$C" --n 60 --seed {seed} --out "$OUT/c30_s{seed}" > "$OUT/c30_s{seed}.log"',
     f"c30_s{seed}", 60)
    for seed in (1, 2)
]
for vid, claim, cmd, d, n in VAL:
    # the value: the tally, the number of cases (exactly 0 .. n-1) and the tester's exit status
    # (0 or 1, no traceback), checked by val_check.sh
    R(vid, S, claim + " (per-case results: $OUT/" + d + "/results.jsonl)", "{out}", cmd.split('"')[1].replace("$C/", ""),
      PRE + cmd + f' ; rc=$? ; "$C/tools/evidence/val_check.sh" {n} "$rc" "$OUT/{d}.log" "$OUT/{d}/results.jsonl"',
      timeout=3600, must=r"^\{.*\} " + str(n) + r" cases, tester exit [01]$")
R("V.ft_excl", S, "File-test generator classes left out because GnuCOBOL deviates from IBM there (class and reason in the source)",
  "{out}", f"tools/difftest/filetest.py:{line_of('tools/difftest/filetest.py', '^    .G-dup21.:')}",
  "/usr/bin/grep -oE '^    \"G-[a-z0-9]+\"' \"$C/tools/difftest/filetest.py\" | tr -d ' \"' | tr '\\n' ' '")
R("V.in_excl", S, "INSPECT-test classes for GnuCOBOL deviations (G-lead is left out by default)", "{out}",
  f"tools/difftest/inspecttest.py:{line_of('tools/difftest/inspecttest.py', '^    .G-lead.:')}",
  "/usr/bin/grep -oE '^    \"G-[a-z0-9]+\"' \"$C/tools/difftest/inspecttest.py\" | tr -d ' \"' | tr '\\n' ' '")
R("V.st_negzero", S, "Status ok-negzero (counted as agreeing): every field decodes to the same value and the bytes differ only in the sign of a zero, where GnuCOBOL keeps the negative sign and the model stores zero as positive (packed D vs C, separate '-' vs '+', overpunch 'p' vs '0'; V.dt_std cases 93, 120, 148 at 2306Z); lines that set it",
  "{out}", "tools/difftest/difftest.py",
  "/usr/bin/grep -n 'return \"negzero\"' \"$C/tools/difftest/difftest.py\" | cut -d: -f1 | tr '\\n' ' '")
R("V.st_packedfc", S, "Status ok-packed-fc (counted as agreeing): every field decodes to the same value and a signed packed field differs only in its sign nibble, F in GnuCOBOL (kept after a MOVE from an unsigned packed item) and C in the model (V.dt_std cases 65, 81 and V.dt_fe cases 12, 13 at 2306Z); line that sets it",
  "{out}", "tools/difftest/difftest.py",
  "/usr/bin/grep -n 'return \"packed-fc\"' \"$C/tools/difftest/difftest.py\" | cut -d: -f1")
R("V.st_bytes", S, "Status mismatch-bytes (a failure): every field decodes to the same value, but the bytes differ in any other way; line that sets it",
  "{out}", "tools/difftest/difftest.py",
  "/usr/bin/grep -n 'return (\"mismatch-bytes\"' \"$C/tools/difftest/difftest.py\" | cut -d: -f1")
R("V.st_trace", S, "Statuses mismatch-trace and abend-trace-mismatch (failures): the file tests' DISPLAY lines after every statement differ, with equal final storage or before an abend at the same statement with the same status; lines that set them",
  "{out}", "tools/difftest/filetest.py",
  "/usr/bin/grep -n 'tagged(\"mismatch-trace\"\\|tagged(\"abend-trace-mismatch\"' \"$C/tools/difftest/filetest.py\" | cut -d: -f1 | tr '\\n' ' '")
R("V.st_recursion", S, "Status lean-unsupported-recursion (declined, not compared): the program re-enters an active PERFORM, which the model reports as unsupported (implementation-specific on IBM); line that sets it",
  "{out}", "tools/difftest/ctrltest.py",
  "/usr/bin/grep -n 'return (\"lean-unsupported-recursion\", None)' \"$C/tools/difftest/ctrltest.py\" | cut -d: -f1")
R("V.st_okabend", S, "Status ok-abend (counted as agreeing): GnuCOBOL and the model stop at the same statement with the same I/O status, and the DISPLAY lines of the statements before it agree; line that sets it",
  "{out}", "tools/difftest/filetest.py",
  "/usr/bin/grep -n 'return (\"ok-abend\", None)' \"$C/tools/difftest/filetest.py\" | cut -d: -f1")
R("V.st_resume", S, "Status lean-unsupported-resume (declined, not compared): control reaches the end of a paragraph whose return slot belongs to an abandoned PERFORM; IBM would resume that PERFORM, which the model reports as unsupported; line that sets it",
  "{out}", "tools/difftest/ctrltest.py",
  "/usr/bin/grep -n 'return (\"lean-unsupported-resume\", None)' \"$C/tools/difftest/ctrltest.py\" | cut -d: -f1")
R("V.dt_bin_mm", S, "The 3 mismatches of V.dt_bin (cases 101, 130 and 197, kept as tools/difftest/bin_cases/T00101.cob, T00130.cob and T00197.cob): a binary item holds a value outside its PICTURE. GnuCOBOL DISPLAYs the full binary value but uses it truncated to the PICTURE digits in arithmetic (101: N4 = 5367323.33 + N2 with N2 = -15755.407 instead of -1015755.407; 197: N5 = 284683.386 - N2 with N2 = -326483.8 instead of -61326483.8; 130: N5 PIC S9(1) COMP holds 1999, and in one ADD N5 TO N6 N4 GnuCOBOL adds 9 to N6, so no size error and NOT ON SIZE ERROR runs, but 1999 to N4; minimal reproduction t130x.cob). The model uses the full binary value (under TRUNC(BIN) binary items are not truncated to their PICTURE): N6 overflows and ON SIZE ERROR runs. Case 130 shows only in the per-statement outcome trace (OTRACE): a later IF overwrote the single FLAG byte of the 2306Z tester. README lists out-of-PICTURE binary reads under TRUNC(BIN) as not validated",
  "{out}", "tools/evidence/bin_trace.sh, tools/difftest/bin_cases/",
  '"$C/tools/evidence/bin_trace.sh"', must=r"^101: ")
R("V.hand", S, "Hand-written cases run by GnuCOBOL and by the front end + semantics: each program's header (GnuCOBOL exit status 0 and the model's normal end) and its DISPLAY lines, compared line by line: NEXT SENTENCE in inline PERFORMs, ALTER, serial SEARCH, SEARCH ALL",
  "{out}", "tools/difftest/{nextsent_cases/ns1.cob,alter_cases/alter1.cob,search_cases/srch1.cob,search_cases/srchall1.cob}",
  PRE + 'python3 -I -B "$C/tools/difftest/filetest.py" --out "$OUT/hand" --run "$C/tools/difftest/nextsent_cases/ns1.cob" "$C/tools/difftest/alter_cases/alter1.cob" "$C/tools/difftest/search_cases/srch1.cob" "$C/tools/difftest/search_cases/srchall1.cob" > "$OUT/hand.txt" 2>&1; '
  "awk -F'|' '/^== / {p++} /^   GnuCOBOL \\(rc / {if ($1 ~ /GnuCOBOL \\(rc 0\\)/ && $2 ~ /^ model via front end \\(stop:/) e++} "
  "/^(   |!! )/ && NF == 2 && $1 !~ /GnuCOBOL/ {n++; if (substr($0, 1, 3) == \"!! \") d++} "
  "END {print p + 0 \" programs, \" e + 0 \" end normally on both sides, \" n + 0 \" lines compared, \" d + 0 \" differ\"}' \"$OUT/hand.txt\"",
  must=r"^4 programs, 4 end normally on both sides, 28 lines compared, 0 differ$")
R("V.hand_fes", S, "Hand-written cases run by GnuCOBOL and by the front end + semantics, compared line by line as in V.hand: VALUE ALL ZERO on numeric items of every usage and in a level 88, reference modifiers written as integer arithmetic, FILLER items in INITIALIZE and INITIALIZE ... REPLACING",
  "{out}", "tools/difftest/{value_cases/vallzero1.cob,refmod_cases/rmconst1.cob,initrepl_cases/fil1.cob}",
  PRE + 'python3 -I -B "$C/tools/difftest/filetest.py" --out "$OUT/hand_fes" --run "$C/tools/difftest/value_cases/vallzero1.cob" "$C/tools/difftest/refmod_cases/rmconst1.cob" "$C/tools/difftest/initrepl_cases/fil1.cob" > "$OUT/hand_fes.txt" 2>&1; '
  "awk -F'|' '/^== / {p++} /^   GnuCOBOL \\(rc / {if ($1 ~ /GnuCOBOL \\(rc 0\\)/ && $2 ~ /^ model via front end \\(stop:/) e++} "
  "/^(   |!! )/ && NF == 2 && $1 !~ /GnuCOBOL/ {n++; if (substr($0, 1, 3) == \"!! \") d++} "
  "END {print p + 0 \" programs, \" e + 0 \" end normally on both sides, \" n + 0 \" lines compared, \" d + 0 \" differ\"}' \"$OUT/hand_fes.txt\"",
  must=r"^3 programs, 3 end normally on both sides, 31 lines compared, 0 differ$")
R("V.swchk", S, "Switch cases outside V.sw (tools/difftest/switch_checks.sh on tools/difftest/switch_cases/): the IBM profile ignores COB_SWITCH_n and takes --switch; a condition name qualified by its mnemonic name; SET of a switch condition name TO TRUE is unsupported; SWITCH-n is no IBM switch name; GnuCOBOL's SWITCH-1 and SWITCH-36 against GnuCOBOL -std=cobol85; --switch wins over the environment; bad option and environment values refused; link.py refuses two programs that use one switch: the summary line",
  "{out}", "tools/difftest/switch_checks.sh",
  PRE + 'bash "$C/tools/difftest/switch_checks.sh" "$OUT/swchk" > "$OUT/swchk.txt" 2>&1; tail -n 1 "$OUT/swchk.txt"',
  must=r"^switch checks: 0 failed$")
R("V.irchk", S, "INITIALIZE forms that stay unsupported or are rejected (tools/difftest/initrepl_checks.sh on initrepl_cases/irunsup1.cob and irbadby1.cob): WITH FILLER, TO VALUE, THEN TO DEFAULT, REPLACING of a reference-modified, data-name-subscripted or pointer identifier, BY an item with a data-name subscript or reference modification or in the identifier's storage, each named; BY a group item rejected: the summary line",
  "{out}", "tools/difftest/initrepl_checks.sh",
  PRE + 'bash "$C/tools/difftest/initrepl_checks.sh" "$OUT/irchk" > "$OUT/irchk.txt" 2>&1; tail -n 1 "$OUT/irchk.txt"',
  must=r"^initialize checks: 0 failed$")
R("V.ptrchk", S, "Plain INITIALIZE of identifiers with POINTER items against the lines IBM's rule 1a gives (tools/difftest/initptr_checks.sh on initrepl_cases/ptr1.cob, ptr2.cob, ptr3.cob): pointers kept by plain INITIALIZE and by REPLACING, alphanumeric-edited items edited in the MOVEs that replace the INITIALIZE, an identifier whose pointer lies only under a REDEFINES child left to the resolver, INITIALIZE of a pointer and REPLACING of a condition name named unsupported (model only: GnuCOBOL's pointer has 8 bytes): the summary line",
  "{out}", "tools/difftest/initptr_checks.sh",
  PRE + 'bash "$C/tools/difftest/initptr_checks.sh" "$OUT/ptrchk" > "$OUT/ptrchk.txt" 2>&1; tail -n 1 "$OUT/ptrchk.txt"',
  must=r"^pointer checks: 0 failed$")
R("V.stm", S, "CBSTM03A + CBSTM03B on CardDemo's data: the semantics (ASCII IR from the unmodified sources) against GnuCOBOL compiling CBSTM03B and CBSTM03A without lines 266-291 (z/OS control-block walk); records of both output files compared byte by byte, the walk's 11 DISPLAY lines against the lines that follow from the constructed address space (computed without the model), and GnuCOBOL's exit status against the model's RETURN-CODE",
  "{out}", "tools/evidence/stm_check.sh, tools/difftest/stm_ascii.py, stm_gnucobol.sh, stm_compare.py",
  '"$C/tools/evidence/stm_check.sh"', timeout=1800, must=r"\bAGREE$")
COLL_HAND = ["v_collate1", "v_collate2", "v_filekey", "v_std2"]
R("V.coll.hand", S, "Hand-written PROGRAM COLLATING SEQUENCE cases run by GnuCOBOL and by the front end + semantics (colltest.py --run), compared line by line: an ALPHABET of literals and figurative constants with SPACE sharing a position (padding spaces), a MAX tie, INSPECT; NC219A's alphabet with THROUGH, ALSO and a two-character literal, HIGH-VALUE and LOW-VALUE in VALUE, MOVE, DISPLAY, comparisons and level 88, EVALUATE THRU; indexed-file keys in binary order (READ NEXT, START); STANDARD-2 with ORD, CHAR, MAX, MIN, ORD-MAX and ORD-MIN",
  "{out}", "tools/difftest/coll_cases/{" + ",".join(f + ".cob" for f in COLL_HAND) + "}",
  PRE + 'python3 -I -B "$C/tools/difftest/colltest.py" --root "$C" --out "$OUT/coll_hand" --run '
  + " ".join(f'"$C/tools/difftest/coll_cases/{f}.cob"' for f in COLL_HAND) + ' > "$OUT/coll_hand.txt" 2>&1; '
  "awk '/^== / {p++; if ($NF == \"ok\") o++} /^(   |!! )/ {n++; if (substr($0, 1, 3) == \"!! \") d++} "
  "END {print p + 0 \" programs, \" o + 0 \" ok, \" n + 0 \" lines compared, \" d + 0 \" differ\"}' \"$OUT/coll_hand.txt\"",
  must=r"^4 programs, 4 ok, 70 lines compared, 0 differ$")
R("V.coll.gdep", S, "The cases colltest.py leaves out, run as in V.coll.hand (status, then the labels of the lines that differ): G-alsolit (GnuCOBOL decides = and <> between two literals by their bytes, ignoring ALSO: L01 L02 L03), G-ordchar (ORD and CHAR in native order under an ALPHABET of literals: O1 O2 O3 H1 H2 H3), and SEARCH ALL with an alphanumeric KEY under a PROGRAM COLLATING SEQUENCE, where the model stops with unsupported (lean-signal)",
  "{out}", "tools/difftest/coll_cases/{g_alsolit.cob,g_ordchar.cob,u_searchall.cob}",
  PRE + 'python3 -I -B "$C/tools/difftest/colltest.py" --root "$C" --out "$OUT/coll_gdep" --run '
  + " ".join(f'"$C/tools/difftest/coll_cases/{f}.cob"' for f in ["g_alsolit", "g_ordchar", "u_searchall"])
  + ' > "$OUT/coll_gdep.txt" 2>&1; '
  "awk '/^== / {n = split($0, a, \"/\"); f = a[n]; sub(/:.*/, \"\", f); printf \"%s%s %s\", (np++ ? \"; \" : \"\"), f, $NF; next} "
  "/^!! / {split(substr($0, 4), b, \" \"); printf \" %s\", b[1]} END {print \"\"}' \"$OUT/coll_gdep.txt\"",
  must=r"^g_alsolit\.cob mismatch L01 L02 L03; g_ordchar\.cob mismatch O1 O2 O3 H1 H2 H3; u_searchall\.cob lean-signal$")
SYSIN_HAND = ["g_sysin_edit", "g_sysin_empty", "g_sysin_eof", "g_sysin_just", "g_sysin_long", "g_sysin_num",
              "i_cobswait_bad", "n_nodevice", "v_cobswait", "v_sysin_pad"]
R("V.sysin.hand", S, "Hand-written ACCEPT FROM SYSIN cases run by GnuCOBOL (standard input = the deck) and by the front end + semantics (cobolrun --sysin = the deck's records; sysintest.py --run), per case the model's end and the number of lines that differ: COBSWAIT's statements on CardDemo's WAITSTEP card and a short record at the end of the input agree; the GnuCOBOL departures G-sysin-edit, -eof, -just, -long, -num and the empty variable-length record (IBM leaves the area unchanged) differ as documented; a non-digit card in the COBSWAIT shape stops the model with invalidData; no system input device stops it with unsupported",
  "{out}", "tools/difftest/sysin_cases/{" + ",".join(f + ".cob" for f in SYSIN_HAND) + "}",
  PRE + 'python3 -I -B "$C/tools/difftest/sysintest.py" --root "$C" --out "$OUT/sysin_hand" --run '
  + " ".join(f'"$C/tools/difftest/sysin_cases/{f}.cob"' for f in SYSIN_HAND) + ' > "$OUT/sysin_hand.txt" 2>&1; '
  "awk '/^== / {if (np++) printf \"%s %d; \", f, d; n = split($2, a, \"/\"); f = a[n]; sub(/:$/, \"\", f); "
  "s = $4; sub(/^fault:Cobol[.]Fault[.]/, \"\", s); sub(/^stop:.*/, \"stop\", s); f = f \" \" s; d = 0; next} "
  "/^!! / {d++} END {printf \"%s %d\\n\", f, d}' \"$OUT/sysin_hand.txt\"",
  must=r"^g_sysin_edit\.cob stop 2; g_sysin_empty\.cob stop 1; g_sysin_eof\.cob stop 2; g_sysin_just\.cob stop 1; "
  r"g_sysin_long\.cob stop 1; g_sysin_num\.cob stop 1; i_cobswait_bad\.cob invalidData 1; n_nodevice\.cob unsupported 1; "
  r"v_cobswait\.cob stop 0; v_sysin_pad\.cob stop 0$")
R("V.acceptday", S, "ACCEPT FROM DAY, DAY YYYYDDD and DAY-OF-WEEK (tools/difftest/acceptday_check.sh on accept_cases/acceptday1.cob): GnuCOBOL's values agree with its DATE YYYYMMDD of the same run by INTEGER-OF-DATE, and the model's values at four clock readings (2024-12-31, 2000-02-29, 2001-01-01, 2026-10-27) are those date(1) gives, in numeric and alphanumeric receivers: the summary line",
  "{out}", "tools/difftest/acceptday_check.sh",
  PRE + 'bash "$C/tools/difftest/acceptday_check.sh" "$OUT/acceptday" > "$OUT/acceptday.txt" 2>&1; tail -n 1 "$OUT/acceptday.txt"',
  must=r"^acceptday checks: 0 failed$")
R("V.crepl.hand", S, "Hand-written COPY / REPLACE cases run by GnuCOBOL and by the front end + semantics (copyrepltest.py --run, each case copied into $OUT with its copybooks), compared line by line: IBM's COPY examples 2, 3, 5, 6, 7 and 8 (no blanks inside the delimiters, no OCCURS DEPENDING ON) and IBM's REPLACE example with LEADING ==XX-== BY ==WS-== in place of an empty partial word, plus COPY OF a library directory",
  "{out}", "tools/difftest/copyrepl_cases/{v_ibmex.cob,v_replace.cob}",
  PRE + 'python3 -I -B "$C/tools/difftest/copyrepltest.py" --root "$C" --out "$OUT/crepl_hand" --run '
  '"$C/tools/difftest/copyrepl_cases/v_ibmex.cob" "$C/tools/difftest/copyrepl_cases/v_replace.cob" > "$OUT/crepl_hand.txt" 2>&1; '
  "awk '/^[a-z_]+[.]cob: / {p++; if ($NF == \"ok\") o++} /^  [=!] / {n++; if (substr($0, 3, 1) == \"!\") d++} "
  "END {print p + 0 \" programs, \" o + 0 \" ok, \" n + 0 \" lines compared, \" d + 0 \" differ\"}' \"$OUT/crepl_hand.txt\"",
  must=r"^2 programs, 2 ok, 10 lines compared, 0 differ$")
R("V.contlit", S, "Alphanumeric literals continued over 3 and 4 lines whose middle lines end before column 72 (IBM: the spaces through column 72 of every continued line belong to the literal), one whose middle line reaches column 72, a comparison with a 3-line literal (as NIST SM201A COPY-TEST-11), a 4-line DISPLAY literal and a 3-line literal in a copybook (as NIST K6SCA's CCVS-C-1 header), run by GnuCOBOL and by the front end + semantics (copyrepltest.py --run), compared line by line",
  "{out}", "tools/difftest/cont_cases/{v_contlit.cob,CTLIT.cpy}",
  PRE + 'python3 -I -B "$C/tools/difftest/copyrepltest.py" --root "$C" --out "$OUT/contlit" --run '
  '"$C/tools/difftest/cont_cases/v_contlit.cob" > "$OUT/contlit.txt" 2>&1; '
  "awk '/^[a-z_]+[.]cob: / {p++; if ($NF == \"ok\") o++} /^  [=!] / {n++; if (substr($0, 3, 1) == \"!\") d++} "
  "END {print p + 0 \" programs, \" o + 0 \" ok, \" n + 0 \" lines compared, \" d + 0 \" differ\"}' \"$OUT/contlit.txt\"",
  must=r"^1 programs, 1 ok, 6 lines compared, 0 differ$")
CREPL_GDEP = ["g_sepcomma", "g_parencomma", "g_litcase", "g_dline", "g_ptblank", "g_pwblank", "g_emptypw", "v_ibmreplace"]
R("V.crepl.gdep", S, "The COPY / REPLACE cases copyrepltest.py leaves out, run as in V.crepl.hand (status, then the label of each line that differs, from the model's line): G-sepcomma (a pseudo-text-1 that is a separator comma: GnuCOBOL never matches it), G-parencomma (separator commas inside parentheses are not spaces for GnuCOBOL), G-litcase (GnuCOBOL matches a literal in either case), G-dline (GnuCOBOL drops debugging lines before matching), G-ptblank (GnuCOBOL keeps blanks at the ends of pseudo-text-2: cobc-error), G-pwblank (cobc rejects blanks inside partial-word delimiters), an empty partial-word-2 (cobc aborts) and IBM's REPLACE example verbatim (cobc aborts; the model prints IBM's documented lines Original: (Hello, Mom!) and Modified: Hello, COBOL!)",
  "{out}", "tools/difftest/copyrepl_cases/{" + ",".join(f + ".cob" for f in CREPL_GDEP) + "}",
  PRE + 'python3 -I -B "$C/tools/difftest/copyrepltest.py" --root "$C" --out "$OUT/crepl_gdep" --run '
  + " ".join(f'"$C/tools/difftest/copyrepl_cases/{f}.cob"' for f in CREPL_GDEP) + ' > "$OUT/crepl_gdep.txt" 2>&1; '
  "awk '/^[a-z_]+[.]cob: / {printf \"%s%s %s\", (np++ ? \"; \" : \"\"), substr($1, 1, length($1) - 1), $2; next} "
  "/^  ! / {i = index($0, \"model \\047\"); split(substr($0, i + 7), b, \" \"); printf \" %s\", b[1]} END {print \"\"}' \"$OUT/crepl_gdep.txt\"",
  must=r"^g_sepcomma\.cob mismatch L01 L03; g_parencomma\.cob mismatch L01 L02; g_litcase\.cob mismatch L02; g_dline\.cob mismatch L01 L02; g_ptblank\.cob cobc-error L01 L02 L03; g_pwblank\.cob cobc-error L01 L02 L03; g_emptypw\.cob cobc-error L01 L02; v_ibmreplace\.cob cobc-error Original: Modified:$")
# hand-written cases of classtest.py / dpctest.py (--run): the agreeing ones counted as in V.coll.hand, the others
# listed with their status and the labels of the lines that differ, as in V.coll.gdep
HAND_COUNT = ("awk '/^== / {p++; if ($NF == \"ok\") o++} /^(   |!! )/ {n++; if (substr($0, 1, 3) == \"!! \") d++} "
              "END {print p + 0 \" programs, \" o + 0 \" ok, \" n + 0 \" lines compared, \" d + 0 \" differ\"}'")
HAND_LIST = ("awk '/^== / {n = split($0, a, \"/\"); f = a[n]; sub(/:.*/, \"\", f); printf \"%s%s %s\", (np++ ? \"; \" : \"\"), f, $NF; next} "
             "/^!! / {split(substr($0, 4), b, \" \"); printf \" %s\", b[1]} END {print \"\"}'")
for vid, tester, cdir, files, how, claim, must in [
    ("V.class.hand", "classtest", "class_cases", ["v_class1", "v_class_seq"], HAND_COUNT,
     "Hand-written CLASS cases run by GnuCOBOL and by the front end + semantics (classtest.py --run), compared line by line: NC174A's classes (one character, THROUGH either way, a string of characters) and ordinal positions, a hexadecimal literal, SPACE, ZERO, QUOTE, HIGH-VALUE and LOW-VALUE as members; subjects alphanumeric, alphabetic, numeric with an embedded and a separate sign, numeric-edited, a group, a subscripted and a reference-modified item; NOT, AND, OR, EVALUATE, PERFORM UNTIL; and classes under PROGRAM COLLATING SEQUENCE NATIVE",
     r"^2 programs, 2 ok, 38 lines compared, 0 differ$"),
    ("V.class.unsup", "classtest", "class_cases", ["u_class_alphabet", "u_class_usage", "u_class_odo", "u_class_refvar"], HAND_LIST,
     "Class conditions with a class name that the front end makes unsupported, run as in V.class.hand (status per case): under a PROGRAM COLLATING SEQUENCE that is an ALPHABET of literals, on a binary item, on a group containing an OCCURS DEPENDING ON table, on a reference modification whose length is a data name",
     r"^u_class_alphabet\.cob fe-unsupported; u_class_usage\.cob fe-unsupported; u_class_odo\.cob fe-unsupported; u_class_refvar\.cob fe-unsupported$"),
    ("V.dpc.hand", "dpctest", "dpc_cases", ["v_dpc1", "v_currency1", "v_bwz1"], HAND_COUNT,
     "Hand-written DECIMAL-POINT IS COMMA, CURRENCY SIGN and BLANK WHEN ZERO cases run by GnuCOBOL and by the front end + semantics (dpctest.py --run), compared line by line: VALUE clauses with decimal-comma literals (also ,125), NC107A-style pictures (9.999.999,99, ZZ.ZZZ,99, **.***,99, *.***,** at zero, WWWWW, W9999, W.WWW,99, CR, DB, B, /, 0, BLANK WHEN ZERO, floating - and W), COMPUTE, IF and ADD ... GIVING with decimal-comma literals; CURRENCY SIGN IS W alone; BLANK WHEN ZERO on unsigned numeric items (MOVE, COMPUTE, INITIALIZE, comparison)",
     r"^3 programs, 3 ok, 50 lines compared, 0 differ$"),
    ("V.dpc.gdep", "dpctest", "dpc_cases", ["g_ins0", "g_floatcs", "g_bwzv", "u_dpc_display"], HAND_LIST,
     "The cases dpctest.py leaves out, run as in V.dpc.hand (status, then the labels of the lines that differ): G-ins0 (GnuCOBOL writes the simple insertion symbols 0 and / in or right after a floating or zero-suppression string, which IBM counts part of it), G-floatcs (COMPUTE / ADD ... GIVING into a floating currency string with an insertion symbol after its first symbol drops a digit in GnuCOBOL), G-bwzv (BLANK WHEN ZERO on a numeric item with V: GnuCOBOL one byte longer), and DISPLAY of a decimal literal under DECIMAL-POINT IS COMMA, unsupported in the front end",
     r"^g_ins0\.cob mismatch G01 G02 G03 G05 G10; g_floatcs\.cob mismatch H03 H04 H07; g_bwzv\.cob mismatch Z05 Z06; u_dpc_display\.cob fe-unsupported$"),
    ("V.editpt.hand", "editpttest", "editpt_cases", ["v_editpt1", "v_editlead"], HAND_COUNT,
     "Hand-written cases of insertion characters around the decimal point and left of the string run by GnuCOBOL and by the front end + semantics (editpttest.py --run), compared line by line: , and B right before the decimal point after a Z, *, $, + or - string with no 9 (with a zero integer part replaced, a floating symbol immediately left of the point), . and V, all-Z and all-* pictures; the theorem pictures -ZZZ,ZZZ,ZZZ.ZZ, +ZZZ,ZZZ,ZZZ.ZZ, Z(9).99- and 9(9).99-; controls with a 9 before the insertion character; 0 and / right after the point; pictures with no integer digit position (0.ZZ, /.**, B.**); B 0 / left of a Z, * or floating string, after a fixed sign or $ too (written), and a , right after a floating string's first symbol (part of the string)",
     r"^2 programs, 2 ok, 48 lines compared, 0 differ$"),
    ("V.editpt.gdep", "editpttest", "editpt_cases", ["g_editins_pt", "g_editptb"], HAND_LIST,
     "The editing cases where GnuCOBOL departs from IBM, run as in V.editpt.hand (status, then the labels of the lines that differ): G-editins (GnuCOBOL writes a 0 or / insertion character right before the decimal point or inside a zero-suppression or floating string, which IBM counts part of the string; editpttest.py checks these against its IBM mirror) and G-editptb (GnuCOBOL writes 0 for a B or , right after the decimal point when the integer part is a suppression or floating string and zero; left out of editpttest.py's generation)",
     r"^g_editins_pt\.cob mismatch I01 I02 I03 I04; g_editptb\.cob mismatch B01 B02 B03 B04 B05 B06 B07$"),
    ("V.just.hand", "justtest", "just_cases", ["v_just1"], HAND_COUNT,
     "Hand-written MOVEs into JUSTIFIED RIGHT items run by GnuCOBOL and by the front end + semantics (justtest.py --run), compared line by line: groups shorter and longer than the receiver into PIC X(n) JUSTIFIED and PIC A(n) JUST items and table elements (literal and data-name subscripts), into a JUSTIFIED member of a group and into the group itself, into a JUSTIFIED and a plain item at once; controls: a reference-modified group, a member, a literal, a numeric item, ALL literal, SPACES, ZERO",
     r"^1 programs, 1 ok, 17 lines compared, 0 differ$"),
    ("V.displit.hand", "displittest", "displit_cases", ["v_displit1"], HAND_COUNT,
     "Hand-written DISPLAYs of unsigned numeric literals run by GnuCOBOL and by the front end + semantics (displittest.py --run), compared line by line: 1.5, 0.05, .5, 100.00, 007.250, an 18-digit decimal, integers with and without leading zeros, literals among other operands, a literal alone",
     r"^1 programs, 1 ok, 12 lines compared, 0 differ$"),
    ("V.displit.unsup", "displittest", "displit_cases", ["u_displit_minus", "u_displit_plus"], HAND_LIST,
     "DISPLAY of a signed numeric literal (-1.5, +15), run as in V.displit.hand (status per case): the front end makes the statement unsupported (IBM gives no form for the sign; GnuCOBOL 3.2 writes -15 and +15)",
     r"^u_displit_minus\.cob fe-unsupported; u_displit_plus\.cob fe-unsupported$"),
    ("V.lc.hand", "lctest", "lc_cases", ["v_lc1", "v_lcsep"], HAND_COUNT,
     "Hand-written PICTURE character-strings that begin with a comma run by GnuCOBOL and by the front end + semantics (lctest.py --run), compared line by line: under DECIMAL-POINT IS COMMA pictures that begin with the decimal point (,99 ,999 ,9(4) ,ZZ ,** ,99+ ,99CR ,99 BLANK WHEN ZERO ,9B9 ,99-, written PIC, PICTURE, PIC IS and PICTURE IS; two of them de-edited); separator commas after PIC (a comma followed by a space or by the end of the line, PICTURE IS , 999) and commas the change does not touch (ZZ,ZZ9; PIC 9(3), VALUE; PIC X(4), VALUE); zero in all-Z, BLANK WHEN ZERO, all-* and all-floating items whose picture begins with a comma (the whole item spaces or asterisks)",
     r"^2 programs, 2 ok, 28 lines compared, 0 differ$"),
    ("V.lc.gdep", "lctest", "lc_cases", ["g_editlc"], HAND_LIST,
     "The GnuCOBOL departure G-editlc, run as in V.lc.hand (status, then the labels of the lines that differ): GnuCOBOL 3.2 writes a ',' that has no digit position on its left as a space, IBM writes the ',' (PIC ,ZZ9 ,999 ,**9 ,$$9 ,++9 ,--9, PICTURE IS ,ZZ9.99CR, ,9(3)V99, B,ZZ9, and a comma continued onto a continuation line); lctest.py checks such lines against its IBM mirror",
     r"^g_editlc\.cob mismatch L01 L02 L03 L04 L05 L06 L07 L08 L09 L10$"),
    ("V.close.hand", "closetest", "close_cases", ["v_closereel1", "v_closelock1", "v_closelock2", "v_openrev1"], HAND_COUNT,
     "Hand-written CLOSE ... REEL / UNIT, NO REWIND and LOCK and OPEN ... REVERSED cases run by GnuCOBOL and by the front end + semantics (closetest.py --run), compared line by line: REEL, UNIT, UNIT FOR REMOVAL, REEL NO REWIND, REEL WITH NO REWIND, UNIT REMOVAL on sequential files open OUTPUT, INPUT (also at the end of the file), I-O and EXTEND (07, the file stays open, READs and WRITEs go on where they were), a REWRITE right after the phrase (43); WITH NO REWIND and NO REWIND (07, closed: READ 47); WITH LOCK and LOCK on sequential and indexed files (00), then OPEN in every mode (38), READ (47), WRITE (48); two files with phrases in one CLOSE, files without FILE STATUS, closed files (42); OPEN of a locked file running the USE declarative of the file (as NIST SQ215A); OPEN INPUT ... REVERSED of an empty file and of a file of one record (00, read as by OPEN INPUT), of an absent OPTIONAL file (05), of an open file (41) and of a locked one (38)",
     r"^4 programs, 4 ok, 80 lines compared, 0 differ$"),
    ("V.close.unsup", "closetest", "close_cases", ["u_closereel_idx", "u_closenorew_idx", "u_closereel_absent", "u_closenorew_absent", "u_openrev_many", "u_openrev_idx", "u_openrev_out", "u_openrev_var"], HAND_LIST,
     "CLOSE and OPEN phrases where IBM rejects them or does not define the result, run as in V.close.hand (status per case): REEL and NO REWIND on an indexed file (IBM: not valid for VSAM files; the front end makes the statement unsupported; GnuCOBOL closes the file, 00) and on an absent OPTIONAL file opened INPUT (IBM gives no status for a file on no medium; the model stops with unsupported; GnuCOBOL closes the file, 00); OPEN INPUT ... REVERSED of a disk file of two records (IBM: REVERSED does not apply to a direct-access device, where the READs start is not said; the model stops with unsupported; GnuCOBOL ignores REVERSED), of an indexed file (not valid for VSAM files: the front end), after OUTPUT (REVERSED is a phrase of OPEN INPUT: the front end) and of a variable-length file (the record format must be fixed: the model)",
     r"^u_closereel_idx\.cob frontend-unsupported; u_closenorew_idx\.cob frontend-unsupported; u_closereel_absent\.cob lean-signal; u_closenorew_absent\.cob lean-signal; u_openrev_many\.cob lean-signal; u_openrev_idx\.cob frontend-unsupported; u_openrev_out\.cob frontend-unsupported; u_openrev_var\.cob lean-signal$"),
    ("V.close.gdep", "closetest", "close_cases", ["g_lockclose_seq", "g_lockclose_idx"], HAND_LIST,
     "G-lockclose, the case closetest.py leaves out, run as in V.close.hand (status, then the labels of the lines that differ): a CLOSE of a file closed WITH LOCK, where IBM gives 42 and the file stays locked; GnuCOBOL gives 00 and lifts the lock of a sequential file (L02, and L03's OPEN succeeds), and ends with a segmentation fault on an indexed file (gnucobol-abend)",
     r"^g_lockclose_seq\.cob mismatch L02 L03; g_lockclose_idx\.cob gnucobol-abend$"),
    ("V.pow.hand", "powtest", "pow_cases", ["v_pow1"], HAND_COUNT,
     "Hand-written powers with an exponent that is an integral data item or expression, run by GnuCOBOL and by the front end + semantics (powtest.py --run), compared line by line: NC250A's IF relations and sign conditions (10 ** THREE + 1, 9 ** TWO + (180 - 90)) and NC252A's COMPUTE (3 ** ATWO), exponents of every usage, a sum, a negation, a difference, a double and zero, decimal bases whose powers keep every place within dmax, negative exponents with exact quotients, a receiver overflowing into ON SIZE ERROR, a nested power, powers on both sides of a relation",
     r"^1 programs, 1 ok, 21 lines compared, 0 differ$"),
    ("V.pow.gdep", "powtest", "pow_cases", ["g_powtrunc", "g_pownegdiv", "g_pow0neg", "g_negcmp"], HAND_LIST,
     "The power cases where GnuCOBOL departs from IBM, run as in V.pow.hand (status, then the labels of the lines that differ; the model gives IBM's values): G-powtrunc (IBM truncates the power to dmax places, ir4, before using it: DA ** THREE * 10 with DA 1.5 and dmax 1 is 33.0, GnuCOBOL 33.7), G-pownegdiv (for a negative exponent IBM divides 1 by ir4 and keeps dmax places, a size error when ir4 is 0; GnuCOBOL divides 1 by the exact power) and G-pow0neg (zero raised to a negative power: IBM a size error, GnuCOBOL 0); and two comparison departures found while writing powtest.py, which it avoids: G-ucmpneg (an unsigned item compared with a negative value) and G-negconst (a negative literal or constant expression compared with an item), which GnuCOBOL compares as if the value were positive",
     r"^g_powtrunc\.cob mismatch T01 T02 T03 T04; g_pownegdiv\.cob mismatch U01 U02 U03 U04 U05; g_pow0neg\.cob mismatch Z01 Z02 Z03 Z04; g_negcmp\.cob mismatch N01 N02 N03 N04 N05$"),
    ("V.pow.unsup", "powtest", "pow_cases", ["u_pow_rounded", "u_pow_edited", "u_pow_decexp", "u_pow_divexp", "u_pow_decrel",
                                             "u_pow_fnarg", "u_pow_neglit", "u_pow_intfn", "u_pow_litover", "u_pow00", "u_pow65",
                                             "u_pow30"], HAND_LIST,
     "Powers the model leaves unsupported, run as in V.pow.hand (status per case): the front end keeps a ROUNDED receiver, a numeric-edited receiver, an exponent with decimal places or a division, a relation with a decimal operand, a power inside a function argument, a negative literal exponent, a COMPUTE with INTEGER of a decimal argument and a power under a literal exponent unsupported; the semantics stops with unsupported at 0 ** 0, at an exponent value of more than 64 and at a power of more than 30 digits",
     r"^u_pow_rounded\.cob fe-unsupported; u_pow_edited\.cob fe-unsupported; u_pow_decexp\.cob fe-unsupported; u_pow_divexp\.cob fe-unsupported; u_pow_decrel\.cob fe-unsupported; u_pow_fnarg\.cob fe-unsupported; u_pow_neglit\.cob fe-unsupported; u_pow_intfn\.cob fe-unsupported; u_pow_litover\.cob fe-unsupported; u_pow00\.cob lean-signal; u_pow65\.cob lean-signal; u_pow30\.cob lean-signal$"),
    ("V.dmax.hand", "dmaxtest", "dmax_cases", ["v_all88", "v_all88_nc250a", "v_cond1", "v_edited1", "v_intfn1", "v_div1", "v_fnarg1", "v_rmode1"], HAND_COUNT,
     "Hand-written cases of the dmax-fix corrections run by GnuCOBOL and by the front end + semantics (dmaxtest.py --run), compared line by line: level-88 VALUE ALL literal on X(4) (BACB is ALL 'BAC') and X(5) items, a group and a table element, with several values, IF, IF NOT, SET ... TO TRUE and an explicit relation with an ALL literal; NC250A's IF--TEST-28; divisions in conditions: relations whose other comparand gives the places (A / C > 1.5 with A 5, C 3 is true), the comparand on the left, sign conditions with the expression's own places, an abbreviated relation, EVALUATE TRUE, PERFORM UNTIL, an EVALUATE subject with as many places as its object; COMPUTE into numeric-edited receivers (ZZ9.99 = 10 / 4 is 2.50), two receivers, a signed edited receiver, ROUNDED, a product after the quotient; INTEGER, INTEGER-PART and MOD next to a division where GnuCOBOL gives IBM's values (INTEGER (1.2345) * (10 / 3) is 3), and of negative arguments; quotients by IBM's rule where GnuCOBOL agrees: a divisor with 3 places and dmax 0 (2 / 3.000 * 3 is 0), a product dividend (1.23 * 4.56 / 7 * 100 is 80.12: 4 places), CBACT04C's one division, ROUNDED; a division inside a function argument, computed with the function's inner-dmax, in a relation (MAX (D2 / D1, 0.05) > 0.65 with D2 1.00, D1 1.5 is true: 0.66), a sign condition and an abbreviated relation, and NIST IF133A's REM (3 / 2, .75), 0; COMPUTE of one quotient with ROUNDED MODE NEAREST-EVEN or AWAY-FROM-ZERO rounds the exact quotient as DIVIDE ... GIVING does (251 / 100 into PIC 9 is 3 with NEAREST-EVEN, 201 / 100 is 3 with AWAY-FROM-ZERO), plain ROUNDED and truncation alike",
     r"^8 programs, 8 ok, 60 lines compared, 0 differ$"),
    ("V.dmax.gdep", "dmaxtest", "dmax_cases", ["g_evalown", "g_intfn1", "g_div1", "g_fnarg1"], HAND_LIST,
     "The dmax cases where GnuCOBOL departs from IBM, run as in V.dmax.hand (status, then the labels of the lines that differ; the model gives IBM's values): G-evalown (IBM: an EVALUATE subject or object, compared with no relational operator, \"is evaluated without regard to the attributes of its comparand\"; GnuCOBOL -std=ibm gives the subject A / C the dmax of the relation with each object: WHEN 1.6 is taken for A 5, C 3, IBM takes WHEN 1); G-osvsdiv (GnuCOBOL -std=ibm keeps more places for a quotient than IBM's max(d2 - d1, dmax): COMPUTE N0 = A / B * 10 + FUNCTION INTEGER (D5) with A 10, B 3, D5 1.2345 into S9(5) is 31 on IBM, an integer function adding no places to dmax, 34 in GnuCOBOL; A1 / B3 * 30 with A1 1.0, B3 3.000 into 9(5)V99 is 9.90 on IBM, 2 places, 9.99 in GnuCOBOL; a nested quotient; a divisor scaled by P (9PP, no decimal places)); G-fnarg (GnuCOBOL -std=ibm keeps more places for a quotient inside a function argument than IBM's inner-dmax, the most decimal places of the function's arguments: MAX (D2 / N7, 0.05) with D2 1.00, N7 7 into S9(3)V9(6) is 0.140000 on IBM, 0.142857 in GnuCOBOL; ROUNDED does not reach the argument; a quotient of such a function; nested functions; an EVALUATE subject)",
     r"^g_evalown\.cob mismatch V01 V02 V04; g_intfn1\.cob mismatch F01 F02 F03 F04; g_div1\.cob mismatch G01 G02 G03; g_fnarg1\.cob mismatch G01 G02 G03 G04 G05$"),
    ("V.ir30.hand", "ir30test", "ir30_cases", ["v_ir30_1"], HAND_COUNT,
     "Hand-written intermediate results over 30 digits whose places IBM carries without changing the value, run by GnuCOBOL and by the front end + semantics (ir30test.py --run), compared line by line: a 32-digit product in a COMPUTE and in a condition (30 integer places kept), IF133A's FUNCTION REM (FUNCTION REM (A, B), B), MULTIPLY GIVING two receivers, IF110A's FACTORIAL (1) + B (the add is the final result), NC250A's 10 ** N + 1 > 1000, FUNCTION SUM of six 18-digit items, two 36-digit final results of MULTIPLY GIVING (the second stored by the truncation rules: no intermediate result, no 30-digit cut) and the quotient of a 36-digit product",
     r"^1 programs, 1 ok, 10 lines compared, 0 differ$"),
    ("V.ir30.gdep", "ir30test", "ir30_cases", ["g_ir30_1"], HAND_LIST,
     "G-ir30, run as in V.ir30.hand (status, then the labels of the lines that differ; the model gives IBM's values, GnuCOBOL computes exactly): A9 * B9 * C8 with 9V9 items and dmax 9 (A9 * B9 keeps 12 decimal places: 22330437.411120000, GnuCOBOL 22330437.411126352), A14 * B14 * 10 with 14V4 items and dmax 4 (4 places: 12.3450, GnuCOBOL 12.3454), IF A9 * B9 * C8 > 22330437.41112 (false on IBM, true in GnuCOBOL), (F1 * F3) / S2 * L13 (F1 * F3 keeps 17 places, so its quotient has 17: 420718385588.021730, GnuCOBOL 420718385588.021737)",
     r"^g_ir30_1\.cob mismatch G01 G02 G03 G04$"),
    ("V.ir30.unsup", "ir30test", "ir30_cases", ["u_ir30_cut", "u_ir30_rem", "u_ir30_open", "u_ir30_rndc", "u_ir30_comp5", "u_ir30_max", "u_ir30_divq", "u_ir30_divinto", "u_ir30_mulr"], HAND_LIST,
     "Intermediate results over 30 digits the model stops at, run as in V.ir30.hand (status per case, U01 the step not reached): a cut integer digit that is not 0 (IBM: message IGZ0036W, the program goes on; stop-cut) in a product and in the quotient step of FUNCTION REM; ROUNDED with places beyond dmax, ROUNDED whose places, one more at each operation, can reach 33 digits where the table gives 27, and a COMP-5 product (the places IBM carries are open; stop-open); FUNCTION MAX of an 18-digit integer and a 2.16 item (one result field of 34 digits), DIVIDE with two GIVING receivers, DIVIDE ... INTO ... ROUNDED without GIVING (each receiver a dividend) and MULTIPLY ... ROUNDED whose intermediate result can need more than 30 digits (stop-unsup)",
     r"^u_ir30_cut\.cob stop-cut U01; u_ir30_rem\.cob stop-cut U01; u_ir30_open\.cob stop-open U01; u_ir30_rndc\.cob stop-open U01; u_ir30_comp5\.cob stop-open U01; u_ir30_max\.cob stop-unsup U01; u_ir30_divq\.cob stop-unsup U01; u_ir30_divinto\.cob stop-unsup U01; u_ir30_mulr\.cob stop-unsup U01$"),
    ("V.powlit.hand", "ir30test", "powlit_cases", ["v_powlit_1"], HAND_COUNT,
     "Hand-written powers by a literal exponent whose places IBM carries without changing the value, run by GnuCOBOL and by the front end + semantics (ir30test.py --run), compared line by line: L4 ** 2 of a 15-digit L4 (30 digits, an odd number in the base: carried exactly) divided by 1000000000000, S1 ** 3, 1.5 ** 2 + S1, F2 ** 2 into 4 places (36 digits: held with dmax 4 places, all the receiver shows) and IF L1 ** 2 > 15241383935 (32 digits, dmax 0)",
     r"^1 programs, 1 ok, 5 lines compared, 0 differ$"),
    ("V.powlit.gdep", "ir30test", "powlit_cases", ["g_powlit_1"], HAND_LIST,
     "G-powlit and G-litpow64, run as in V.powlit.hand (status, then the labels of the lines that differ; the model gives IBM's values): F2 ** 2 * 10 with F2 = 1.2345 and dmax 4 (the power keeps 4 places: 15.2390, GnuCOBOL 15.2399), 1.5 ** 40 * 1000 with dmax 6 (11057332320.940000, GnuCOBOL 11057332320.940012), P10 ** 3 * 1000 of a 9(6)V9(4) item (30 digits, an even number in the base: 4 places, 1881.3000, GnuCOBOL 1881.3659), 2 ** 64 / 1000 (20 digits, exact: 18446744073709551; GnuCOBOL folds the literal power in 64-bit binary: 0)",
     r"^g_powlit_1\.cob mismatch G01 G02 G03 G04$"),
    ("V.powlit.unsup", "ir30test", "powlit_cases", ["u_powlit_cut", "u_powlit_rnd", "u_powlit_fn", "u_powlit_par"], HAND_LIST,
     "Powers by a literal exponent the model stops at, run as in V.powlit.hand (status per case, U01 the step not reached): L1 ** 2 of a 16-digit L1 held with dmax 0 places needs 32 digits (IBM truncates it with a message; stop-cutpow); S2 ** 14 under ROUNDED (28 digits, one more place might be carried: the row is open), F2 ** 2 in a FUNCTION MAX argument (dmax 4 or 6 by the open reading R1) and C5 ** 3 of a COMP-5 item that can hold 20 digits (30 to 60 digits: the row is open) (stop-openpow)",
     r"^u_powlit_cut\.cob stop-cutpow U01; u_powlit_rnd\.cob stop-openpow U01; u_powlit_fn\.cob stop-openpow U01; u_powlit_par\.cob stop-openpow U01$"),
    ("V.pow0.hand", "ir30test", "pow0_cases", ["v_pow0_1"], HAND_COUNT,
     "Hand-written powers by the literal exponent 0 whose value is 1, run by GnuCOBOL and by the front end + semantics (ir30test.py --run), compared line by line: a nonzero item base with ON SIZE ERROR, a zero base without ON SIZE ERROR (the value returned is 1), the literals 7 and 1.5 as bases, an expression base times 3, a zero base in a condition, the literal 0 as the base without ON SIZE ERROR",
     r"^1 programs, 1 ok, 8 lines compared, 0 differ$"),
    ("V.pow0.gdep", "ir30test", "pow0_cases", ["g_pow0_1"], HAND_LIST,
     "G-pow00 and G-litpow00, run as in V.pow0.hand (status, then the labels of the lines that differ; the model gives IBM's lines): with ON SIZE ERROR a zero item base, the literal 0 and the difference of an item and itself raised to the literal power 0 are size errors and the receiver keeps 77; GnuCOBOL runs ON SIZE ERROR for the data bases but stores 1 and 6, and folds the literal 0 ** 0 to 1 with no size error",
     r"^g_pow0_1\.cob mismatch G01 H02 G02 G03$"),
    ("V.pow0.unsup", "ir30test", "pow0_cases", ["u_pow0_not"], HAND_LIST,
     "A power by the literal exponent 0 in a COMPUTE with NOT ON SIZE ERROR and no ON SIZE ERROR, run as in V.pow0.hand (status, U01 the step not reached): with a nonzero base the value is 1 and the phrase runs; with a zero base the size error condition skips the phrase while the value 1 is stored (without ON SIZE ERROR the resultant identifier is computed), which the model does not represent (stop-unsup)",
     r"^u_pow0_not\.cob stop-unsup U01$"),
    ("V.c30.hand", "ir30test", "c30_cases", ["v_c30_1"], HAND_COUNT,
     "Hand-written arithmetic statements whose composite of operands is 30 digits or fewer, run by GnuCOBOL and by the front end + semantics (ir30test.py --run), compared line by line: ADD TO with 15 + 15 places, ADD GIVING (the receiver after GIVING not counted), a literal of 15 digits as written, SUBTRACT FROM, SUBTRACT FROM GIVING, MULTIPLY BY two receivers of 18 and 6.12 places (no ROUNDED: no intermediate result), MULTIPLY GIVING, DIVIDE INTO two receivers, DIVIDE GIVING with a REMAINDER item that is not counted",
     r"^1 programs, 1 ok, 9 lines compared, 0 differ$"),
    ("V.c30.unsup", "ir30test", "c30_cases", ["u_c30_add", "u_c30_addg", "u_c30_subg", "u_c30_mul", "u_c30_div", "u_c30_corr", "u_c30_lit"], HAND_LIST,
     "Arithmetic statements whose composite of operands exceeds 30 digits, which the front end makes unsupported with the composite's digits and IBM's limit (status per case): ADD TO and ADD GIVING of 16.2 and 2.16 items (32), SUBTRACT FROM GIVING (32), MULTIPLY GIVING and DIVIDE INTO receivers of 18 and 3.15 places (33), ADD CORRESPONDING with a pair of 16.2 and 2.16 items (32), ADD of a literal of 16 digits as written TO a 3.15 item (31)",
     r"^u_c30_add\.cob fe-unsupported; u_c30_addg\.cob fe-unsupported; u_c30_subg\.cob fe-unsupported; u_c30_mul\.cob fe-unsupported; u_c30_div\.cob fe-unsupported; u_c30_corr\.cob fe-unsupported; u_c30_lit\.cob fe-unsupported$"),
]:
    R(vid, S, claim, "{out}", f"tools/difftest/{cdir}/{{" + ",".join(f + ".cob" for f in files) + "}",
      PRE + f'python3 -I -B "$C/tools/difftest/{tester}.py" --root "$C" --out "$OUT/{vid[2:]}" --run '
      + " ".join(f'"$C/tools/difftest/{cdir}/{f}.cob"' for f in files) + f' > "$OUT/{vid[2:]}.txt" 2>&1; '
      + how + f' "$OUT/{vid[2:]}.txt"', must=must)
for prog, claim in [("cbtrn02c", "CBTRN02C on CardDemo's 300 daily transactions (README commands): end, events, DISPLAYs, WRITEs per file, REWRITEs, RETURN-CODE"),
                    ("cbtrn03c", "CBTRN03C on CBTRN02C's 262 transaction records (README commands)"),
                    ("cbact01c", "CBACT01C on CardDemo's 50 accounts with the COBDATFT model (README commands)"),
                    ("cbstm03ab", "CBSTM03A + CBSTM03B on CBTRN02C's output and CardDemo's data (README commands)"),
                    ("cbact04c", "CBACT04C on CardDemo's TCATBALF (50 category records), ACCTDATA, CARDXREF and DISCGRP: end, events, DISPLAYs, WRITEs per file, REWRITEs (49 for 50 accounts: the last account is not rewritten), and the number of DISPLAYs of 'TRY WITH DEFAULT GROUP CODE' (every record takes the DEFAULT disclosure-group path)")]:
    R(f"V.run.{prog}", S, claim + "; tested (one run), not proved", "{out}", "tools/evidence/sample_runs.sh",
      f"\"$C/tools/evidence/sample_runs.sh\" {prog}")

# ---------------------------------------------------------------- effort per KLOC
S = "effort"
CARD = ["CBACT01C", "CBACT02C", "CBACT03C", "CBACT04C", "CBCUS01C", "CBTRN01C", "CBTRN02C", "CBTRN03C"]
PROOFS = ["Cbact01c", "Cbact02c", "Cbact03c", "Cbcus01c", "Cbact04c", "Cbact04cAny", "Cbact04cAll", "Cbact04cEvents", "Cbact04cEvery",
          "Cbtrn01c", "Cbtrn02c", "Cbtrn02cDup", "Cbtrn03c", "Cbtrn03cStop", "Cbtrn03cAny", "Cbtrn03cEvery"]
R("E1", S, "COBOL side: non-comment lines of the 8 CardDemo programs with all-input theorems, copybooks not counted (rule: tools/evidence/cobol_lines.awk)",
  "{out} lines", "$CD/app/cbl/{" + ",".join(CARD) + "}.cbl",
  "cd \"$CD/app/cbl\" && awk -f \"$C/tools/evidence/cobol_lines.awk\" " + " ".join(f"{p}.cbl" for p in CARD))
R("E2", S, "COBOL side with copybooks: sum over the 8 programs of the program's lines plus the lines of the copybooks it copies (a copybook copied by two programs counts twice)",
  "{out} lines", "$CD/app/cbl, $CD/app/cpy",
  "cd \"$CD/app\" && t=0; for p in " + " ".join(CARD) + "; do t=$((t + $(awk -f \"$C/tools/evidence/cobol_lines.awk\" cbl/$p.cbl))); "
  "for c in $(awk '{l = substr($0, 8, 65)} l ~ /COPY/ {for (i = 1; i <= NF; i++) if ($i == \"COPY\") {x = $(i + 1); gsub(/\\./, \"\", x); print x}}' cbl/$p.cbl | LC_ALL=C sort -u); do "
  "f=$(ls cpy | awk -v c=\"$c\" 'toupper($0) == toupper(c) \".CPY\"'); [ -n \"$f\" ] && t=$((t + $(awk -f \"$C/tools/evidence/cobol_lines.awk\" cpy/$f))); done; done; echo $t")
R("E3", S, "Lean side, program-specific: non-blank non-comment lines of the proof files of those 8 programs (statements, models, lemmas, invariants, proofs, intermediate theorems; rule: tools/evidence/lean_lines.awk)",
  "{out} lines", "Examples/{" + ",".join(PROOFS) + "}.lean",
  "cd \"$C/Examples\" && awk -f \"$C/tools/evidence/lean_lines.awk\" " + " ".join(f"{p}.lean" for p in PROOFS))
R("E4", S, "Lean side, library (shared by all proofs, not program-specific): non-blank non-comment lines of Cobol.lean and Cobol/**/*.lean",
  "{out} lines", "Cobol.lean, Cobol/",
  "cd \"$C\" && awk -f tools/evidence/lean_lines.awk Cobol.lean $(find Cobol -name '*.lean' | LC_ALL=C sort)")
R("E5", S, "Program-specific Lean lines per 1000 COBOL lines (integer division): E3 x 1000 / E1 (copybooks not counted) and E3 x 1000 / E2 (copybooks counted)",
  "{out}", "rows E1, E2, E3 (same commands)",
  "cd \"$C/Examples\" && l=$(awk -f \"$C/tools/evidence/lean_lines.awk\" " + " ".join(f"{p}.lean" for p in PROOFS) + "); "
  "cd \"$CD/app\" && c=0; w=0; for p in " + " ".join(CARD) + "; do n=$(awk -f \"$C/tools/evidence/cobol_lines.awk\" cbl/$p.cbl); c=$((c + n)); w=$((w + n)); "
  "for x in $(awk '{s = substr($0, 8, 65)} s ~ /COPY/ {for (i = 1; i <= NF; i++) if ($i == \"COPY\") {y = $(i + 1); gsub(/\\./, \"\", y); print y}}' cbl/$p.cbl | LC_ALL=C sort -u); do "
  "f=$(ls cpy | awk -v c=\"$x\" 'toupper($0) == toupper(c) \".CPY\"'); [ -n \"$f\" ] && w=$((w + $(awk -f \"$C/tools/evidence/cobol_lines.awk\" cpy/$f))); done; done; "
  "echo \"$l Lean lines: $((l * 1000 / c)) per 1000 COBOL lines without copybooks ($c), $((l * 1000 / w)) per 1000 with copybooks ($w)\"")


# ---------------------------------------------------------------- run, write
def sig_of(f, name):
    out, err, _ = run(f'awk -v name="{name}" -f "$C/tools/evidence/sig.awk" "$C/{f}"', 60)
    return norm(out)


def selected(r):
    return (not ONLY or any(r["id"].startswith(p) for p in ONLY)) and not any(r["id"].startswith(p) for p in SKIP)


def write_tsv(path, rs):
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("\t".join(COLS) + "\n")
        for r in rs:
            fh.write("\t".join(norm(str(r[c])) for c in COLS) + "\n")


REUSE = {}  # --reuse A.tsv,B.tsv: rows checked by an earlier run with the same command
for path in [p for p in OPTS.get("--reuse", "").split(",") if p]:
    ls = open(path, encoding="utf-8").read().rstrip("\n").split("\n")
    for l in ls[1:]:
        d = dict(zip(ls[0].split("\t"), l.split("\t")))
        REUSE[d["id"]] = d

done = []
for r in rows:
    if not selected(r):
        continue
    old = REUSE.get(r["id"])
    if old and old["recheck_cmd"] == norm(r["recheck_cmd"]):
        r["expected"], r["checked_utc"] = old["expected"], old["checked_utc"]
        if "{sig}" in r["value"]:
            r["value"] = r["value"].replace("{sig}", sig_of(r["sig_file"], r["sig_name"]))
        r["value"] = r["value"].replace("{out}", r["expected"])
        print(f"{r['id']}\treused\t{r['expected'][:150]}", flush=True)
        done.append(r)
        continue
    out, err, secs = run(r["recheck_cmd"], r["timeout"])
    lines = [l for l in out.split("\n") if l.strip()]
    if len(lines) != 1:
        print(f"FAIL {r['id']}: {len(lines)} output lines\n{out[-2000:]}\n{err[-2000:]}", flush=True)
        sys.exit(1)
    r["expected"] = norm(lines[0])
    if r.get("must") and not re.search(r["must"], r["expected"]):
        print(f"FAIL {r['id']}: output does not match {r['must']!r}\n{out[-2000:]}\n{err[-2000:]}",
              flush=True)
        sys.exit(1)
    r["checked_utc"] = utc()
    if "{sig}" in r["value"]:
        r["value"] = r["value"].replace("{sig}", sig_of(r["sig_file"], r["sig_name"]))
    r["value"] = r["value"].replace("{out}", r["expected"])
    r["secs"] = secs
    print(f"{r['id']}\t{secs:.0f}s\t{r['expected'][:150]}", flush=True)
    done.append(r)
    write_tsv(os.path.join(OUT, "EVIDENCE_carddemo.partial.tsv"), done)

write_tsv(os.path.join(OUT, "EVIDENCE_carddemo.tsv"), done)
print(f"{len(done)} claims written to {OUT}/EVIDENCE_carddemo.tsv")
