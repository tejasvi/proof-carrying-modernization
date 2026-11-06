# CardDemo evidence package (rendered from EVIDENCE_carddemo.tsv)

The TSV is the source; this file only renders it. Every claim has a command that re-checks it
and the exact output it printed when it was checked. The commands use:

- `C`: the coblean snapshot root; `CD`: the CardDemo checkout at commit
  59cc6c2fd7ebd7ef7925cad552a01a4b8b6e4d5e; `OUT`: a fresh scratch directory;
  `TC`: `$HOME/.elan/toolchains/leanprover--lean4---v4.35.0`.
- Each command writes only under `$OUT`, uses one core (`LEAN_NUM_THREADS=1`, Lake builds one
  file at a time) and no network. Run them from any directory, e.g.
  `C=... CD=... OUT=$(mktemp -d) TC=... bash -c '<recheck_cmd>'`.
- Wording: "kernel-checked" = a Lean theorem whose axioms are listed; "agrees" = a differential
  test (GnuCOBOL, Java, Rust) with the per-case results named; "tested" = a single run.
- Every command except row TH0 uses the snapshot's built files under `$C/.lake/build` (Lean
  object files, `cobolrun`). Row TH0 rebuilds all of them from source in `$OUT/tree` (about 20
  min). Rows that do not call GnuCOBOL can then also be run with `C=$OUT/tree` (the copy leaves
  out `third_party/`, which holds GnuCOBOL).


## artifact

### A1

- claim: Lean toolchain named by the project
- value: leanprover/lean4:v4.35.0
- source: lean-toolchain:1
- re-check: `cat "$C/lean-toolchain"`
- expected: `leanprover/lean4:v4.35.0`
- checked: 2026-10-24T23:07:03Z

### A2

- claim: Lean version used for every check
- value: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- source: $TC/bin/lean
- re-check: `"$TC/bin/lean" --version`
- expected: `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`
- checked: 2026-10-24T23:07:03Z

### A3

- claim: CardDemo commit of the COBOL sources, copybooks and sample data
- value: 59cc6c2fd7ebd7ef7925cad552a01a4b8b6e4d5e
- source: $CD (git checkout)
- re-check: `git -C "$CD" rev-parse HEAD`
- expected: `59cc6c2fd7ebd7ef7925cad552a01a4b8b6e4d5e`
- checked: 2026-10-24T23:07:03Z

### A4

- claim: CardDemo sources are unmodified at that commit (tracked files under app/ with changes)
- value: 0 files changed
- source: $CD (git checkout)
- re-check: `git --no-optional-locks -C "$CD" status --porcelain --untracked-files=no -- app | wc -l`
- expected: `0`
- checked: 2026-10-24T23:07:03Z

### A5

- claim: GnuCOBOL version used by the differential tests
- value: cobc (GnuCOBOL) 3.2.0
- source: scripts/cobc.sh (<os-image> debs unpacked in third_party/gnucobol)
- re-check: `"$C/scripts/cobc.sh" --version | head -n 1`
- expected: `cobc (GnuCOBOL) 3.2.0`
- checked: 2026-10-24T23:07:04Z


## trust

### T1

- claim: Lean files in which the word bv_decide occurs (definition of the cobol_bv tactic, comments, uses); the theorems that depend on its native axiom are those whose axiom lines list a ._native.bv_decide axiom (section theorems)
- value: Cobol/Logic/Attr.lean Cobol/Target/Bits.lean Cobol/Target/Rust.lean Examples/Binary.lean
- source: grep over Cobol/ and Examples/
- re-check: `/usr/bin/grep -rlw bv_decide "$C/Cobol" "$C/Examples" --include=*.lean | sed "s|^$C/||" | LC_ALL=C sort | tr "\n" " "`
- expected: `Cobol/Logic/Attr.lean Cobol/Target/Bits.lean Cobol/Target/Rust.lean Examples/Binary.lean`
- checked: 2026-10-24T23:07:04Z

### T2

- claim: Lean files that use native_decide or Lean.ofReduceBool (separately, bv_decide adds its own native axiom to the theorems that call it: row T1 and the TH*.ax rows; only bincnt_equiv, row TH4.ax, depends on one)
- value: 0 files
- source: grep over Cobol/ and Examples/
- re-check: `/usr/bin/grep -rlE "native_decide|ofReduceBool" "$C/Cobol" "$C/Examples" --include=*.lean | wc -l`
- expected: `0`
- checked: 2026-10-24T23:07:04Z

### T3

- claim: Proof files in which the word sorry occurs (theorems with sorry would also show sorryAx in their axiom lines, section theorems)
- value: 0 files
- source: grep over Cobol/ and Examples/
- re-check: `/usr/bin/grep -rlw sorry "$C/Cobol" "$C/Examples" --include=*.lean | wc -l`
- expected: `0`
- checked: 2026-10-24T23:07:04Z

### T4

- claim: Trusted: the semantics definitions that the theorem statements refer to (IR, storage, data formats, statements, files, the COBDATFT model), non-blank non-comment lines
- value: 3072 lines
- source: Cobol/IR.lean Cobol/Mem.lean Cobol/Codec.lean Cobol/Data.lean Cobol/Config.lean Cobol/Round.lean Cobol/Digits.lean Cobol/Edit.lean Cobol/Layout.lean Cobol/Sem/*.lean Cobol/Ext/CardDemo.lean Cobol/Spec.lean
- re-check: `cd "$C" && awk -f tools/evidence/lean_lines.awk Cobol/IR.lean Cobol/Mem.lean Cobol/Codec.lean Cobol/Data.lean Cobol/Config.lean Cobol/Round.lean Cobol/Digits.lean Cobol/Edit.lean Cobol/Layout.lean Cobol/Sem/*.lean Cobol/Ext/CardDemo.lean Cobol/Spec.lean`
- expected: `3072`
- checked: 2026-10-24T23:07:04Z

### T5

- claim: Trusted: the loader that turns an IR JSON file into the Program constant a theorem is about (cobol_program), non-blank non-comment lines
- value: 899 lines
- source: Cobol/Frontend/Surface.lean Cobol/Frontend/Resolve.lean Cobol/Frontend/Load.lean
- re-check: `cd "$C" && awk -f tools/evidence/lean_lines.awk Cobol/Frontend/Surface.lean Cobol/Frontend/Resolve.lean Cobol/Frontend/Load.lean`
- expected: `899`
- checked: 2026-10-24T23:07:04Z

### T6

- claim: Not trusted, checked by the kernel: proof automation (symbolic execution, simprocs, tactics), non-blank non-comment lines
- value: 2118 lines
- source: Cobol/Logic/*.lean
- re-check: `cd "$C" && awk -f tools/evidence/lean_lines.awk Cobol/Logic/*.lean`
- expected: `2118`
- checked: 2026-10-24T23:07:04Z

### T7

- claim: Not trusted by any proof: the Python front end that writes the IR JSON files (validated, sections theorems and validation), lines that are neither blank nor # comments
- value: 3145 lines
- source: tools/cobolfe/*.py
- re-check: `cd "$C" && cat tools/cobolfe/*.py | /usr/bin/grep -cv "^[[:space:]]*\(#.*\)\?$"`
- expected: `3145`
- checked: 2026-10-24T23:07:05Z

### T8

- claim: Not trusted by any proof: cobolrun, the compiled interpreter used only to run programs in the differential tests and sample-data runs
- value: .lake/build/bin/cobolrun
- source: CobolRun.lean
- re-check: `ls "$C/.lake/build/bin/cobolrun" | sed "s|^$C/||"`
- expected: `.lake/build/bin/cobolrun`
- checked: 2026-10-24T23:07:05Z

### T9

- claim: cobolrun (run time) and cobol_program (elaboration, the Program constants of the theorems) turn an IR JSON file into a Program with the same function, programOfJson; lines that call it
- value: 91 199
- source: Cobol/Frontend/Load.lean
- re-check: `/usr/bin/grep -n 'programOfJson j' "$C/Cobol/Frontend/Load.lean" | cut -d: -f1 | tr '\n' ' '`
- expected: `91 199`
- checked: 2026-10-24T23:07:05Z


## semantics

### S1

- claim: Statement forms of the IR (constructors of Cobol.Stmt)
- value: 45
- source: Cobol/IR.lean
- re-check: `awk '/^inductive Stmt/,/deriving/' "$C/Cobol/IR.lean" | /usr/bin/grep '^  | ' | /usr/bin/grep -oE '\| [a-zA-Z]+' | wc -l`
- expected: `45`
- checked: 2026-10-24T23:07:05Z

### S2

- claim: README section listing what is not modelled or is reported as unsupported (sha256 of the section)
- value: c28e1f6e2f27edc4742fa9dabedc3fd160b5d178889e14e06b827d8f8dad2cc9
- source: README.md, section **Not modelled, or reported as `unsupported`:**
- re-check:

  ```
  awk '/^\*\*Not modelled, or reported as `unsupported`:\*\*/{on=1} on && /^\*\*Proof-side limits/{on=0} on' "$C/README.md" | sha256sum | cut -c1-64
  ```
- expected: `c28e1f6e2f27edc4742fa9dabedc3fd160b5d178889e14e06b827d8f8dad2cc9`
- checked: 2026-10-24T23:07:05Z

### S3

- claim: Fuel monotonicity: a run that ends with a signal other than outOfFuel ends the same way with any larger fuel (statement, sha256 of its one-line form)
- value: 0072dbae30b4d6985cacb31787b47943c58aa743993401ad370cea5707328d84
- source: Cobol.Program.run_mono, Cobol/Logic/FuelMono.lean:326
- re-check: `awk -v name=Program.run_mono -f "$C/tools/evidence/sig.awk" "$C/Cobol/Logic/FuelMono.lean" | sha256sum | cut -c1-64`
- expected: `0072dbae30b4d6985cacb31787b47943c58aa743993401ad370cea5707328d84`
- checked: 2026-10-24T23:07:05Z

### S4

- claim: Kernel-checked library theorems: axioms of Program.run_mono and loopUntil_list_exit
- value: 'Cobol.Program.run_mono' depends on axioms: [propext, Classical.choice, Quot.sound] 'Cobol.loopUntil_list_exit' depends on axioms: [propext, Quot.sound]
- source: docs/evidence_axioms.lean
- re-check: `"$C/scripts/recheck_lean.sh" docs/evidence_axioms.lean 2>&1 | tr '\n' ' '`
- expected: `'Cobol.Program.run_mono' depends on axioms: [propext, Classical.choice, Quot.sound] 'Cobol.loopUntil_list_exit' depends on axioms: [propext, Quot.sound]`
- checked: 2026-10-24T23:07:06Z


## theorems

### TH0

- claim: Full rebuild from source in a copy under $OUT (library, all proof files, cobolrun): build result, theorems with exactly the axioms [propext, Classical.choice, Quot.sound], theorems with a bv_decide axiom; wall time about 20 min on 1 core (17 min measured at a machine load of about 250)
- value: Build completed successfully (115 jobs). | standard: 24 | bv_decide: 1
- source: scripts/recheck_build.sh
- re-check: `"$C/scripts/recheck_build.sh" | awk '/Build completed/ {b = $0} /depends on axioms: \[propext, Classical.choice, Quot.sound\]$/ {s++} /bv_decide/ {v++} END {print b " | standard: " s + 0 " | bv_decide: " v + 0}'`
- expected: `Build completed successfully (115 jobs). | standard: 24 | bv_decide: 1`
- checked: 2026-10-24T23:34:41Z

### TH1.ax

- claim: acctint_equiv is kernel-checked; the axioms it depends on (ACCTINT (examples/acctint, not CardDemo))
- value: 'acctint_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: acctint_equiv, Examples/AcctInt.lean:83
- re-check: `"$C/scripts/recheck_lean.sh" Examples/AcctInt.lean 2>&1 | /usr/bin/grep -F "'acctint_equiv' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'acctint_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:07:10Z

### TH1.st

- claim: acctint_equiv: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem acctint_equiv (m : Mem) (hm : m.size = 33) (ty : UInt8) (bal rate : Int) (days : Int32) (hty : m.field ACCT_TYPE = [ty]) (hbal : decodeNum {} ACCT_BALANCE.fmt (m.field ACCT_BALANCE) = some bal) (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate) (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some days.toInt) : cobolObs (AcctInt.run {} 20 (AcctInt.initState m)) = javaObs (AcctIntJava.accrue (Codepage.cp037Char ty) (some (.valueOf bal 2)) (.valueOf rate 5) days)
- source: acctint_equiv, Examples/AcctInt.lean:83
- re-check: `awk -v name="acctint_equiv" -f "$C/tools/evidence/sig.awk" "$C/Examples/AcctInt.lean" | sha256sum | cut -c1-64`
- expected: `3fe13668e2d28390a2ff653ee732564f5a04e2da6024c3083f11519323aff0b2`
- checked: 2026-10-24T23:07:10Z

### IR.acctint

- claim: IR file loaded by the ACCTINT (examples/acctint, not CardDemo) proofs (cobol_program), sha256
- value: 62621a21d125396b5f540594488c0ab644ba6584c1bd25881ae08e47823181cf
- source: examples/acctint/acctint.ir.json
- re-check: `sha256sum < "$C/examples/acctint/acctint.ir.json" | cut -c1-64`
- expected: `62621a21d125396b5f540594488c0ab644ba6584c1bd25881ae08e47823181cf`
- checked: 2026-10-24T23:07:10Z

### TH2.ax

- claim: acctint_equiv_lowvalues is kernel-checked; the axioms it depends on (ACCTINT (examples/acctint, not CardDemo))
- value: 'acctint_equiv_lowvalues' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: acctint_equiv_lowvalues, Examples/AcctInt.lean:102
- re-check: `"$C/scripts/recheck_lean.sh" Examples/AcctInt.lean 2>&1 | /usr/bin/grep -F "'acctint_equiv_lowvalues' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'acctint_equiv_lowvalues' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:07:13Z

### TH2.st

- claim: acctint_equiv_lowvalues: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem acctint_equiv_lowvalues (m : Mem) (hm : m.size = 33) (ty : UInt8) (rate : Int) (days : Int32) (hty : m.field ACCT_TYPE = [ty]) (hraw : m.field ACCT_BAL_RAW = [0, 0, 0, 0, 0, 0, 0]) (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate) (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some days.toInt) : cobolObs (AcctInt.run {} 20 (AcctInt.initState m)) = javaObs (AcctIntJava.accrue (Codepage.cp037Char ty) none (.valueOf rate 5) days)
- source: acctint_equiv_lowvalues, Examples/AcctInt.lean:102
- re-check: `awk -v name="acctint_equiv_lowvalues" -f "$C/tools/evidence/sig.awk" "$C/Examples/AcctInt.lean" | sha256sum | cut -c1-64`
- expected: `85de9dec91a970e855b134a115dfbd934d76460e095621948bdbcd7cfe7371dc`
- checked: 2026-10-24T23:07:13Z

### TH3.ax

- claim: acctint_rust_equiv is kernel-checked; the axioms it depends on (ACCTINT (examples/acctint, not CardDemo))
- value: 'acctint_rust_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: acctint_rust_equiv, Examples/AcctIntRust.lean:56
- re-check: `"$C/scripts/recheck_lean.sh" Examples/AcctIntRust.lean 2>&1 | /usr/bin/grep -F "'acctint_rust_equiv' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'acctint_rust_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:07:15Z

### TH3.st

- claim: acctint_rust_equiv: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem acctint_rust_equiv (m : Mem) (hm : m.size = 33) (ty : UInt8) (bal rate : Int64) (days : UInt16) (hty : m.field ACCT_TYPE = [ty]) (hbal : decodeNum {} ACCT_BALANCE.fmt (m.field ACCT_BALANCE) = some bal.toInt) (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate.toInt) (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some (days.toNat : Int)) : cobolObs (AcctInt.run {} 20 (AcctInt.initState m)) = rustObs (AcctIntRust.accrue (Codepage.cp037Char ty) (some bal) rate days)
- source: acctint_rust_equiv, Examples/AcctIntRust.lean:56
- re-check: `awk -v name="acctint_rust_equiv" -f "$C/tools/evidence/sig.awk" "$C/Examples/AcctIntRust.lean" | sha256sum | cut -c1-64`
- expected: `cdd466f8bef511dc2625ae46dcead2b697a13ac3de227b1fcb308748aecee4d0`
- checked: 2026-10-24T23:07:15Z

### TH4.ax

- claim: bincnt_equiv is kernel-checked; the axioms it depends on (BINCNT (examples/binary, not CardDemo))
- value: 'bincnt_equiv' depends on axioms: [propext, Classical.choice, Quot.sound, bincnt_equiv._native.bv_decide.ax_7]
- source: bincnt_equiv, Examples/Binary.lean:35
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Binary.lean 2>&1 | /usr/bin/grep -F "'bincnt_equiv' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'bincnt_equiv' depends on axioms: [propext, Classical.choice, Quot.sound, bincnt_equiv._native.bv_decide.ax_7]`
- checked: 2026-10-24T23:07:16Z

### TH4.st

- claim: bincnt_equiv: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem bincnt_equiv (m : Mem) (hm : m.size = 8) (c0 c1 t0 t1 t2 t3 : UInt8) (hc : m.field WS_CNT = [c0, c1]) (ht : m.field WS_TOTAL = [t0, t1, t2, t3]) : let r := BinCnt.run {} 10 (BinCnt.initState m) r.1 = .stop .goback ∧ r.2.mem.field WS_CNT ++ r.2.mem.field WS_TOTAL ++ r.2.mem.field WS_OUT = BinCntJava.update c0 c1 t0 t1 t2 t3
- source: bincnt_equiv, Examples/Binary.lean:35
- re-check: `awk -v name="bincnt_equiv" -f "$C/tools/evidence/sig.awk" "$C/Examples/Binary.lean" | sha256sum | cut -c1-64`
- expected: `8e2f3a364d45f8a851c01d0c7362b54778bc7b62aedf8a355981572468ae64c4`
- checked: 2026-10-24T23:07:16Z

### IR.bincnt

- claim: IR file loaded by the BINCNT (examples/binary, not CardDemo) proofs (cobol_program), sha256
- value: 8dc2f72c12976fa334f2891b8a3c6f386c4fd9e309ea8fcef260dd5910a537ff
- source: examples/binary/bincnt.ir.json
- re-check: `sha256sum < "$C/examples/binary/bincnt.ir.json" | cut -c1-64`
- expected: `8dc2f72c12976fa334f2891b8a3c6f386c4fd9e309ea8fcef260dd5910a537ff`
- checked: 2026-10-24T23:07:16Z

### TH5.ax

- claim: recsum_equiv is kernel-checked; the axioms it depends on (RECSUM (examples/recsum, not CardDemo))
- value: 'recsum_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: recsum_equiv, Examples/RecSum.lean:92
- re-check: `"$C/scripts/recheck_lean.sh" Examples/RecSum.lean 2>&1 | /usr/bin/grep -F "'recsum_equiv' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'recsum_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:07:19Z

### TH5.st

- claim: recsum_equiv: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem recsum_equiv (m : Mem) (hm : m.size = 28) (recs : List (List UInt8 × Int)) (n : Nat) (hrecs : ∀ r ∈ recs, r.1.length = 4 ∧ r.2.natAbs < 10000000) (hlen : recs.length ≤ 9999) (hn : recs.length < n) : let r := RecSum.run {} (n + 10) (RecSum.initState m [(1, recs.map encIn)]) r.1 = .stop .goback ∧ writes r.2 = (RecSumJava.run (recs.map toJava)).map encOut
- source: recsum_equiv, Examples/RecSum.lean:92
- re-check: `awk -v name="recsum_equiv" -f "$C/tools/evidence/sig.awk" "$C/Examples/RecSum.lean" | sha256sum | cut -c1-64`
- expected: `1d0e0ffbbe7f8a6ec303f3c528f6d540473d05a29e23422860c4d2a1ced3e355`
- checked: 2026-10-24T23:07:19Z

### IR.recsum

- claim: IR file loaded by the RECSUM (examples/recsum, not CardDemo) proofs (cobol_program), sha256
- value: ff3a63b331ca2926667219d3cab60c61f7339905618ef89702c5f8df5459ad0d
- source: examples/recsum/recsum.ir.json
- re-check: `sha256sum < "$C/examples/recsum/recsum.ir.json" | cut -c1-64`
- expected: `ff3a63b331ca2926667219d3cab60c61f7339905618ef89702c5f8df5459ad0d`
- checked: 2026-10-24T23:07:19Z

### TH6.ax

- claim: CardDemo.Cbact01c.cbact01c_extracts is kernel-checked; the axioms it depends on (CBACT01C)
- value: 'CardDemo.Cbact01c.cbact01c_extracts' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbact01c.cbact01c_extracts, Examples/Cbact01c.lean:329
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbact01c.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbact01c.cbact01c_extracts' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbact01c.cbact01c_extracts' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:07:38Z

### TH6.st

- claim: CardDemo.Cbact01c.cbact01c_extracts: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbact01c_extracts (m : Mem) (hm : m.size = 1071) (accts : List Acct) (hval : ∀ a ∈ accts, a.valid) (n : Nat) (hn : accts.length < n) : let r := Cbact01c.run { call := Ext.cardDemoCalls Cbact01c.cfg } (n + 40) (Cbact01c.initState m [(1, accts.map Acct.bytes)]) let s := model (m.read 927 2) (m.read 390 7) accts r.1 = .stop .goback ∧ r.2.out = [.display endMsg] ++ s.out ++ [.display startMsg]
- source: CardDemo.Cbact01c.cbact01c_extracts, Examples/Cbact01c.lean:329
- re-check: `awk -v name="cbact01c_extracts" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbact01c.lean" | sha256sum | cut -c1-64`
- expected: `3171fe9579634f5b56ced5cba818f10cb63dc34fdfe914d5b76b51000c246f78`
- checked: 2026-10-24T23:07:38Z

### IR.cbact01c

- claim: IR file loaded by the CBACT01C proofs (cobol_program), sha256
- value: 26ab6e5f84fc4a1433aa088ddb48ed70fc7582abbd3703c21c09dbad8851cdfb
- source: examples/carddemo/cbact01c.ir.json
- re-check: `sha256sum < "$C/examples/carddemo/cbact01c.ir.json" | cut -c1-64`
- expected: `26ab6e5f84fc4a1433aa088ddb48ed70fc7582abbd3703c21c09dbad8851cdfb`
- checked: 2026-10-24T23:07:38Z

### TH7.ax

- claim: CardDemo.Cbact02c.cbact02c_lists is kernel-checked; the axioms it depends on (CBACT02C)
- value: 'CardDemo.Cbact02c.cbact02c_lists' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbact02c.cbact02c_lists, Examples/Cbact02c.lean:58
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbact02c.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbact02c.cbact02c_lists' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbact02c.cbact02c_lists' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:07:42Z

### TH7.st

- claim: CardDemo.Cbact02c.cbact02c_lists: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbact02c_lists (m : Mem) (hm : m.size = 323) (recs : List (List UInt8)) (n : Nat) (hrecs : ∀ r ∈ recs, r.length = 150) (hn : recs.length < n) : let r := Cbact02c.run {} (n + 20) (Cbact02c.initState m [(1, recs)]) r.1 = .stop .goback ∧ displays r.2 = [startMsg] ++ recs ++ [endMsg]
- source: CardDemo.Cbact02c.cbact02c_lists, Examples/Cbact02c.lean:58
- re-check: `awk -v name="cbact02c_lists" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbact02c.lean" | sha256sum | cut -c1-64`
- expected: `aa9ecfcd1368e668da8a6510cdb84e0d5253c18df509d80acac7a2e4668ce12f`
- checked: 2026-10-24T23:07:42Z

### IR.cbact02c

- claim: IR file loaded by the CBACT02C proofs (cobol_program), sha256
- value: 1c4c76c910ab50fa73f777a985cbbf441def222dedfab71a2dbc18f6a012eecb
- source: examples/carddemo/cbact02c.ir.json
- re-check: `sha256sum < "$C/examples/carddemo/cbact02c.ir.json" | cut -c1-64`
- expected: `1c4c76c910ab50fa73f777a985cbbf441def222dedfab71a2dbc18f6a012eecb`
- checked: 2026-10-24T23:07:42Z

### TH8.ax

- claim: CardDemo.Cbact02c.cbact02c_lists' is kernel-checked; the axioms it depends on (CBACT02C)
- value: 'CardDemo.Cbact02c.cbact02c_lists'' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbact02c.cbact02c_lists', Examples/Cbact02cSum.lean:66
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbact02cSum.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbact02c.cbact02c_lists'' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbact02c.cbact02c_lists'' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:07:44Z

### TH8.st

- claim: CardDemo.Cbact02c.cbact02c_lists': its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbact02c_lists' (m : Mem) (hm : m.size = 323) (recs : List (List UInt8)) (n : Nat) (hrecs : ∀ r ∈ recs, r.length = 150) (hn : recs.length < n) : let r := Cbact02c.run {} (n + 20) (Cbact02c.initState m [(1, recs)]) r.1 = .stop .goback ∧ displays r.2 = [startMsg] ++ recs ++ [endMsg]
- source: CardDemo.Cbact02c.cbact02c_lists', Examples/Cbact02cSum.lean:66
- re-check: `awk -v name="cbact02c_lists'" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbact02cSum.lean" | sha256sum | cut -c1-64`
- expected: `88db09bb6ae1686e4b29a30d3fd15f670b7c2c60a88f82bf9130c62db0f6d368`
- checked: 2026-10-24T23:07:44Z

### TH9.ax

- claim: CardDemo.Cbact03c.cbact03c_lists is kernel-checked; the axioms it depends on (CBACT03C)
- value: 'CardDemo.Cbact03c.cbact03c_lists' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbact03c.cbact03c_lists, Examples/Cbact03c.lean:55
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbact03c.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbact03c.cbact03c_lists' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbact03c.cbact03c_lists' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:07:48Z

### TH9.st

- claim: CardDemo.Cbact03c.cbact03c_lists: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbact03c_lists (m : Mem) (hm : m.size = 123) (recs : List (List UInt8)) (n : Nat) (hrecs : ∀ r ∈ recs, r.length = 50) (hn : recs.length < n) : let r := Cbact03c.run {} (n + 20) (Cbact03c.initState m [(1, recs)]) r.1 = .stop .goback ∧ displays r.2 = [startMsg] ++ recs.flatMap (fun r => [r, r]) ++ [endMsg]
- source: CardDemo.Cbact03c.cbact03c_lists, Examples/Cbact03c.lean:55
- re-check: `awk -v name="cbact03c_lists" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbact03c.lean" | sha256sum | cut -c1-64`
- expected: `2b7c0d0c8c22ba60820e3e78d5c3ee5f947572b72e6d7afaf1ae75dfa29d1168`
- checked: 2026-10-24T23:07:48Z

### IR.cbact03c

- claim: IR file loaded by the CBACT03C proofs (cobol_program), sha256
- value: 0b595702748ab299ac464d19d24587e574e1f99b7f4da6d2481ab68aca2811c8
- source: examples/carddemo/cbact03c.ir.json
- re-check: `sha256sum < "$C/examples/carddemo/cbact03c.ir.json" | cut -c1-64`
- expected: `0b595702748ab299ac464d19d24587e574e1f99b7f4da6d2481ab68aca2811c8`
- checked: 2026-10-24T23:07:48Z

### TH10.ax

- claim: CardDemo.Cbcus01c.cbcus01c_lists is kernel-checked; the axioms it depends on (CBCUS01C)
- value: 'CardDemo.Cbcus01c.cbcus01c_lists' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbcus01c.cbcus01c_lists, Examples/Cbcus01c.lean:55
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbcus01c.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbcus01c.cbcus01c_lists' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbcus01c.cbcus01c_lists' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:07:51Z

### TH10.st

- claim: CardDemo.Cbcus01c.cbcus01c_lists: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbcus01c_lists (m : Mem) (hm : m.size = 1023) (recs : List (List UInt8)) (n : Nat) (hrecs : ∀ r ∈ recs, r.length = 500) (hn : recs.length < n) : let r := Cbcus01c.run {} (n + 20) (Cbcus01c.initState m [(1, recs)]) r.1 = .stop .goback ∧ displays r.2 = [startMsg] ++ recs.flatMap (fun r => [r, r]) ++ [endMsg]
- source: CardDemo.Cbcus01c.cbcus01c_lists, Examples/Cbcus01c.lean:55
- re-check: `awk -v name="cbcus01c_lists" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbcus01c.lean" | sha256sum | cut -c1-64`
- expected: `929dec0602e61a23de0a3e8671ee5a0654faa6aafd6163ecb57cd8c2187caffe`
- checked: 2026-10-24T23:07:51Z

### IR.cbcus01c

- claim: IR file loaded by the CBCUS01C proofs (cobol_program), sha256
- value: 60216395c95d843028d80430ac6101ca98dbe88f731e80454993a9c7a4c78a94
- source: examples/carddemo/cbcus01c.ir.json
- re-check: `sha256sum < "$C/examples/carddemo/cbcus01c.ir.json" | cut -c1-64`
- expected: `60216395c95d843028d80430ac6101ca98dbe88f731e80454993a9c7a4c78a94`
- checked: 2026-10-24T23:07:51Z

### TH11.ax

- claim: CardDemo.Cbact04c.cbact04c_last_account_not_updated is kernel-checked; the axioms it depends on (CBACT04C)
- value: 'CardDemo.Cbact04c.cbact04c_last_account_not_updated' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbact04c.cbact04c_last_account_not_updated, Examples/Cbact04c.lean:32
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbact04c.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbact04c.cbact04c_last_account_not_updated' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbact04c.cbact04c_last_account_not_updated' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:08:08Z

### TH11.st

- claim: CardDemo.Cbact04c.cbact04c_last_account_not_updated: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbact04c_last_account_not_updated (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8) -- the clock reading: `YYYYMMDDhhmmss`, hundredths `mil` (two digits), time zone (cpre cpost : List UInt8) (mil : Int) (hcpre : cpre.length = 14) (hcpost : cpost.length = 5) (hmil : mil.natAbs < 100) (hmil0 : 0 ≤ mil) (hclk : clk 0 = cpre ++ encodeNum {} { digits := 2 } mil ++ cpost) -- the one category-balance record: account `acct`, type `ty`, category `cat`, balance `bal` (acct cat bal : Int) (ty tf : List UInt8) (hty : ty.length = 2) (htf : tf.length = 22) (hacct : acct.natAbs < 100000000000) (hacct0 : 0 ≤ acct) (hcat : cat.natAbs < 10000) (hcat0 : 0 ≤ cat) (hbal : bal.natAbs < 100000000000) -- the account, its cross-reference and its disclosure group (a1 a2 grp af : List UInt8) (abal : Int) (ha1 : a1.length = 1) (ha2 : a2.length = 88) (hgrp : grp.length = 10) (haf : af.length = 178) (card cust xf : List UInt8) (hcard : card.length = 16) (hcust : cust.length = 9) (hxf : xf.length = 14) (rate : Int) (hrate : rate.natAbs < 1000000) (hr0 : rate ≠ 0) (df : List UInt8) (hdf : df.length = 28) (n : Nat) : let t := encodeNum {} TRANCAT_ACCT_ID.fmt acct ++ ty ++ encodeNum {} TRANCAT_CD.fmt cat ++ encodeNum {} TRAN_CAT_BAL.fmt bal ++ tf let a := encodeNum {} ACCT_ID.fmt acct ++ a1 ++ encodeNum {} ACCT_CURR_BAL.fmt abal ++ a2 ++ grp ++ af let x := card ++ cust ++ encodeNum {} XREF_ACCT_ID.fmt acct ++ xf let d := grp ++ ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt cat ++ encodeNum {} DIS_INT_RATE.fmt rate ++ df let r := Cbact04c.run { clock := clk } (n + 60) (Cbact04c.initState m [(1, [t]), (2, [x]), (3, [a]), (4, [d])]) r.1 = .stop .goback ∧ acctRewrites r.2 = [] ∧ (tranWrites r.2).length = 1
- source: CardDemo.Cbact04c.cbact04c_last_account_not_updated, Examples/Cbact04c.lean:32
- re-check: `awk -v name="cbact04c_last_account_not_updated" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbact04c.lean" | sha256sum | cut -c1-64`
- expected: `fbf06bc0eaeacdc2638d899cf9eee4113c22959f9de34d12a58db05a7687561a`
- checked: 2026-10-24T23:08:08Z

### IR.cbact04c

- claim: IR file loaded by the CBACT04C proofs (cobol_program), sha256
- value: 59d5918d0a85a808230b339654adfda9d71627ee5d5b26978febafe86552900f
- source: examples/carddemo/cbact04c.ir.json
- re-check: `sha256sum < "$C/examples/carddemo/cbact04c.ir.json" | cut -c1-64`
- expected: `59d5918d0a85a808230b339654adfda9d71627ee5d5b26978febafe86552900f`
- checked: 2026-10-24T23:08:08Z

### TH12.ax

- claim: CardDemo.Cbact04c.cbact04c_last_account_not_updated' is kernel-checked; the axioms it depends on (CBACT04C)
- value: 'CardDemo.Cbact04c.cbact04c_last_account_not_updated'' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbact04c.cbact04c_last_account_not_updated', Examples/Cbact04cSum.lean:68
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbact04cSum.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbact04c.cbact04c_last_account_not_updated'' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbact04c.cbact04c_last_account_not_updated'' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:08:24Z

### TH12.st

- claim: CardDemo.Cbact04c.cbact04c_last_account_not_updated': its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbact04c_last_account_not_updated' (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8) -- the clock reading: `YYYYMMDDhhmmss`, hundredths `mil` (two digits), time zone (cpre cpost : List UInt8) (mil : Int) (hcpre : cpre.length = 14) (hcpost : cpost.length = 5) (hmil : mil.natAbs < 100) (hmil0 : 0 ≤ mil) (hclk : clk 0 = cpre ++ encodeNum {} { digits := 2 } mil ++ cpost) -- the one category-balance record: account `acct`, type `ty`, category `cat`, balance `bal` (acct cat bal : Int) (ty tf : List UInt8) (hty : ty.length = 2) (htf : tf.length = 22) (hacct : acct.natAbs < 100000000000) (hacct0 : 0 ≤ acct) (hcat : cat.natAbs < 10000) (hcat0 : 0 ≤ cat) (hbal : bal.natAbs < 100000000000) -- the account, its cross-reference and its disclosure group (a1 a2 grp af : List UInt8) (abal : Int) (ha1 : a1.length = 1) (ha2 : a2.length = 88) (hgrp : grp.length = 10) (haf : af.length = 178) (card cust xf : List UInt8) (hcard : card.length = 16) (hcust : cust.length = 9) (hxf : xf.length = 14) (rate : Int) (hrate : rate.natAbs < 1000000) (hr0 : rate ≠ 0) (df : List UInt8) (hdf : df.length = 28) (n : Nat) : let t := encodeNum {} TRANCAT_ACCT_ID.fmt acct ++ ty ++ encodeNum {} TRANCAT_CD.fmt cat ++ encodeNum {} TRAN_CAT_BAL.fmt bal ++ tf let a := encodeNum {} ACCT_ID.fmt acct ++ a1 ++ encodeNum {} ACCT_CURR_BAL.fmt abal ++ a2 ++ grp ++ af let x := card ++ cust ++ encodeNum {} XREF_ACCT_ID.fmt acct ++ xf let d := grp ++ ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt cat ++ encodeNum {} DIS_INT_RATE.fmt rate ++ df let r := Cbact04c.run { clock := clk } (n + 60) (Cbact04c.initState m [(1, [t]), (2, [x]), (3, [a]), (4, [d])]) r.1 = .stop .goback ∧ acctRewrites r.2 = [] ∧ (tranWrites r.2).length = 1
- source: CardDemo.Cbact04c.cbact04c_last_account_not_updated', Examples/Cbact04cSum.lean:68
- re-check: `awk -v name="cbact04c_last_account_not_updated'" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbact04cSum.lean" | sha256sum | cut -c1-64`
- expected: `366943f625aa6aa05d1f4d9d1ae5d5dd6aa0981af728cfe44a9034b05dc030e6`
- checked: 2026-10-24T23:08:24Z

### TH13.ax

- claim: CardDemo.Cbact04c.cbact04c_two_accounts is kernel-checked; the axioms it depends on (CBACT04C)
- value: 'CardDemo.Cbact04c.cbact04c_two_accounts' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbact04c.cbact04c_two_accounts, Examples/Cbact04c2.lean:21
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbact04c2.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbact04c.cbact04c_two_accounts' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbact04c.cbact04c_two_accounts' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:08:59Z

### TH13.st

- claim: CardDemo.Cbact04c.cbact04c_two_accounts: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbact04c_two_accounts (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8) (cpre cpost : List UInt8) (mil : Int) (hcpre : cpre.length = 14) (hcpost : cpost.length = 5) (hmil : mil.natAbs < 100) (hmil0 : 0 ≤ mil) (hclk0 : clk 0 = cpre ++ encodeNum {} { digits := 2 } mil ++ cpost) (hclk1 : clk 1 = cpre ++ encodeNum {} { digits := 2 } mil ++ cpost) -- two category-balance records, one per account, same type `ty` and category `cat` (acct1 acct2 cat bal1 bal2 : Int) (ty tf1 tf2 : List UInt8) (hty : ty.length = 2) (htf1 : tf1.length = 22) (htf2 : tf2.length = 22) (hacct1 : acct1.natAbs < 100000000000) (hacct10 : 0 ≤ acct1) (hacct2 : acct2.natAbs < 100000000000) (hacct20 : 0 ≤ acct2) (hne : acct1 ≠ acct2) (hcat : cat.natAbs < 10000) (hcat0 : 0 ≤ cat) (hbal1 : bal1.natAbs < 1000000000) (hbal2 : bal2.natAbs < 1000000000) -- account 1 (balance `abal1`, the fields 1050-UPDATE-ACCOUNT touches), account 2, group `grp` (s1 mid1 zip1 af1 grp p2 q2 : List UInt8) (abal1 cc1 cd1 : Int) (habal1 : abal1.natAbs < 100000000000) (hs1 : s1.length = 1) (hmid1 : mid1.length = 54) (hzip1 : zip1.length = 10) (haf1 : af1.length = 178) (hgrp : grp.length = 10) (hp2 : p2.length = 101) (hq2 : q2.length = 178) (card1 card2 cust1 cust2 xf1 xf2 : List UInt8) (hcard1 : card1.length = 16) (hcard2 : card2.length = 16) (hcust1 : cust1.length = 9) (hcust2 : cust2.length = 9) (hxf1 : xf1.length = 14) (hxf2 : xf2.length = 14) (rate : Int) (hrate : rate.natAbs < 1000000) (hr0 : rate ≠ 0) (df : List UInt8) (hdf : df.length = 28) (n : Nat) : let t1 := encodeNum {} TRANCAT_ACCT_ID.fmt acct1 ++ ty ++ encodeNum {} TRANCAT_CD.fmt cat ++ encodeNum {} TRAN_CAT_BAL.fmt bal1 ++ tf1 let t2 := encodeNum {} TRANCAT_ACCT_ID.fmt acct2 ++ ty ++ encodeNum {} TRANCAT_CD.fmt cat ++ encodeNum {} TRAN_CAT_BAL.fmt bal2 ++ tf2 let a1 := encodeNum {} ACCT_ID.fmt acct1 ++ s1 ++ encodeNum {} ACCT_CURR_BAL.fmt abal1 ++ mid1 ++ encodeNum {} ACCT_CURR_CYC_CREDIT.fmt cc1 ++ encodeNum {} ACCT_CURR_CYC_DEBIT.fmt cd1 ++ zip1 ++ grp ++ af1 let a2 := encodeNum {} ACCT_ID.fmt acct2 ++ p2 ++ grp ++ q2 let x1 := card1 ++ cust1 ++ encodeNum {} XREF_ACCT_ID.fmt acct1 ++ xf1 let x2 := card2 ++ cust2 ++ encodeNum {} XREF_ACCT_ID.fmt acct2 ++ xf2 let d := grp ++ ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt cat ++ encodeNum {} DIS_INT_RATE.fmt rate ++ df let r := Cbact04c.run { clock := clk } (n + 80) (Cbact04c.initState m [(1, [t1, t2]), (2, [x1, x2]), (3, [a1, a2]), (4, [d])]) r.1 = .stop .goback ∧ (tranWrites r.2).length = 2 ∧ acctRewrites r.2 = [encodeNum {} ACCT_ID.fmt acct1 ++ s1 ++ encodeNum {} ACCT_CURR_BAL.fmt (abal1 + divRound .truncation (bal1 * rate) 120000) ++ mid1 ++ encodeNum {} ACCT_CURR_CYC_CREDIT.fmt 0 ++ encodeNum {} ACCT_CURR_CYC_DEBIT.fmt 0 ++ zip1 ++ grp ++ af1]
- source: CardDemo.Cbact04c.cbact04c_two_accounts, Examples/Cbact04c2.lean:21
- re-check: `awk -v name="cbact04c_two_accounts" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbact04c2.lean" | sha256sum | cut -c1-64`
- expected: `ed19d489b02981e9df6c6fb8ba47900c850e9ca9a7e9e16c206849af9feac2fc`
- checked: 2026-10-24T23:08:59Z

### TH14.ax

- claim: CardDemo.Cbact04c.cbact04c_one_account is kernel-checked; the axioms it depends on (CBACT04C)
- value: 'CardDemo.Cbact04c.cbact04c_one_account' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbact04c.cbact04c_one_account, Examples/Cbact04cAny.lean:79
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbact04cAny.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbact04c.cbact04c_one_account' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbact04c.cbact04c_one_account' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:09:28Z

### TH14.st

- claim: CardDemo.Cbact04c.cbact04c_one_account: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbact04c_one_account (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8) (hclk : ∀ k, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧ 0 ≤ mil ∧ clk k = pre ++ encodeNum {} { digits := 2 } mil ++ post) (acct : Int) (hacct : acct.natAbs < 100000000000) (hacct0 : 0 ≤ acct) (cats : List Cat) (hcats : ∀ c ∈ cats, c.valid) (hlen : cats.length < 999999) -- the account record and its cross-reference, found by key (accts xrefs discs : List (List UInt8)) (ai xi : Nat) (arec xrec : List UInt8) (a1 a2 grp af : List UInt8) (abal : Int) (ha1 : a1.length = 1) (ha2 : a2.length = 88) (hgrp : grp.length = 10) (haf : af.length = 178) (harec : arec = encodeNum {} ACCT_ID.fmt acct ++ a1 ++ encodeNum {} ACCT_CURR_BAL.fmt abal ++ a2 ++ grp ++ af) (hai : Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt acct) accts = some ai) (hag : accts.getD ai [] = arec) (hxrec : xrec.length = 50) (hxi : Sem.findKey { off := 25, len := 11 } (encodeNum {} FD_XREF_ACCT_ID.fmt acct) xrefs = some xi) (hxg : xrefs.getD xi [] = xrec) -- each category's disclosure group (its rate may be zero) (di : Cat → Nat) (rate : Cat → Int) (dfill : Cat → List UInt8) (hdisc : ∀ c ∈ cats, Sem.findKey { off := 0, len := 16 } (grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat) discs = some (di c) ∧ discs.getD (di c) [] = grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat ++ encodeNum {} DIS_INT_RATE.fmt (rate c) ++ dfill c ∧ (dfill c).length = 28 ∧ (rate c).natAbs < 1000000) (n : Nat) (hn : cats.length < n) : let r := Cbact04c.run { clock := clk } (n + 60) (Cbact04c.initState m [(1, cats.map (Cat.bytes acct)), (2, xrefs), (3, accts), (4, discs)]) r.1 = .stop .goback ∧ acctRewrites r.2 = [] ∧ (tranWrites r.2).length = (cats.filter (fun c => rate c ≠ 0)).length
- source: CardDemo.Cbact04c.cbact04c_one_account, Examples/Cbact04cAny.lean:79
- re-check: `awk -v name="cbact04c_one_account" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbact04cAny.lean" | sha256sum | cut -c1-64`
- expected: `55911f9f7ef87506850e07dcf9ec27618d4d36f849018ef1ff607570a3a1a0cf`
- checked: 2026-10-24T23:09:28Z

### TH15.ax

- claim: CardDemo.Cbact04c.cbact04c_all is kernel-checked; the axioms it depends on (CBACT04C)
- value: 'CardDemo.Cbact04c.cbact04c_all' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbact04c.cbact04c_all, Examples/Cbact04cAll.lean:212
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbact04cAll.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbact04c.cbact04c_all' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbact04c.cbact04c_all' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:10:23Z

### TH15.st

- claim: CardDemo.Cbact04c.cbact04c_all: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbact04c_all (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8) (hclk : ∀ k, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧ 0 ≤ mil ∧ clk k = pre ++ encodeNum {} { digits := 2 } mil ++ post) (accs : List Acc) (hval : ∀ a ∈ accs, a.valid) (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) (hlen : (items accs).length < 999999) -- each account's record and cross-reference, found by key (accts xrefs discs : List (List UInt8)) (ai xi : Acc → Nat) (hacct : ∀ a ∈ accs, Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt a.id) accts = some (ai a) ∧ accts.getD (ai a) [] = a.bytes) (hxref : ∀ a ∈ accs, Sem.findKey { off := 25, len := 11 } (encodeNum {} FD_XREF_ACCT_ID.fmt a.id) xrefs = some (xi a) ∧ xrefs.getD (xi a) [] = a.xrec) -- each category's disclosure group (its rate may be zero) (rate : Acc → Cat → Int) (di : Acc → Cat → Nat) (dfill : Acc → Cat → List UInt8) (hdisc : ∀ a ∈ accs, ∀ c ∈ a.cats, Sem.findKey { off := 0, len := 16 } (a.grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat) discs = some (di a c) ∧ discs.getD (di a c) [] = a.grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat ++ encodeNum {} DIS_INT_RATE.fmt (rate a c) ++ dfill a c ∧ (dfill a c).length = 28 ∧ (rate a c).natAbs < 1000000) (n : Nat) (hn : (items accs).length < n) : let r := Cbact04c.run { clock := clk } (n + 60) (Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)), (2, xrefs), (3, accts), (4, discs)]) r.1 = .stop .goback ∧ acctRewrites r.2 = accs.dropLast.map (fun a => a.posted (totalInt (rate a) a.cats)) ∧ (tranWrites r.2).length = nTxA rate (items accs)
- source: CardDemo.Cbact04c.cbact04c_all, Examples/Cbact04cAll.lean:212
- re-check: `awk -v name="cbact04c_all" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbact04cAll.lean" | sha256sum | cut -c1-64`
- expected: `c8f2b8247f05cb5f491488d746bf689a25c8566d265d65b359cb6f5d3b122660`
- checked: 2026-10-24T23:10:23Z

### TH16.ax

- claim: CardDemo.Cbact04c.cbact04c_events is kernel-checked; the axioms it depends on (CBACT04C)
- value: 'CardDemo.Cbact04c.cbact04c_events' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbact04c.cbact04c_events, Examples/Cbact04cEvents.lean:237
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbact04cEvents.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbact04c.cbact04c_events' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbact04c.cbact04c_events' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:12:20Z

### TH16.st

- claim: CardDemo.Cbact04c.cbact04c_events: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbact04c_events (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8) (hclk : ∀ k, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧ 0 ≤ mil ∧ clk k = pre ++ encodeNum {} { digits := 2 } mil ++ post) (accs : List Acc) (hval : ∀ a ∈ accs, a.valid) (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) (hlen : (items accs).length < 999999) (accts xrefs discs : List (List UInt8)) (ai xi : Acc → Nat) (hacct : ∀ a ∈ accs, Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt a.id) accts = some (ai a) ∧ accts.getD (ai a) [] = a.bytes) (hxref : ∀ a ∈ accs, Sem.findKey { off := 25, len := 11 } (encodeNum {} FD_XREF_ACCT_ID.fmt a.id) xrefs = some (xi a) ∧ xrefs.getD (xi a) [] = a.xrec) (rate : Acc → Cat → Int) (di : Acc → Cat → Nat) (dfill : Acc → Cat → List UInt8) (hdisc : ∀ a ∈ accs, ∀ c ∈ a.cats, Sem.findKey { off := 0, len := 16 } (a.grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat) discs = some (di a c) ∧ discs.getD (di a c) [] = a.grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat ++ encodeNum {} DIS_INT_RATE.fmt (rate a c) ++ dfill a c ∧ (dfill a c).length = 28 ∧ (rate a c).natAbs < 1000000) (n : Nat) (hn : (items accs).length < n) : let r := Cbact04c.run { clock := clk } (n + 60) (Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)), (2, xrefs), (3, accts), (4, discs)]) let s := model4 rate (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk (items accs) r.1 = .stop .goback ∧ r.2.out = [.display endMsg] ++ s.out ++ [.display startMsg]
- source: CardDemo.Cbact04c.cbact04c_events, Examples/Cbact04cEvents.lean:237
- re-check: `awk -v name="cbact04c_events" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbact04cEvents.lean" | sha256sum | cut -c1-64`
- expected: `a6ae745685c0bca09a10708fba260a017c7c42e8e7f29e864912b323448bd28c`
- checked: 2026-10-24T23:12:20Z

### TH17.ax

- claim: CardDemo.Cbtrn01c.cbtrn01c_verifies is kernel-checked; the axioms it depends on (CBTRN01C)
- value: 'CardDemo.Cbtrn01c.cbtrn01c_verifies' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbtrn01c.cbtrn01c_verifies, Examples/Cbtrn01c.lean:152
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbtrn01c.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbtrn01c.cbtrn01c_verifies' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbtrn01c.cbtrn01c_verifies' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:12:49Z

### TH17.st

- claim: CardDemo.Cbtrn01c.cbtrn01c_verifies: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbtrn01c_verifies (m : Mem) (hm : m.size = 3441) (trans : List (List UInt8)) (htr : ∀ t ∈ trans, t.length = 350) (xrefs : List Xref) (hxv : ∀ x ∈ xrefs, x.valid) (accts : List (List UInt8)) (hac : ∀ a ∈ accts, a.length = 300) (n : Nat) (hn : trans.length < n) : let r := Cbtrn01c.run {} (n + 40) (Cbtrn01c.initState m [(1, trans), (3, xrefs.map Xref.bytes), (5, accts)]) r.1 = .stop .goback ∧ displays r.2 = [startMsg] ++ trans.flatMap (fun t => t :: lookupMsgs xrefs accts t) ++ lookupMsgs xrefs accts (trans.getLast?.getD (m.read 1700 350)) ++ [endMsg]
- source: CardDemo.Cbtrn01c.cbtrn01c_verifies, Examples/Cbtrn01c.lean:152
- re-check: `awk -v name="cbtrn01c_verifies" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbtrn01c.lean" | sha256sum | cut -c1-64`
- expected: `98cf027af177bdc2bf6c5f908424669faadd4690fac8902843c071e5b629d594`
- checked: 2026-10-24T23:12:49Z

### IR.cbtrn01c

- claim: IR file loaded by the CBTRN01C proofs (cobol_program), sha256
- value: fe0ffd1e310610abac859e39146fd32c93b74f3cb884bae74b5d2e8d39b6f4f5
- source: examples/carddemo/cbtrn01c.ir.json
- re-check: `sha256sum < "$C/examples/carddemo/cbtrn01c.ir.json" | cut -c1-64`
- expected: `fe0ffd1e310610abac859e39146fd32c93b74f3cb884bae74b5d2e8d39b6f4f5`
- checked: 2026-10-24T23:12:49Z

### TH18.ax

- claim: CardDemo.Cbtrn01c.cbtrn01c_verifies_all is kernel-checked; the axioms it depends on (CBTRN01C)
- value: 'CardDemo.Cbtrn01c.cbtrn01c_verifies_all' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbtrn01c.cbtrn01c_verifies_all, Examples/Cbtrn01c.lean:261
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbtrn01c.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbtrn01c.cbtrn01c_verifies_all' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbtrn01c.cbtrn01c_verifies_all' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:13:16Z

### TH18.st

- claim: CardDemo.Cbtrn01c.cbtrn01c_verifies_all: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbtrn01c_verifies_all (m : Mem) (hm : m.size = 3441) (trans : List (List UInt8)) (htr : ∀ t ∈ trans, t.length = 350) (xrefs : List Xref) (hxv : ∀ x ∈ xrefs, x.valid) (accts : List (List UInt8)) (hac : ∀ a ∈ accts, a.length = 300) (custs cards tr6 : List (List UInt8)) (n : Nat) (hn : trans.length < n) : let r := Cbtrn01c.run {} (n + 40) (Cbtrn01c.initState m [(1, trans), (2, custs), (3, xrefs.map Xref.bytes), (4, cards), (5, accts), (6, tr6)]) r.1 = .stop .goback ∧ displays r.2 = [startMsg] ++ trans.flatMap (fun t => t :: lookupMsgs xrefs accts t) ++ lookupMsgs xrefs accts (trans.getLast?.getD (m.read 1700 350)) ++ [endMsg]
- source: CardDemo.Cbtrn01c.cbtrn01c_verifies_all, Examples/Cbtrn01c.lean:261
- re-check: `awk -v name="cbtrn01c_verifies_all" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbtrn01c.lean" | sha256sum | cut -c1-64`
- expected: `1cc1cbbe6890539b19b192b7066564f28a1472c30650f98e924aa52cff700505`
- checked: 2026-10-24T23:13:16Z

### TH19.ax

- claim: CardDemo.Cbtrn02c.cbtrn02c_posts is kernel-checked; the axioms it depends on (CBTRN02C)
- value: 'CardDemo.Cbtrn02c.cbtrn02c_posts' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbtrn02c.cbtrn02c_posts, Examples/Cbtrn02c.lean:562
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbtrn02c.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbtrn02c.cbtrn02c_posts' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbtrn02c.cbtrn02c_posts' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:14:37Z

### TH19.st

- claim: CardDemo.Cbtrn02c.cbtrn02c_posts: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbtrn02c_posts (m : Mem) (hm : m.size = 3252) (clk : Nat → List UInt8) (hclk : ∀ k, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧ 0 ≤ mil ∧ clk k = pre ++ encodeNum {} { digits := 2 } mil ++ post) (trans : List Tran) (htv : ∀ t ∈ trans, t.valid) (hids : (trans.map Tran.id).Nodup) (hlen : trans.length < 1000000000) (xrefs : List Xref) (hxv : ∀ x ∈ xrefs, x.valid) (accts : List Acct) (hav : ∀ a ∈ accts, a.valid) (cats : List TCat) (hcv : ∀ c ∈ cats, c.valid) (n : Nat) (hn : trans.length < n) : let r := Cbtrn02c.run { clock := clk } (n + 60) (Cbtrn02c.initState m [(1, trans.map Tran.bytes), (3, xrefs.map Xref.bytes), (5, accts.map Acct.bytes), (6, cats.map TCat.bytes)]) let s := model xrefs clk (m.read 2212 20) ⟨accts, cats, m.read 2618 22, 0, 0, []⟩ trans r.1 = .stop .goback ∧ r.2.out = [.display endMsg, .display (rejMsg ++ encodeNum {} WS_REJECT_COUNT.fmt s.rejects), .display (procMsg ++ encodeNum {} WS_TRANSACTION_COUNT.fmt trans.length)] ++ s.out ++ [.display startMsg] ∧ r.2.mem.read 3250 2 = encodeNum {} RETURN_CODE.fmt (if 0 < s.rejects then 4 else 0)
- source: CardDemo.Cbtrn02c.cbtrn02c_posts, Examples/Cbtrn02c.lean:562
- re-check: `awk -v name="cbtrn02c_posts" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbtrn02c.lean" | sha256sum | cut -c1-64`
- expected: `d1911daa886b5e88c4857f0a6cccec997ffcfceb2158e350dadb7dee13342e2b`
- checked: 2026-10-24T23:14:37Z

### IR.cbtrn02c

- claim: IR file loaded by the CBTRN02C proofs (cobol_program), sha256
- value: 20ac4c44beb0b843aa25aa6bd84760c80ba0e1c709e6a0753be2055da29ff1a1
- source: examples/carddemo/cbtrn02c.ir.json
- re-check: `sha256sum < "$C/examples/carddemo/cbtrn02c.ir.json" | cut -c1-64`
- expected: `20ac4c44beb0b843aa25aa6bd84760c80ba0e1c709e6a0753be2055da29ff1a1`
- checked: 2026-10-24T23:14:37Z

### TH20.ax

- claim: CardDemo.Cbtrn02c.cbtrn02c_any is kernel-checked; the axioms it depends on (CBTRN02C)
- value: 'CardDemo.Cbtrn02c.cbtrn02c_any' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbtrn02c.cbtrn02c_any, Examples/Cbtrn02cDup.lean:249
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbtrn02cDup.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbtrn02c.cbtrn02c_any' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbtrn02c.cbtrn02c_any' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:16:39Z

### TH20.st

- claim: CardDemo.Cbtrn02c.cbtrn02c_any: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbtrn02c_any (m : Mem) (hm : m.size = 3252) (clk : Nat → List UInt8) (hclk : ∀ k, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧ 0 ≤ mil ∧ clk k = pre ++ encodeNum {} { digits := 2 } mil ++ post) (trans : List Tran) (htv : ∀ t ∈ trans, t.valid) (hlen : trans.length < 1000000000) (xrefs : List Xref) (hxv : ∀ x ∈ xrefs, x.valid) (accts : List Acct) (hav : ∀ a ∈ accts, a.valid) (cats : List TCat) (hcv : ∀ c ∈ cats, c.valid) (n : Nat) (hn : trans.length < n) : let r := Cbtrn02c.run { clock := clk } (n + 60) (Cbtrn02c.initState m [(1, trans.map Tran.bytes), (3, xrefs.map Xref.bytes), (5, accts.map Acct.bytes), (6, cats.map TCat.bytes)]) let sx := modelX xrefs clk (m.read 2212 20) ⟨accts, cats, m.read 2618 22, 0, 0, []⟩ trans if sx.stop then r.1 = .fault (.abend 999) ∧ r.2.out = sx.m.out ++ [.display startMsg] ∧ r.2.mem.read 3250 2 = encodeNum {} RETURN_CODE.fmt 0 else r.1 = .stop .goback ∧ r.2.out = [.display endMsg, .display (rejMsg ++ encodeNum {} WS_REJECT_COUNT.fmt sx.m.rejects), .display (procMsg ++ encodeNum {} WS_TRANSACTION_COUNT.fmt trans.length)] ++ sx.m.out ++ [.display startMsg] ∧ r.2.mem.read 3250 2 = encodeNum {} RETURN_CODE.fmt (if 0 < sx.m.rejects then 4 else 0)
- source: CardDemo.Cbtrn02c.cbtrn02c_any, Examples/Cbtrn02cDup.lean:249
- re-check: `awk -v name="cbtrn02c_any" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbtrn02cDup.lean" | sha256sum | cut -c1-64`
- expected: `728d277ac55dad87215c0b2c5d99d87a913bc0e741a394c00bd6dafe0f9f8afb`
- checked: 2026-10-24T23:16:39Z

### TH21.ax

- claim: CardDemo.Cbtrn03c.cbtrn03c_report is kernel-checked; the axioms it depends on (CBTRN03C)
- value: 'CardDemo.Cbtrn03c.cbtrn03c_report' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbtrn03c.cbtrn03c_report, Examples/Cbtrn03c.lean:534
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbtrn03c.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbtrn03c.cbtrn03c_report' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbtrn03c.cbtrn03c_report' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:18:22Z

### TH21.st

- claim: CardDemo.Cbtrn03c.cbtrn03c_report: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbtrn03c_report (m : Mem) (hm : m.size = 2309) (trans : List Tran) (htv : ∀ t ∈ trans, t.valid) (hne : trans ≠ []) (hlen : trans.length < 10000000) (xrefs : List Xref) (hxv : ∀ x ∈ xrefs, x.valid) (types catgs : List (List UInt8)) (htyl : ∀ r ∈ types, r.length = 60) (hcgl : ∀ r ∈ catgs, r.length = 60) (parm : List UInt8) (hpl : parm.length = 80) (prest : List (List UInt8)) (hdate : ∀ t ∈ trans, Sem.cmpBytes (t.proc.take 10) (parm.take 10) ≠ .lt ∧ Sem.cmpBytes (t.proc.take 10) ((parm.drop 11).take 10) ≠ .gt) (hxf : ∀ t ∈ trans, (Sem.findKey { off := 0, len := 16 } t.card (xrefs.map Xref.bytes)).isSome) (htf : ∀ t ∈ trans, (Sem.findKey { off := 0, len := 2 } t.ty types).isSome) (hcf : ∀ t ∈ trans, (Sem.findKey { off := 0, len := 6 } (t.ty ++ encodeNum {} FD_TRAN_CAT_CD.fmt t.cat) catgs).isSome) (hcard : ∀ t ∈ trans, t.card ≠ List.replicate 16 64) (n : Nat) (hn : trans.length < n) : let r := Cbtrn03c.run {} (n + 60) (Cbtrn03c.initState m [(1, trans.map Tran.bytes), (2, xrefs.map Xref.bytes), (3, types), (4, catgs), (6, parm :: prest)]) let s := report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) trans r.1 = .stop .goback ∧ r.2.out = [.display endMsg] ++ eofEvents s (trans.getLast hne) ++ s.out ++ [.display (reportingMsg ++ parm.take 10 ++ toMsg ++ (parm.drop 11).take 10), .display startMsg]
- source: CardDemo.Cbtrn03c.cbtrn03c_report, Examples/Cbtrn03c.lean:534
- re-check: `awk -v name="cbtrn03c_report" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbtrn03c.lean" | sha256sum | cut -c1-64`
- expected: `240281cf53dd973e27789dc94e4a36277b02679ffcd076aae313d73380226f9c`
- checked: 2026-10-24T23:18:22Z

### IR.cbtrn03c

- claim: IR file loaded by the CBTRN03C proofs (cobol_program), sha256
- value: e04dea09f48b67f591bba4a3f98ea3f1b13f2aa8d8cc9f96f44467fc0b9df873
- source: examples/carddemo/cbtrn03c.ir.json
- re-check: `sha256sum < "$C/examples/carddemo/cbtrn03c.ir.json" | cut -c1-64`
- expected: `e04dea09f48b67f591bba4a3f98ea3f1b13f2aa8d8cc9f96f44467fc0b9df873`
- checked: 2026-10-24T23:18:22Z

### TH22.ax

- claim: CardDemo.Cbtrn03c.cbtrn03c_stops is kernel-checked; the axioms it depends on (CBTRN03C)
- value: 'CardDemo.Cbtrn03c.cbtrn03c_stops' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbtrn03c.cbtrn03c_stops, Examples/Cbtrn03cStop.lean:86
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbtrn03cStop.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbtrn03c.cbtrn03c_stops' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbtrn03c.cbtrn03c_stops' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:20:03Z

### TH22.st

- claim: CardDemo.Cbtrn03c.cbtrn03c_stops: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbtrn03c_stops (m : Mem) (hm : m.size = 2309) (pre : List Tran) (t0 : Tran) (post : List Tran) (hpv : ∀ t ∈ pre, t.valid) (ht0v : t0.valid) (hlen : pre.length < 10000000) (xrefs : List Xref) (hxv : ∀ x ∈ xrefs, x.valid) (types catgs : List (List UInt8)) (htyl : ∀ r ∈ types, r.length = 60) (hcgl : ∀ r ∈ catgs, r.length = 60) (parm : List UInt8) (hpl : parm.length = 80) (prest : List (List UInt8)) (hpre : ∀ t ∈ pre, inRange parm t) (ht0 : ¬ inRange parm t0) (hxf : ∀ t ∈ pre, (Sem.findKey { off := 0, len := 16 } t.card (xrefs.map Xref.bytes)).isSome) (htf : ∀ t ∈ pre, (Sem.findKey { off := 0, len := 2 } t.ty types).isSome) (hcf : ∀ t ∈ pre, (Sem.findKey { off := 0, len := 6 } (t.ty ++ encodeNum {} FD_TRAN_CAT_CD.fmt t.cat) catgs).isSome) (hcard : ∀ t ∈ pre, t.card ≠ List.replicate 16 64) (n : Nat) (hn : pre.length < n) : let r := Cbtrn03c.run {} (n + 60) (Cbtrn03c.initState m [(1, (pre ++ t0 :: post).map Tran.bytes), (2, xrefs.map Xref.bytes), (3, types), (4, catgs), (6, parm :: prest)]) let s := report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) pre r.1 = .stop .goback ∧ r.2.out = [.display endMsg] ++ s.out ++ [.display (reportingMsg ++ parm.take 10 ++ toMsg ++ (parm.drop 11).take 10), .display startMsg]
- source: CardDemo.Cbtrn03c.cbtrn03c_stops, Examples/Cbtrn03cStop.lean:86
- re-check: `awk -v name="cbtrn03c_stops" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbtrn03cStop.lean" | sha256sum | cut -c1-64`
- expected: `b4f48581715d0e777e61f4b05d026e23365cf164489e00bcfb67ea7df9234eb9`
- checked: 2026-10-24T23:20:03Z

### TH23.ax

- claim: CardDemo.Cbtrn03c.cbtrn03c_any is kernel-checked; the axioms it depends on (CBTRN03C)
- value: 'CardDemo.Cbtrn03c.cbtrn03c_any' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbtrn03c.cbtrn03c_any, Examples/Cbtrn03cAny.lean:232
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbtrn03cAny.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbtrn03c.cbtrn03c_any' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbtrn03c.cbtrn03c_any' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:22:21Z

### TH23.st

- claim: CardDemo.Cbtrn03c.cbtrn03c_any: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbtrn03c_any (m : Mem) (hm : m.size = 2309) (trans : List Tran) (htv : ∀ t ∈ trans, t.valid) (hlen : trans.length < 10000000) (t00 : Tran) (ht00 : trans = [] → t00.valid ∧ m.read 733 350 = t00.bytes) (xrefs : List Xref) (hxv : ∀ x ∈ xrefs, x.valid) (types catgs : List (List UInt8)) (htyl : ∀ r ∈ types, r.length = 60) (hcgl : ∀ r ∈ catgs, r.length = 60) (parm : List UInt8) (hpl : parm.length = 80) (prest : List (List UInt8)) (hcard : ∀ t ∈ trans, t.card ≠ List.replicate 16 64) (n : Nat) (hn : trans.length < n) : let r := Cbtrn03c.run {} (n + 60) (Cbtrn03c.initState m [(1, trans.map Tran.bytes), (2, xrefs.map Xref.bytes), (3, types), (4, catgs), (6, parm :: prest)]) let res := result3 parm (trans.getLast?.getD t00) (report3x xrefs types catgs parm trans) r.1 = res.1 ∧ r.2.out = res.2
- source: CardDemo.Cbtrn03c.cbtrn03c_any, Examples/Cbtrn03cAny.lean:232
- re-check: `awk -v name="cbtrn03c_any" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbtrn03cAny.lean" | sha256sum | cut -c1-64`
- expected: `8b1c487b7fe4e89fba28fa45668f356dfc459e00c1d37dacc008f1aa892ffe7f`
- checked: 2026-10-24T23:22:21Z

### TH24.ax

- claim: CardDemo.Cbtrn03c.cbtrn03c_every is kernel-checked; the axioms it depends on (CBTRN03C)
- value: 'CardDemo.Cbtrn03c.cbtrn03c_every' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbtrn03c.cbtrn03c_every, Examples/Cbtrn03cEvery.lean:176
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbtrn03cEvery.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbtrn03c.cbtrn03c_every' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbtrn03c.cbtrn03c_every' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:24:49Z

### TH24.st

- claim: CardDemo.Cbtrn03c.cbtrn03c_every: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbtrn03c_every (m : Mem) (hm : m.size = 2309) (trans : List Tran) (htv : ∀ t ∈ trans, t.valid) (hlen : trans.length < 10000000) (t00 : Tran) (ht00 : trans = [] → t00.valid ∧ m.read 733 350 = t00.bytes) (x0 : Int) (hx0 : trans.head?.map Tran.card = some (List.replicate 16 64) → m.read 1110 11 = encodeNum {} XREF_ACCT_ID.fmt x0 ∧ x0.natAbs < 100000000000 ∧ 0 ≤ x0) (xrefs : List Xref) (hxv : ∀ x ∈ xrefs, x.valid) (types catgs : List (List UInt8)) (htyl : ∀ r ∈ types, r.length = 60) (hcgl : ∀ r ∈ catgs, r.length = 60) (parm : List UInt8) (hpl : parm.length = 80) (prest : List (List UInt8)) (n : Nat) (hn : trans.length < n) : let r := Cbtrn03c.run {} (n + 60) (Cbtrn03c.initState m [(1, trans.map Tran.bytes), (2, xrefs.map Xref.bytes), (3, types), (4, catgs), (6, parm :: prest)]) let res := result3 parm (trans.getLast?.getD t00) (report3xe xrefs types catgs parm x0 trans) r.1 = res.1 ∧ r.2.out = res.2
- source: CardDemo.Cbtrn03c.cbtrn03c_every, Examples/Cbtrn03cEvery.lean:176
- re-check: `awk -v name="cbtrn03c_every" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbtrn03cEvery.lean" | sha256sum | cut -c1-64`
- expected: `f2f2d3b4b438b15adf552afc659f09b4d7e109cf64548ee73d47b258aed86752`
- checked: 2026-10-24T23:24:50Z

### TH25.ax

- claim: CardDemo.Cbact04c.cbact04c_every is kernel-checked; the axioms it depends on (CBACT04C)
- value: 'CardDemo.Cbact04c.cbact04c_every' depends on axioms: [propext, Classical.choice, Quot.sound]
- source: CardDemo.Cbact04c.cbact04c_every, Examples/Cbact04cEvery.lean:391
- re-check: `"$C/scripts/recheck_lean.sh" Examples/Cbact04cEvery.lean 2>&1 | /usr/bin/grep -F "'CardDemo.Cbact04c.cbact04c_every' depends on axioms" | sed 's/^[^ ]*:[0-9]*:[0-9]*: //'`
- expected: `'CardDemo.Cbact04c.cbact04c_every' depends on axioms: [propext, Classical.choice, Quot.sound]`
- checked: 2026-10-24T23:32:49Z

### TH25.st

- claim: CardDemo.Cbact04c.cbact04c_every: its statement (every binder is a remaining hypothesis; record and fuel bounds included), one line, sha256
- value: theorem cbact04c_every (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8) (hclk : ∀ k, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧ 0 ≤ mil ∧ clk k = pre ++ encodeNum {} { digits := 2 } mil ++ post) (accs : List Acc) (hval : ∀ a ∈ accs, a.validIn) (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) (hlen : (items accs).length < 999999) (accts : List Acc) (hav : ∀ a ∈ accts, a.validRec) (xrefs : List (List UInt8)) (hxl : ∀ r ∈ xrefs, r.length = 50) (discs : List Disc) (hdv : ∀ d ∈ discs, d.valid) (n : Nat) (hn : (items accs).length < n) : let r := Cbact04c.run { clock := clk } (n + 60) (Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)), (2, xrefs), (3, accts.map Acc.bytes), (4, discs.map Disc.bytes)]) let s := model4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk (items accs) if s.stop then r.1 = .fault (.abend 999) ∧ r.2.out = s.out ++ [.display startMsg] else r.1 = .stop .goback ∧ r.2.out = [.display endMsg] ++ s.out ++ [.display startMsg]
- source: CardDemo.Cbact04c.cbact04c_every, Examples/Cbact04cEvery.lean:391
- re-check: `awk -v name="cbact04c_every" -f "$C/tools/evidence/sig.awk" "$C/Examples/Cbact04cEvery.lean" | sha256sum | cut -c1-64`
- expected: `2a3859a3dfc2b58024a0573110dab9e46d9c3617d656e249fdfca01911895b9a`
- checked: 2026-10-24T23:32:49Z

### IRFE.cbact01c

- claim: examples/carddemo/cbact01c.ir.json is the front end's output on $CD/app/cbl/CBACT01C.cbl (same JSON after key sorting)
- value: same
- source: tools/cobolfe/cobolfe.py; examples/carddemo/cbact01c.ir.json
- re-check: `mkdir -p "$OUT/irfe" && python3 -I -B "$C/tools/cobolfe/cobolfe.py" "$CD/app/cbl/CBACT01C.cbl" -I "$CD/app/cpy" --tab-width 4 -o "$OUT/irfe/cbact01c.json" && [ "$(jq -S . "$OUT/irfe/cbact01c.json" | sha256sum)" = "$(jq -S . "$C/examples/carddemo/cbact01c.ir.json" | sha256sum)" ] && echo same || echo DIFFERENT`
- expected: `same`
- checked: 2026-10-24T23:32:49Z

### IRFE.cbact02c

- claim: examples/carddemo/cbact02c.ir.json is the front end's output on $CD/app/cbl/CBACT02C.cbl (same JSON after key sorting)
- value: same
- source: tools/cobolfe/cobolfe.py; examples/carddemo/cbact02c.ir.json
- re-check: `mkdir -p "$OUT/irfe" && python3 -I -B "$C/tools/cobolfe/cobolfe.py" "$CD/app/cbl/CBACT02C.cbl" -I "$CD/app/cpy" --tab-width 4 -o "$OUT/irfe/cbact02c.json" && [ "$(jq -S . "$OUT/irfe/cbact02c.json" | sha256sum)" = "$(jq -S . "$C/examples/carddemo/cbact02c.ir.json" | sha256sum)" ] && echo same || echo DIFFERENT`
- expected: `same`
- checked: 2026-10-24T23:32:49Z

### IRFE.cbact03c

- claim: examples/carddemo/cbact03c.ir.json is the front end's output on $CD/app/cbl/CBACT03C.cbl (same JSON after key sorting)
- value: same
- source: tools/cobolfe/cobolfe.py; examples/carddemo/cbact03c.ir.json
- re-check: `mkdir -p "$OUT/irfe" && python3 -I -B "$C/tools/cobolfe/cobolfe.py" "$CD/app/cbl/CBACT03C.cbl" -I "$CD/app/cpy" --tab-width 4 -o "$OUT/irfe/cbact03c.json" && [ "$(jq -S . "$OUT/irfe/cbact03c.json" | sha256sum)" = "$(jq -S . "$C/examples/carddemo/cbact03c.ir.json" | sha256sum)" ] && echo same || echo DIFFERENT`
- expected: `same`
- checked: 2026-10-24T23:32:49Z

### IRFE.cbact04c

- claim: examples/carddemo/cbact04c.ir.json is the front end's output on $CD/app/cbl/CBACT04C.cbl (same JSON after key sorting)
- value: same
- source: tools/cobolfe/cobolfe.py; examples/carddemo/cbact04c.ir.json
- re-check: `mkdir -p "$OUT/irfe" && python3 -I -B "$C/tools/cobolfe/cobolfe.py" "$CD/app/cbl/CBACT04C.cbl" -I "$CD/app/cpy" --tab-width 4 -o "$OUT/irfe/cbact04c.json" && [ "$(jq -S . "$OUT/irfe/cbact04c.json" | sha256sum)" = "$(jq -S . "$C/examples/carddemo/cbact04c.ir.json" | sha256sum)" ] && echo same || echo DIFFERENT`
- expected: `same`
- checked: 2026-10-24T23:32:49Z

### IRFE.cbcus01c

- claim: examples/carddemo/cbcus01c.ir.json is the front end's output on $CD/app/cbl/CBCUS01C.cbl (same JSON after key sorting)
- value: same
- source: tools/cobolfe/cobolfe.py; examples/carddemo/cbcus01c.ir.json
- re-check: `mkdir -p "$OUT/irfe" && python3 -I -B "$C/tools/cobolfe/cobolfe.py" "$CD/app/cbl/CBCUS01C.cbl" -I "$CD/app/cpy" --tab-width 4 -o "$OUT/irfe/cbcus01c.json" && [ "$(jq -S . "$OUT/irfe/cbcus01c.json" | sha256sum)" = "$(jq -S . "$C/examples/carddemo/cbcus01c.ir.json" | sha256sum)" ] && echo same || echo DIFFERENT`
- expected: `same`
- checked: 2026-10-24T23:32:49Z

### IRFE.cbtrn01c

- claim: examples/carddemo/cbtrn01c.ir.json is the front end's output on $CD/app/cbl/CBTRN01C.cbl (same JSON after key sorting)
- value: same
- source: tools/cobolfe/cobolfe.py; examples/carddemo/cbtrn01c.ir.json
- re-check: `mkdir -p "$OUT/irfe" && python3 -I -B "$C/tools/cobolfe/cobolfe.py" "$CD/app/cbl/CBTRN01C.cbl" -I "$CD/app/cpy" --tab-width 4 -o "$OUT/irfe/cbtrn01c.json" && [ "$(jq -S . "$OUT/irfe/cbtrn01c.json" | sha256sum)" = "$(jq -S . "$C/examples/carddemo/cbtrn01c.ir.json" | sha256sum)" ] && echo same || echo DIFFERENT`
- expected: `same`
- checked: 2026-10-24T23:32:49Z

### IRFE.cbtrn02c

- claim: examples/carddemo/cbtrn02c.ir.json is the front end's output on $CD/app/cbl/CBTRN02C.cbl (same JSON after key sorting)
- value: same
- source: tools/cobolfe/cobolfe.py; examples/carddemo/cbtrn02c.ir.json
- re-check: `mkdir -p "$OUT/irfe" && python3 -I -B "$C/tools/cobolfe/cobolfe.py" "$CD/app/cbl/CBTRN02C.cbl" -I "$CD/app/cpy" --tab-width 4 -o "$OUT/irfe/cbtrn02c.json" && [ "$(jq -S . "$OUT/irfe/cbtrn02c.json" | sha256sum)" = "$(jq -S . "$C/examples/carddemo/cbtrn02c.ir.json" | sha256sum)" ] && echo same || echo DIFFERENT`
- expected: `same`
- checked: 2026-10-24T23:32:49Z

### IRFE.cbtrn03c

- claim: examples/carddemo/cbtrn03c.ir.json is the front end's output on $CD/app/cbl/CBTRN03C.cbl (same JSON after key sorting)
- value: same
- source: tools/cobolfe/cobolfe.py; examples/carddemo/cbtrn03c.ir.json
- re-check: `mkdir -p "$OUT/irfe" && python3 -I -B "$C/tools/cobolfe/cobolfe.py" "$CD/app/cbl/CBTRN03C.cbl" -I "$CD/app/cpy" --tab-width 4 -o "$OUT/irfe/cbtrn03c.json" && [ "$(jq -S . "$OUT/irfe/cbtrn03c.json" | sha256sum)" = "$(jq -S . "$C/examples/carddemo/cbtrn03c.ir.json" | sha256sum)" ] && echo same || echo DIFFERENT`
- expected: `same`
- checked: 2026-10-24T23:32:49Z

### IRFE.cbstm03ab

- claim: examples/carddemo/cbstm03ab.ir.json is CBSTM03A with CBSTM03B linked in by tools/cobolfe/link.py, from the unmodified sources (same JSON after key sorting)
- value: same
- source: tools/cobolfe/cobolfe.py, tools/cobolfe/link.py; examples/carddemo/cbstm03ab.ir.json
- re-check: `mkdir -p "$OUT/irfe" && cd "$OUT/irfe" && python3 -I -B "$C/tools/cobolfe/cobolfe.py" "$CD/app/cbl/CBSTM03A.CBL" -I "$CD/app/cpy" --tab-width 4 -o a.json && python3 -I -B "$C/tools/cobolfe/cobolfe.py" "$CD/app/cbl/CBSTM03B.CBL" -I "$CD/app/cpy" --tab-width 4 -o b.json && python3 -I -B "$C/tools/cobolfe/link.py" a.json b.json -o ab.json > /dev/null && [ "$(jq -S . ab.json | sha256sum)" = "$(jq -S . "$C/examples/carddemo/cbstm03ab.ir.json" | sha256sum)" ] && echo same || echo DIFFERENT`
- expected: `same`
- checked: 2026-10-24T23:32:49Z


## coverage

### CV0

- claim: Programs in the CardDemo checkout (app/cbl and the three optional modules)
- value: 44 programs
- source: $CD/app/*/cbl, $CD/app/cbl
- re-check: `ls "$CD"/app/cbl/ "$CD"/app/app-*/cbl/ | /usr/bin/grep -ciE '\.cbl$'`
- expected: `44`
- checked: 2026-10-24T23:32:49Z

### CV.CBACT01C

- claim: CBACT01C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: cbact01c_extracts
- value: CBACT01C kind=batch lines=358 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback
- source: $CD/app/cbl/CBACT01C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/CBACT01C.cbl"`
- expected: `CBACT01C kind=batch lines=358 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback`
- checked: 2026-10-24T23:32:50Z

### CV.CBACT02C

- claim: CBACT02C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: cbact02c_lists, cbact02c_lists'
- value: CBACT02C kind=batch lines=129 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback
- source: $CD/app/cbl/CBACT02C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/CBACT02C.cbl"`
- expected: `CBACT02C kind=batch lines=129 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback`
- checked: 2026-10-24T23:32:50Z

### CV.CBACT03C

- claim: CBACT03C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: cbact03c_lists
- value: CBACT03C kind=batch lines=130 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback
- source: $CD/app/cbl/CBACT03C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/CBACT03C.cbl"`
- expected: `CBACT03C kind=batch lines=130 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback`
- checked: 2026-10-24T23:32:50Z

### CV.CBACT04C

- claim: CBACT04C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: cbact04c_last_account_not_updated, cbact04c_last_account_not_updated', cbact04c_two_accounts, cbact04c_one_account, cbact04c_all, cbact04c_events, cbact04c_every
- value: CBACT04C kind=batch lines=552 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback
- source: $CD/app/cbl/CBACT04C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/CBACT04C.cbl"`
- expected: `CBACT04C kind=batch lines=552 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback`
- checked: 2026-10-24T23:32:50Z

### CV.CBCUS01C

- claim: CBCUS01C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: cbcus01c_lists
- value: CBCUS01C kind=batch lines=130 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback
- source: $CD/app/cbl/CBCUS01C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/CBCUS01C.cbl"`
- expected: `CBCUS01C kind=batch lines=130 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback`
- checked: 2026-10-24T23:32:50Z

### CV.CBEXPORT

- claim: CBEXPORT: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: CBEXPORT kind=batch lines=396 fe=ok unsupported=0 resolves=no reason="uncaught exception: key EXPORT-SEQUENCE-NUM is outside the record area of file 6 "
- source: $CD/app/cbl/CBEXPORT.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/CBEXPORT.cbl"`
- expected: `CBEXPORT kind=batch lines=396 fe=ok unsupported=0 resolves=no reason="uncaught exception: key EXPORT-SEQUENCE-NUM is outside the record area of file 6 "`
- checked: 2026-10-24T23:32:50Z

### CV.CBIMPORT

- claim: CBIMPORT: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: CBIMPORT kind=batch lines=337 fe=ok unsupported=0 resolves=no reason="uncaught exception: key EXPORT-SEQUENCE-NUM is outside the record area of file 1 "
- source: $CD/app/cbl/CBIMPORT.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/CBIMPORT.cbl"`
- expected: `CBIMPORT kind=batch lines=337 fe=ok unsupported=0 resolves=no reason="uncaught exception: key EXPORT-SEQUENCE-NUM is outside the record area of file 1 "`
- checked: 2026-10-24T23:32:50Z

### CV.CBSTM03A

- claim: CBSTM03A: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: CBSTM03A kind=batch lines=784 fe=ok unsupported=0 resolves=yes signal=fault:Cobol.Fault.unsupported "CALL CBSTM03B"
- source: $CD/app/cbl/CBSTM03A.CBL
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/CBSTM03A.CBL"`
- expected: `CBSTM03A kind=batch lines=784 fe=ok unsupported=0 resolves=yes signal=fault:Cobol.Fault.unsupported "CALL CBSTM03B"`
- checked: 2026-10-24T23:32:51Z

### CV.CBSTM03B

- claim: CBSTM03B: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: CBSTM03B kind=batch lines=162 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback
- source: $CD/app/cbl/CBSTM03B.CBL
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/CBSTM03B.CBL"`
- expected: `CBSTM03B kind=batch lines=162 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback`
- checked: 2026-10-24T23:32:51Z

### CV.CBTRN01C

- claim: CBTRN01C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: cbtrn01c_verifies, cbtrn01c_verifies_all
- value: CBTRN01C kind=batch lines=415 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback
- source: $CD/app/cbl/CBTRN01C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/CBTRN01C.cbl"`
- expected: `CBTRN01C kind=batch lines=415 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback`
- checked: 2026-10-24T23:32:51Z

### CV.CBTRN02C

- claim: CBTRN02C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: cbtrn02c_posts, cbtrn02c_any
- value: CBTRN02C kind=batch lines=619 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback
- source: $CD/app/cbl/CBTRN02C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/CBTRN02C.cbl"`
- expected: `CBTRN02C kind=batch lines=619 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback`
- checked: 2026-10-24T23:32:51Z

### CV.CBTRN03C

- claim: CBTRN03C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: cbtrn03c_report, cbtrn03c_stops, cbtrn03c_any, cbtrn03c_every
- value: CBTRN03C kind=batch lines=545 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback
- source: $CD/app/cbl/CBTRN03C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/CBTRN03C.cbl"`
- expected: `CBTRN03C kind=batch lines=545 fe=ok unsupported=0 resolves=yes signal=stop:Cobol.StopKind.goback`
- checked: 2026-10-24T23:32:51Z

### CV.COACTUPC

- claim: COACTUPC: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COACTUPC kind=cics lines=3368 fe=stop reason="COACTUPC.cbl:615:8: copybook DFHBMSCA not found"
- source: $CD/app/cbl/COACTUPC.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COACTUPC.cbl"`
- expected: `COACTUPC kind=cics lines=3368 fe=stop reason="COACTUPC.cbl:615:8: copybook DFHBMSCA not found"`
- checked: 2026-10-24T23:32:51Z

### CV.COACTVWC

- claim: COACTVWC: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COACTVWC kind=cics lines=703 fe=stop reason="COACTVWC.cbl:221:8: copybook DFHBMSCA not found"
- source: $CD/app/cbl/COACTVWC.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COACTVWC.cbl"`
- expected: `COACTVWC kind=cics lines=703 fe=stop reason="COACTVWC.cbl:221:8: copybook DFHBMSCA not found"`
- checked: 2026-10-24T23:32:51Z

### CV.COADM01C

- claim: COADM01C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COADM01C kind=cics lines=189 fe=stop reason="COADM01C.cbl:60:8: copybook DFHAID not found"
- source: $CD/app/cbl/COADM01C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COADM01C.cbl"`
- expected: `COADM01C kind=cics lines=189 fe=stop reason="COADM01C.cbl:60:8: copybook DFHAID not found"`
- checked: 2026-10-24T23:32:51Z

### CV.COBIL00C

- claim: COBIL00C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COBIL00C kind=cics lines=420 fe=stop reason="COBIL00C.cbl:84:8: copybook DFHAID not found"
- source: $CD/app/cbl/COBIL00C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COBIL00C.cbl"`
- expected: `COBIL00C kind=cics lines=420 fe=stop reason="COBIL00C.cbl:84:8: copybook DFHAID not found"`
- checked: 2026-10-24T23:32:51Z

### CV.COBSWAIT

- claim: COBSWAIT: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COBSWAIT kind=batch lines=13 fe=ok unsupported=1 resolves=yes signal=fault:Cobol.Fault.unsupported "ACCEPT (line 36): ACCEPT FROM SYSIN"
- source: $CD/app/cbl/COBSWAIT.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COBSWAIT.cbl"`
- expected: `COBSWAIT kind=batch lines=13 fe=ok unsupported=1 resolves=yes signal=fault:Cobol.Fault.unsupported "ACCEPT (line 36): ACCEPT FROM SYSIN"`
- checked: 2026-10-24T23:32:52Z

### CV.COCRDLIC

- claim: COCRDLIC: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COCRDLIC kind=cics lines=1093 fe=stop reason="COCRDLIC.cbl:267:8: copybook DFHBMSCA not found"
- source: $CD/app/cbl/COCRDLIC.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COCRDLIC.cbl"`
- expected: `COCRDLIC kind=cics lines=1093 fe=stop reason="COCRDLIC.cbl:267:8: copybook DFHBMSCA not found"`
- checked: 2026-10-24T23:32:52Z

### CV.COCRDSLC

- claim: COCRDSLC: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COCRDSLC kind=cics lines=642 fe=stop reason="COCRDSLC.cbl:208:8: copybook DFHBMSCA not found"
- source: $CD/app/cbl/COCRDSLC.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COCRDSLC.cbl"`
- expected: `COCRDSLC kind=cics lines=642 fe=stop reason="COCRDSLC.cbl:208:8: copybook DFHBMSCA not found"`
- checked: 2026-10-24T23:32:52Z

### CV.COCRDUPC

- claim: COCRDUPC: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COCRDUPC kind=cics lines=1194 fe=stop reason="COCRDUPC.cbl:327:8: copybook DFHBMSCA not found"
- source: $CD/app/cbl/COCRDUPC.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COCRDUPC.cbl"`
- expected: `COCRDUPC kind=cics lines=1194 fe=stop reason="COCRDUPC.cbl:327:8: copybook DFHBMSCA not found"`
- checked: 2026-10-24T23:32:52Z

### CV.COMEN01C

- claim: COMEN01C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COMEN01C kind=cics lines=213 fe=stop reason="COMEN01C.cbl:60:8: copybook DFHAID not found"
- source: $CD/app/cbl/COMEN01C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COMEN01C.cbl"`
- expected: `COMEN01C kind=cics lines=213 fe=stop reason="COMEN01C.cbl:60:8: copybook DFHAID not found"`
- checked: 2026-10-24T23:32:52Z

### CV.CORPT00C

- claim: CORPT00C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: CORPT00C kind=cics lines=498 fe=stop reason="CORPT00C.cbl:148:8: copybook DFHAID not found"
- source: $CD/app/cbl/CORPT00C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/CORPT00C.cbl"`
- expected: `CORPT00C kind=cics lines=498 fe=stop reason="CORPT00C.cbl:148:8: copybook DFHAID not found"`
- checked: 2026-10-24T23:32:52Z

### CV.COSGN00C

- claim: COSGN00C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COSGN00C kind=cics lines=172 fe=stop reason="COSGN00C.cbl:57:8: copybook DFHAID not found"
- source: $CD/app/cbl/COSGN00C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COSGN00C.cbl"`
- expected: `COSGN00C kind=cics lines=172 fe=stop reason="COSGN00C.cbl:57:8: copybook DFHAID not found"`
- checked: 2026-10-24T23:32:52Z

### CV.COTRN00C

- claim: COTRN00C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COTRN00C kind=cics lines=529 fe=stop reason="COTRN00C.cbl:80:8: copybook DFHAID not found"
- source: $CD/app/cbl/COTRN00C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COTRN00C.cbl"`
- expected: `COTRN00C kind=cics lines=529 fe=stop reason="COTRN00C.cbl:80:8: copybook DFHAID not found"`
- checked: 2026-10-24T23:32:52Z

### CV.COTRN01C

- claim: COTRN01C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COTRN01C kind=cics lines=231 fe=stop reason="COTRN01C.cbl:71:8: copybook DFHAID not found"
- source: $CD/app/cbl/COTRN01C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COTRN01C.cbl"`
- expected: `COTRN01C kind=cics lines=231 fe=stop reason="COTRN01C.cbl:71:8: copybook DFHAID not found"`
- checked: 2026-10-24T23:32:52Z

### CV.COTRN02C

- claim: COTRN02C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COTRN02C kind=cics lines=614 fe=stop reason="COTRN02C.cbl:92:8: copybook DFHAID not found"
- source: $CD/app/cbl/COTRN02C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COTRN02C.cbl"`
- expected: `COTRN02C kind=cics lines=614 fe=stop reason="COTRN02C.cbl:92:8: copybook DFHAID not found"`
- checked: 2026-10-24T23:32:52Z

### CV.COUSR00C

- claim: COUSR00C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COUSR00C kind=cics lines=531 fe=stop reason="COUSR00C.cbl:83:8: copybook DFHAID not found"
- source: $CD/app/cbl/COUSR00C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COUSR00C.cbl"`
- expected: `COUSR00C kind=cics lines=531 fe=stop reason="COUSR00C.cbl:83:8: copybook DFHAID not found"`
- checked: 2026-10-24T23:32:52Z

### CV.COUSR01C

- claim: COUSR01C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COUSR01C kind=cics lines=198 fe=stop reason="COUSR01C.cbl:55:8: copybook DFHAID not found"
- source: $CD/app/cbl/COUSR01C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COUSR01C.cbl"`
- expected: `COUSR01C kind=cics lines=198 fe=stop reason="COUSR01C.cbl:55:8: copybook DFHAID not found"`
- checked: 2026-10-24T23:32:53Z

### CV.COUSR02C

- claim: COUSR02C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COUSR02C kind=cics lines=303 fe=stop reason="COUSR02C.cbl:67:8: copybook DFHAID not found"
- source: $CD/app/cbl/COUSR02C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COUSR02C.cbl"`
- expected: `COUSR02C kind=cics lines=303 fe=stop reason="COUSR02C.cbl:67:8: copybook DFHAID not found"`
- checked: 2026-10-24T23:32:53Z

### CV.COUSR03C

- claim: COUSR03C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COUSR03C kind=cics lines=251 fe=stop reason="COUSR03C.cbl:67:8: copybook DFHAID not found"
- source: $CD/app/cbl/COUSR03C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/COUSR03C.cbl"`
- expected: `COUSR03C kind=cics lines=251 fe=stop reason="COUSR03C.cbl:67:8: copybook DFHAID not found"`
- checked: 2026-10-24T23:32:53Z

### CV.CSUTLDTC

- claim: CSUTLDTC: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: CSUTLDTC kind=batch lines=114 fe=stop reason="CSUTLDTC.cbl:29:31: OCCURS DEPENDING ON is not supported"
- source: $CD/app/cbl/CSUTLDTC.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/cbl/CSUTLDTC.cbl"`
- expected: `CSUTLDTC kind=batch lines=114 fe=stop reason="CSUTLDTC.cbl:29:31: OCCURS DEPENDING ON is not supported"`
- checked: 2026-10-24T23:32:53Z

### CV.CBPAUP0C

- claim: CBPAUP0C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: CBPAUP0C kind=ims lines=266 fe=stop reason="CBPAUP0C.cbl:228:22: unknown data name DIBSTAT"
- source: $CD/app/app-authorization-ims-db2-mq/cbl/CBPAUP0C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/app-authorization-ims-db2-mq/cbl/CBPAUP0C.cbl"`
- expected: `CBPAUP0C kind=ims lines=266 fe=stop reason="CBPAUP0C.cbl:228:22: unknown data name DIBSTAT"`
- checked: 2026-10-24T23:32:53Z

### CV.COPAUA0C

- claim: COPAUA0C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COPAUA0C kind=cics+ims+mq lines=771 fe=stop reason="COPAUA0C.cbl:149:12: copybook CMQODV not found"
- source: $CD/app/app-authorization-ims-db2-mq/cbl/COPAUA0C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/app-authorization-ims-db2-mq/cbl/COPAUA0C.cbl"`
- expected: `COPAUA0C kind=cics+ims+mq lines=771 fe=stop reason="COPAUA0C.cbl:149:12: copybook CMQODV not found"`
- checked: 2026-10-24T23:32:53Z

### CV.COPAUS0C

- claim: COPAUS0C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COPAUS0C kind=cics+ims lines=792 fe=stop reason="COPAUS0C.cbl:168:8: copybook DFHAID not found"
- source: $CD/app/app-authorization-ims-db2-mq/cbl/COPAUS0C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/app-authorization-ims-db2-mq/cbl/COPAUS0C.cbl"`
- expected: `COPAUS0C kind=cics+ims lines=792 fe=stop reason="COPAUS0C.cbl:168:8: copybook DFHAID not found"`
- checked: 2026-10-24T23:32:53Z

### CV.COPAUS1C

- claim: COPAUS1C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COPAUS1C kind=cics+ims lines=461 fe=stop reason="COPAUS1C.cbl:148:8: copybook DFHAID not found"
- source: $CD/app/app-authorization-ims-db2-mq/cbl/COPAUS1C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/app-authorization-ims-db2-mq/cbl/COPAUS1C.cbl"`
- expected: `COPAUS1C kind=cics+ims lines=461 fe=stop reason="COPAUS1C.cbl:148:8: copybook DFHAID not found"`
- checked: 2026-10-24T23:32:53Z

### CV.COPAUS2C

- claim: COPAUS2C: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COPAUS2C kind=cics+db2 lines=201 fe=stop reason="COPAUS2C.cbl:65:12: unexpected 'SQL INCLUDE SQLCA' in the DATA DIVISION"
- source: $CD/app/app-authorization-ims-db2-mq/cbl/COPAUS2C.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/app-authorization-ims-db2-mq/cbl/COPAUS2C.cbl"`
- expected: `COPAUS2C kind=cics+db2 lines=201 fe=stop reason="COPAUS2C.cbl:65:12: unexpected 'SQL INCLUDE SQLCA' in the DATA DIVISION"`
- checked: 2026-10-24T23:32:53Z

### CV.DBUNLDGS

- claim: DBUNLDGS: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: DBUNLDGS kind=ims lines=198 fe=ok unsupported=2 resolves=yes signal=fault:Cobol.Fault.unsupported "ENTRY (line 165): ENTRY"
- source: $CD/app/app-authorization-ims-db2-mq/cbl/DBUNLDGS.CBL
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/app-authorization-ims-db2-mq/cbl/DBUNLDGS.CBL"`
- expected: `DBUNLDGS kind=ims lines=198 fe=ok unsupported=2 resolves=yes signal=fault:Cobol.Fault.unsupported "ENTRY (line 165): ENTRY"`
- checked: 2026-10-24T23:32:53Z

### CV.PAUDBLOD

- claim: PAUDBLOD: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: PAUDBLOD kind=ims lines=251 fe=ok unsupported=2 resolves=yes signal=fault:Cobol.Fault.unsupported "ENTRY (line 171): ENTRY"
- source: $CD/app/app-authorization-ims-db2-mq/cbl/PAUDBLOD.CBL
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/app-authorization-ims-db2-mq/cbl/PAUDBLOD.CBL"`
- expected: `PAUDBLOD kind=ims lines=251 fe=ok unsupported=2 resolves=yes signal=fault:Cobol.Fault.unsupported "ENTRY (line 171): ENTRY"`
- checked: 2026-10-24T23:32:53Z

### CV.PAUDBUNL

- claim: PAUDBUNL: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: PAUDBUNL kind=ims lines=207 fe=ok unsupported=2 resolves=yes signal=fault:Cobol.Fault.unsupported "ENTRY (line 158): ENTRY"
- source: $CD/app/app-authorization-ims-db2-mq/cbl/PAUDBUNL.CBL
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/app-authorization-ims-db2-mq/cbl/PAUDBUNL.CBL"`
- expected: `PAUDBUNL kind=ims lines=207 fe=ok unsupported=2 resolves=yes signal=fault:Cobol.Fault.unsupported "ENTRY (line 158): ENTRY"`
- checked: 2026-10-24T23:32:54Z

### CV.COBTUPDT

- claim: COBTUPDT: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COBTUPDT kind=db2 lines=177 fe=stop reason="COBTUPDT.cbl:50:13: unexpected 'SQL INCLUDE SQLCA' in the DATA DIVISION"
- source: $CD/app/app-transaction-type-db2/cbl/COBTUPDT.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/app-transaction-type-db2/cbl/COBTUPDT.cbl"`
- expected: `COBTUPDT kind=db2 lines=177 fe=stop reason="COBTUPDT.cbl:50:13: unexpected 'SQL INCLUDE SQLCA' in the DATA DIVISION"`
- checked: 2026-10-24T23:32:54Z

### CV.COTRTLIC

- claim: COTRTLIC: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COTRTLIC kind=cics+db2 lines=1597 fe=stop reason="COTRTLIC.cbl:425:8: copybook DFHBMSCA not found"
- source: $CD/app/app-transaction-type-db2/cbl/COTRTLIC.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/app-transaction-type-db2/cbl/COTRTLIC.cbl"`
- expected: `COTRTLIC kind=cics+db2 lines=1597 fe=stop reason="COTRTLIC.cbl:425:8: copybook DFHBMSCA not found"`
- checked: 2026-10-24T23:32:54Z

### CV.COTRTUPC

- claim: COTRTUPC: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COTRTUPC kind=cics+db2 lines=1241 fe=stop reason="COTRTUPC.cbl:257:8: copybook DFHBMSCA not found"
- source: $CD/app/app-transaction-type-db2/cbl/COTRTUPC.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/app-transaction-type-db2/cbl/COTRTUPC.cbl"`
- expected: `COTRTUPC kind=cics+db2 lines=1241 fe=stop reason="COTRTUPC.cbl:257:8: copybook DFHBMSCA not found"`
- checked: 2026-10-24T23:32:54Z

### CV.COACCT01

- claim: COACCT01: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: COACCT01 kind=cics+mq lines=500 fe=stop reason="COACCT01.cbl:71:8: copybook CMQGMOV not found"
- source: $CD/app/app-vsam-mq/cbl/COACCT01.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/app-vsam-mq/cbl/COACCT01.cbl"`
- expected: `COACCT01 kind=cics+mq lines=500 fe=stop reason="COACCT01.cbl:71:8: copybook CMQGMOV not found"`
- checked: 2026-10-24T23:32:54Z

### CV.CODATE01

- claim: CODATE01: kind (from the source text), non-comment lines, front end, unsupported statements, resolver, outcome with no input files; theorems: none
- value: CODATE01 kind=cics+mq lines=409 fe=stop reason="CODATE01.cbl:71:8: copybook CMQGMOV not found"
- source: $CD/app/app-vsam-mq/cbl/CODATE01.cbl
- re-check: `"$C/tools/evidence/cov_one.sh" "$CD/app/app-vsam-mq/cbl/CODATE01.cbl"`
- expected: `CODATE01 kind=cics+mq lines=409 fe=stop reason="CODATE01.cbl:71:8: copybook CMQGMOV not found"`
- checked: 2026-10-24T23:32:54Z

### CV.CBSTM03AB

- claim: CBSTM03A with CBSTM03B linked in: outcome on CardDemo's data (section validation, V.stm*)
- value: signal=stop:Cobol.StopKind.goback events=7305 displays=11 writes=1:1212,2:6082 rewrites=0
- source: examples/carddemo/cbstm03ab.ir.json
- re-check: `"$C/tools/evidence/sample_runs.sh" cbstm03ab`
- expected: `signal=stop:Cobol.StopKind.goback events=7305 displays=11 writes=1:1212,2:6082 rewrites=0`
- checked: 2026-10-24T23:32:58Z

### CV.sum

- claim: Summary over the 44 programs: programs per kind; kind batch with front end ok, with 0 unsupported statements, resolving; covered = kind batch, front end ok, 0 unsupported statements, resolves; CBSTM03A resolves alone but runs only when linked with CBSTM03B (row CV.CBSTM03AB)
- value: kinds: batch 14, cics 17, cics+db2 3, cics+ims 2, cics+ims+mq 1, cics+mq 2, db2 1, ims 4, | batch 14: front end ok 13, 0 unsupported 12, resolve 11, covered 10 (3824 non-comment lines)
- source: tools/evidence/cov_one.sh over every program
- re-check: `for p in "$CD"/app/cbl/*.[cC][bB][lL] "$CD"/app/app-*/cbl/*.[cC][bB][lL]; do "$C/tools/evidence/cov_one.sh" "$p"; done > "$OUT/cov_all.txt" && echo "kinds: $(awk '{sub(/^kind=/, "", $2); print $2}' "$OUT/cov_all.txt" | LC_ALL=C sort | uniq -c | awk '{printf "%s %s, ", $2, $1}')$(awk '$2 == "kind=batch" {b++; if ($4 == "fe=ok") fe++; if ($4 == "fe=ok" && $5 == "unsupported=0") u0++; if ($6 == "resolves=yes") rs++; if ($4 == "fe=ok" && $5 == "unsupported=0" && $6 == "resolves=yes") {cov++; split($3, a, "="); ln += a[2]}} END {printf "| batch %d: front end ok %d, 0 unsupported %d, resolve %d, covered %d (%d non-comment lines)", b, fe, u0, rs, cov, ln}' "$OUT/cov_all.txt")"`
- expected: `kinds: batch 14, cics 17, cics+db2 3, cics+ims 2, cics+ims+mq 1, cics+mq 2, db2 1, ims 4, | batch 14: front end ok 13, 0 unsupported 12, resolve 11, covered 10 (3824 non-comment lines)`
- checked: 2026-10-24T23:33:03Z

### CV.lines

- claim: Non-comment lines of the 14 programs of kind batch (copybooks not counted)
- value: 4684 lines
- source: tools/evidence/cobol_lines.awk
- re-check: `cd "$CD/app/cbl" && awk -f "$C/tools/evidence/cobol_lines.awk" CBACT01C.cbl CBACT02C.cbl CBACT03C.cbl CBACT04C.cbl CBCUS01C.cbl CBEXPORT.cbl CBIMPORT.cbl CBSTM03A.CBL CBSTM03B.CBL CBTRN01C.cbl CBTRN02C.cbl CBTRN03C.cbl COBSWAIT.cbl CSUTLDTC.cbl`
- expected: `4684`
- checked: 2026-10-24T23:33:03Z


## validation

### V0

- claim: GnuCOBOL flags of the semantics tests: TRUNC(STD) runs use -std=ibm -fbinary-truncate -fno-arithmetic-osvs; TRUNC(BIN) runs use -std=ibm -fno-arithmetic-osvs
- value: COBC_FLAGS = {"std": ["-std=ibm", "-fbinary-truncate", "-fno-arithmetic-osvs"],  "bin": ["-std=ibm", "-fno-arithmetic-osvs"]}
- source: tools/difftest/difftest.py (COBC_FLAGS)
- re-check: `/usr/bin/grep -A1 '^COBC_FLAGS' "$C/tools/difftest/difftest.py" | tr -s ' ' | tr '\n' ' '`
- expected: `COBC_FLAGS = {"std": ["-std=ibm", "-fbinary-truncate", "-fno-arithmetic-osvs"],  "bin": ["-std=ibm", "-fno-arithmetic-osvs"]}`
- checked: 2026-10-24T23:33:03Z

### V.dt_std

- claim: Random programs (MOVE, COMPUTE, ADD/SUBTRACT, MULTIPLY, DIVIDE, IF on numeric and alphanumeric items), TRUNC(STD): the Lean semantics on the generated IR against GnuCOBOL on the generated COBOL, 200 programs, seed 11; status per program (per-case results: $OUT/dt_std/results.jsonl)
- value: {"ok":195,"ok-negzero":5}
- source: tools/difftest/difftest.py
- re-check: `mkdir -p "$OUT/tmp" && export TMPDIR="$OUT/tmp" && cd "$OUT" && python3 -I -B "$C/tools/difftest/difftest.py" --n 200 --seed 11 --out "$OUT/dt_std" > "$OUT/dt_std.log" ; jq -s -c 'group_by(.status) | map({(.[0].status): length}) | add' "$OUT/dt_std/results.jsonl"`
- expected: `{"ok":195,"ok-negzero":5}`
- checked: 2026-10-24T23:33:25Z

### V.dt_bin

- claim: The same generator, TRUNC(BIN): 200 programs, seed 12 (per-case results: $OUT/dt_bin/results.jsonl)
- value: {"mismatch":2,"ok":198}
- source: tools/difftest/difftest.py
- re-check: `mkdir -p "$OUT/tmp" && export TMPDIR="$OUT/tmp" && cd "$OUT" && python3 -I -B "$C/tools/difftest/difftest.py" --n 200 --seed 12 --trunc bin --out "$OUT/dt_bin" > "$OUT/dt_bin.log" ; jq -s -c 'group_by(.status) | map({(.[0].status): length}) | add' "$OUT/dt_bin/results.jsonl"`
- expected: `{"mismatch":2,"ok":198}`
- checked: 2026-10-24T23:33:50Z

### V.ct

- claim: Random control flow (PERFORM THRU, nested PERFORM, GO TO, EXIT, sections): 100 programs, seed 13 (per-case results: $OUT/ct/results.jsonl)
- value: {"lean-unsupported-recursion":10,"lean-unsupported-resume":2,"ok":88}
- source: tools/difftest/ctrltest.py
- re-check: `mkdir -p "$OUT/tmp" && export TMPDIR="$OUT/tmp" && cd "$OUT" && python3 -I -B "$C/tools/difftest/ctrltest.py" --n 100 --seed 13 --out "$OUT/ct" > "$OUT/ct.log" ; jq -s -c 'group_by(.status) | map({(.[0].status): length}) | add' "$OUT/ct/results.jsonl"`
- expected: `{"lean-unsupported-recursion":10,"lean-unsupported-resume":2,"ok":88}`
- checked: 2026-10-24T23:34:05Z

### V.dt_fe

- claim: Front end: the IR that tools/cobolfe extracts from each generated COBOL program, run by the semantics, against GnuCOBOL and the generated IR: 100 programs, seed 14 (per-case results: $OUT/dt_fe/results.jsonl)
- value: {"ok":98,"ok-negzero":2}
- source: tools/difftest/difftest.py
- re-check: `mkdir -p "$OUT/tmp" && export TMPDIR="$OUT/tmp" && cd "$OUT" && python3 -I -B "$C/tools/difftest/difftest.py" --n 100 --seed 14 --frontend --out "$OUT/dt_fe" > "$OUT/dt_fe.log" ; jq -s -c 'group_by(.status) | map({(.[0].status): length}) | add' "$OUT/dt_fe/results.jsonl"`
- expected: `{"ok":98,"ok-negzero":2}`
- checked: 2026-10-24T23:34:24Z

### V.ct_fe

- claim: Front end on random control flow: 60 programs, seed 15 (per-case results: $OUT/ct_fe/results.jsonl)
- value: {"lean-unsupported-recursion":2,"ok":58}
- source: tools/difftest/ctrltest.py
- re-check: `mkdir -p "$OUT/tmp" && export TMPDIR="$OUT/tmp" && cd "$OUT" && python3 -I -B "$C/tools/difftest/ctrltest.py" --n 60 --seed 15 --frontend --out "$OUT/ct_fe" > "$OUT/ct_fe.log" ; jq -s -c 'group_by(.status) | map({(.[0].status): length}) | add' "$OUT/ct_fe/results.jsonl"`
- expected: `{"lean-unsupported-recursion":2,"ok":58}`
- checked: 2026-10-24T23:34:37Z

### V.ft

- claim: Files (sequential and indexed: OPEN, READ, WRITE, REWRITE, DELETE, START, FILE STATUS): 100 programs, seed 101; generator classes for documented GnuCOBOL deviations are not generated (row V.ft_excl) (per-case results: $OUT/ft/results.jsonl)
- value: {"ok":99,"ok-abend":1}
- source: tools/difftest/filetest.py
- re-check: `mkdir -p "$OUT/tmp" && export TMPDIR="$OUT/tmp" && cd "$OUT" && python3 -I -B "$C/tools/difftest/filetest.py" --n 100 --seed 101 --out "$OUT/ft" > "$OUT/ft.log" ; jq -s -c 'group_by(.status) | map({(.[0].status): length}) | add' "$OUT/ft/results.jsonl"`
- expected: `{"ok":99,"ok-abend":1}`
- checked: 2026-10-24T23:35:00Z

### V.us

- claim: UNSTRING (25 statements per program): 60 programs, seed 1 (per-case results: $OUT/us/results.jsonl)
- value: {"ok":60}
- source: tools/difftest/unstringtest.py
- re-check: `mkdir -p "$OUT/tmp" && export TMPDIR="$OUT/tmp" && cd "$OUT" && python3 -I -B "$C/tools/difftest/unstringtest.py" --n 60 --seed 1 --out "$OUT/us" > "$OUT/us.log" ; jq -s -c 'group_by(.status) | map({(.[0].status): length}) | add' "$OUT/us/results.jsonl"`
- expected: `{"ok":60}`
- checked: 2026-10-24T23:35:13Z

### V.in

- claim: INSPECT (25 statements per program): 60 programs, seed 2; class G-lead not generated (row V.in_excl) (per-case results: $OUT/in/results.jsonl)
- value: {"ok":60}
- source: tools/difftest/inspecttest.py
- re-check: `mkdir -p "$OUT/tmp" && export TMPDIR="$OUT/tmp" && cd "$OUT" && python3 -I -B "$C/tools/difftest/inspecttest.py" --n 60 --seed 2 --out "$OUT/in" > "$OUT/in.log" ; jq -s -c 'group_by(.status) | map({(.[0].status): length}) | add' "$OUT/in/results.jsonl"`
- expected: `{"ok":60}`
- checked: 2026-10-24T23:35:25Z

### V.st

- claim: STRING with value delimiters and POINTER (25 statements per program): 60 programs, seed 5 (per-case results: $OUT/st/results.jsonl)
- value: {"ok":60}
- source: tools/difftest/stringtest.py
- re-check: `mkdir -p "$OUT/tmp" && export TMPDIR="$OUT/tmp" && cd "$OUT" && python3 -I -B "$C/tools/difftest/stringtest.py" --n 60 --seed 5 --out "$OUT/st" > "$OUT/st.log" ; jq -s -c 'group_by(.status) | map({(.[0].status): length}) | add' "$OUT/st/results.jsonl"`
- expected: `{"ok":60}`
- checked: 2026-10-24T23:35:36Z

### V.ex_acctint

- claim: ACCTINT: its IR against its COBOL source under GnuCOBOL, 100 random records (per-case results: $OUT/ex_acctint/results.jsonl)
- value: {"ok":100}
- source: examples/acctint/validate.py
- re-check: `mkdir -p "$OUT/tmp" && export TMPDIR="$OUT/tmp" && cd "$OUT" && python3 -I -B "$C/examples/acctint/validate.py" --n 100 --out "$OUT/ex_acctint" > "$OUT/ex_acctint.log" ; jq -s -c 'group_by(.status) | map({(.[0].status): length}) | add' "$OUT/ex_acctint/results.jsonl"`
- expected: `{"ok":100}`
- checked: 2026-10-24T23:35:49Z

### V.ex_binary

- claim: BINCNT: its IR against its COBOL source under GnuCOBOL, 100 random inputs (per-case results: $OUT/ex_binary/results.jsonl)
- value: {"ok":100}
- source: examples/binary/validate.py
- re-check: `mkdir -p "$OUT/tmp" && export TMPDIR="$OUT/tmp" && cd "$OUT" && python3 -I -B "$C/examples/binary/validate.py" --n 100 --out "$OUT/ex_binary" > "$OUT/ex_binary.log" ; jq -s -c 'group_by(.status) | map({(.[0].status): length}) | add' "$OUT/ex_binary/results.jsonl"`
- expected: `{"ok":100}`
- checked: 2026-10-24T23:36:04Z

### V.ex_recsum

- claim: RECSUM: its IR against its COBOL source under GnuCOBOL, 100 random files of 0 to 30 records (per-case results: $OUT/ex_recsum/results.jsonl)
- value: {"ok":100}
- source: examples/recsum/validate.py
- re-check: `mkdir -p "$OUT/tmp" && export TMPDIR="$OUT/tmp" && cd "$OUT" && python3 -I -B "$C/examples/recsum/validate.py" --n 100 --out "$OUT/ex_recsum" > "$OUT/ex_recsum.log" ; jq -s -c 'group_by(.status) | map({(.[0].status): length}) | add' "$OUT/ex_recsum/results.jsonl"`
- expected: `{"ok":100}`
- checked: 2026-10-24T23:36:10Z

### V.tt

- claim: Lean transcriptions of AcctInt.java and the Rust rewrite against the real Java (javac/java) and Rust (rustc, from $HOME/.cargo/bin) code: 500 random inputs (per-case results: $OUT/tt/results.jsonl)
- value: {"ok":500}
- source: $HOME/.cargo/bin:$PATH
- re-check: `mkdir -p "$OUT/tmp" && export TMPDIR="$OUT/tmp" && cd "$OUT" && PATH="$HOME/.cargo/bin:$PATH" python3 -I -B "$C/tools/targettest/targettest.py" --n 500 --out "$OUT/tt" > "$OUT/tt.log" ; jq -s -c 'group_by(.status) | map({(.[0].status): length}) | add' "$OUT/tt/results.jsonl"`
- expected: `{"ok":500}`
- checked: 2026-10-24T23:36:14Z

### V.ft_excl

- claim: File-test generator classes left out because GnuCOBOL deviates from IBM there (class and reason in the source)
- value: G-dup21 G-extend G-lastkey G-rwkey G-rwalt G-rw21 G-open41
- source: tools/difftest/filetest.py:53
- re-check: `/usr/bin/grep -oE '^    "G-[a-z0-9]+"' "$C/tools/difftest/filetest.py" | tr -d ' "' | tr '\n' ' '`
- expected: `G-dup21 G-extend G-lastkey G-rwkey G-rwalt G-rw21 G-open41`
- checked: 2026-10-24T23:36:14Z

### V.in_excl

- claim: INSPECT-test classes for GnuCOBOL deviations (G-lead is left out by default)
- value: G-lead G-order G-chars2
- source: tools/difftest/inspecttest.py:33
- re-check: `/usr/bin/grep -oE '^    "G-[a-z0-9]+"' "$C/tools/difftest/inspecttest.py" | tr -d ' "' | tr '\n' ' '`
- expected: `G-lead G-order G-chars2`
- checked: 2026-10-24T23:36:14Z

### V.st_negzero

- claim: Status ok-negzero (counted as agreeing): the storage bytes differ but every field decodes to the same value (GnuCOBOL keeps a negative zero that the model normalizes); line that sets it
- value: 600
- source: tools/difftest/difftest.py
- re-check: `/usr/bin/grep -n 'status = "ok-negzero"' "$C/tools/difftest/difftest.py" | cut -d: -f1`
- expected: `600`
- checked: 2026-10-24T23:36:14Z

### V.st_recursion

- claim: Status lean-unsupported-recursion (declined, not compared): the program re-enters an active PERFORM, which the model reports as unsupported (implementation-specific on IBM); line that sets it
- value: 268
- source: tools/difftest/ctrltest.py
- re-check: `/usr/bin/grep -n 'return ("lean-unsupported-recursion", None)' "$C/tools/difftest/ctrltest.py" | cut -d: -f1`
- expected: `268`
- checked: 2026-10-24T23:36:14Z

### V.st_okabend

- claim: Status ok-abend (counted as agreeing): GnuCOBOL and the model stop at the same statement with the same I/O status; line that sets it
- value: 826
- source: tools/difftest/filetest.py
- re-check: `/usr/bin/grep -n 'return ("ok-abend", None)' "$C/tools/difftest/filetest.py" | cut -d: -f1`
- expected: `826`
- checked: 2026-10-24T23:36:14Z

### V.st_resume

- claim: Status lean-unsupported-resume (declined, not compared): control reaches the end of a paragraph whose return slot belongs to an abandoned PERFORM; IBM would resume that PERFORM, which the model reports as unsupported; line that sets it
- value: 266
- source: tools/difftest/ctrltest.py
- re-check: `/usr/bin/grep -n 'return ("lean-unsupported-resume", None)' "$C/tools/difftest/ctrltest.py" | cut -d: -f1`
- expected: `266`
- checked: 2026-10-24T23:36:14Z

### V.dt_bin_mm

- claim: The 2 mismatches of V.dt_bin (cases 101 and 197, kept as tools/difftest/bin_cases/T00101.cob and T00197.cob): a COMP-5 item overflows to a value outside its PICTURE. GnuCOBOL DISPLAYs the full binary value but uses it truncated to the PICTURE digits in the next arithmetic statement (101: N4 = 5367323.33 + N2 with N2 = -15755.407 instead of -1015755.407; 197: N5 = 284683.386 - N2 with N2 = -326483.8 instead of -61326483.8); the model uses the full binary value (under TRUNC(BIN) binary items are not truncated to their PICTURE). README lists out-of-PICTURE binary reads under TRUNC(BIN) as not validated
- value: 101: GnuCOBOL shows N2=-1015755407, final N4 GnuCOBOL=535156792 model=435156792 | 197: GnuCOBOL shows N2=-0613264838, final N5 GnuCOBOL=+611167186 model=284683386
- source: tools/evidence/bin_trace.sh, tools/difftest/bin_cases/
- re-check: `"$C/tools/evidence/bin_trace.sh"`
- expected: `101: GnuCOBOL shows N2=-1015755407, final N4 GnuCOBOL=535156792 model=435156792 | 197: GnuCOBOL shows N2=-0613264838, final N5 GnuCOBOL=+611167186 model=284683386`
- checked: 2026-10-24T23:36:14Z

### V.hand

- claim: Hand-written cases run by GnuCOBOL and by the front end + semantics, compared line by line: NEXT SENTENCE in inline PERFORMs, ALTER, serial SEARCH, SEARCH ALL
- value: 28 lines compared, 0 differ
- source: tools/difftest/{nextsent_cases/ns1.cob,alter_cases/alter1.cob,search_cases/srch1.cob,search_cases/srchall1.cob}
- re-check: `mkdir -p "$OUT/tmp" && export TMPDIR="$OUT/tmp" && cd "$OUT" && python3 -I -B "$C/tools/difftest/filetest.py" --out "$OUT/hand" --run "$C/tools/difftest/nextsent_cases/ns1.cob" "$C/tools/difftest/alter_cases/alter1.cob" "$C/tools/difftest/search_cases/srch1.cob" "$C/tools/difftest/search_cases/srchall1.cob" > "$OUT/hand.txt" 2>&1; awk -F'|' '/^   / && NF == 2 && $1 !~ /GnuCOBOL/ {a = $1; b = $2; gsub(/^ +| +$/, "", a); gsub(/^ +| +$/, "", b); n++; if (a != b) d++} END {print n " lines compared, " d + 0 " differ"}' "$OUT/hand.txt"`
- expected: `28 lines compared, 0 differ`
- checked: 2026-10-24T23:36:15Z

### V.stm

- claim: CBSTM03A + CBSTM03B on CardDemo's data: the semantics (ASCII IR from the unmodified sources) against GnuCOBOL compiling CBSTM03B and CBSTM03A without lines 266-291 (z/OS control-block walk); records of both output files compared byte by byte
- value: end: stop:Cobol.StopKind.goback file 1 (stmt.out): 1212 records, GnuCOBOL 1212, 0 differ file 2 (html.out): 6082 records, GnuCOBOL 6082, 0 differ displays after the walk: 0, GnuCOBOL 0, same AGREE
- source: tools/evidence/stm_check.sh, tools/difftest/stm_ascii.py, stm_gnucobol.sh, stm_compare.py
- re-check: `"$C/tools/evidence/stm_check.sh"`
- expected: `end: stop:Cobol.StopKind.goback file 1 (stmt.out): 1212 records, GnuCOBOL 1212, 0 differ file 2 (html.out): 6082 records, GnuCOBOL 6082, 0 differ displays after the walk: 0, GnuCOBOL 0, same AGREE`
- checked: 2026-10-24T23:36:21Z

### V.run.cbtrn02c

- claim: CBTRN02C on CardDemo's 300 daily transactions (README commands): end, events, DISPLAYs, WRITEs per file, REWRITEs, RETURN-CODE; tested (one run), not proved
- value: signal=stop:Cobol.StopKind.goback events=878 displays=54 writes=2:262,4:38,6:50 rewrites=474 return-code=4
- source: tools/evidence/sample_runs.sh
- re-check: `"$C/tools/evidence/sample_runs.sh" cbtrn02c`
- expected: `signal=stop:Cobol.StopKind.goback events=878 displays=54 writes=2:262,4:38,6:50 rewrites=474 return-code=4`
- checked: 2026-10-24T23:36:22Z

### V.run.cbtrn03c

- claim: CBTRN03C on CBTRN02C's 262 transaction records (README commands); tested (one run), not proved
- value: signal=stop:Cobol.StopKind.goback events=718 displays=267 writes=5:451 rewrites=0
- source: tools/evidence/sample_runs.sh
- re-check: `"$C/tools/evidence/sample_runs.sh" cbtrn03c`
- expected: `signal=stop:Cobol.StopKind.goback events=718 displays=267 writes=5:451 rewrites=0`
- checked: 2026-10-24T23:36:22Z

### V.run.cbact01c

- claim: CBACT01C on CardDemo's 50 accounts with the COBDATFT model (README commands); tested (one run), not proved
- value: signal=stop:Cobol.StopKind.goback events=1002 displays=752 writes=2:50,3:50,4:100 rewrites=0
- source: tools/evidence/sample_runs.sh
- re-check: `"$C/tools/evidence/sample_runs.sh" cbact01c`
- expected: `signal=stop:Cobol.StopKind.goback events=1002 displays=752 writes=2:50,3:50,4:100 rewrites=0`
- checked: 2026-10-24T23:36:22Z

### V.run.cbstm03ab

- claim: CBSTM03A + CBSTM03B on CBTRN02C's output and CardDemo's data (README commands); tested (one run), not proved
- value: signal=stop:Cobol.StopKind.goback events=7305 displays=11 writes=1:1212,2:6082 rewrites=0
- source: tools/evidence/sample_runs.sh
- re-check: `"$C/tools/evidence/sample_runs.sh" cbstm03ab`
- expected: `signal=stop:Cobol.StopKind.goback events=7305 displays=11 writes=1:1212,2:6082 rewrites=0`
- checked: 2026-10-24T23:36:26Z

### V.run.cbact04c

- claim: CBACT04C on CardDemo's TCATBALF (50 category records), ACCTDATA, CARDXREF and DISCGRP: end, events, DISPLAYs, WRITEs per file, REWRITEs (49 for 50 accounts: the last account is not rewritten), and the number of DISPLAYs of 'TRY WITH DEFAULT GROUP CODE' (every record takes the DEFAULT disclosure-group path); tested (one run), not proved
- value: signal=stop:Cobol.StopKind.goback events=251 displays=152 writes=5:50 rewrites=49 default-group-retries=50
- source: tools/evidence/sample_runs.sh
- re-check: `"$C/tools/evidence/sample_runs.sh" cbact04c`
- expected: `signal=stop:Cobol.StopKind.goback events=251 displays=152 writes=5:50 rewrites=49 default-group-retries=50`
- checked: 2026-10-24T23:36:26Z


## effort

### E1

- claim: COBOL side: non-comment lines of the 8 CardDemo programs with all-input theorems, copybooks not counted (rule: tools/evidence/cobol_lines.awk)
- value: 2878 lines
- source: $CD/app/cbl/{CBACT01C,CBACT02C,CBACT03C,CBACT04C,CBCUS01C,CBTRN01C,CBTRN02C,CBTRN03C}.cbl
- re-check: `cd "$CD/app/cbl" && awk -f "$C/tools/evidence/cobol_lines.awk" CBACT01C.cbl CBACT02C.cbl CBACT03C.cbl CBACT04C.cbl CBCUS01C.cbl CBTRN01C.cbl CBTRN02C.cbl CBTRN03C.cbl`
- expected: `2878`
- checked: 2026-10-24T23:36:26Z

### E2

- claim: COBOL side with copybooks: sum over the 8 programs of the program's lines plus the lines of the copybooks it copies (a copybook copied by two programs counts twice)
- value: 3229 lines
- source: $CD/app/cbl, $CD/app/cpy
- re-check: `cd "$CD/app" && t=0; for p in CBACT01C CBACT02C CBACT03C CBACT04C CBCUS01C CBTRN01C CBTRN02C CBTRN03C; do t=$((t + $(awk -f "$C/tools/evidence/cobol_lines.awk" cbl/$p.cbl))); for c in $(awk '{l = substr($0, 8, 65)} l ~ /COPY/ {for (i = 1; i <= NF; i++) if ($i == "COPY") {x = $(i + 1); gsub(/\./, "", x); print x}}' cbl/$p.cbl | LC_ALL=C sort -u); do f=$(ls cpy | awk -v c="$c" 'toupper($0) == toupper(c) ".CPY"'); [ -n "$f" ] && t=$((t + $(awk -f "$C/tools/evidence/cobol_lines.awk" cpy/$f))); done; done; echo $t`
- expected: `3229`
- checked: 2026-10-24T23:36:27Z

### E3

- claim: Lean side, program-specific: non-blank non-comment lines of the proof files of those 8 programs (statements, models, lemmas, invariants, proofs, intermediate theorems; rule: tools/evidence/lean_lines.awk)
- value: 5760 lines
- source: Examples/{Cbact01c,Cbact02c,Cbact03c,Cbcus01c,Cbact04c,Cbact04cAny,Cbact04cAll,Cbact04cEvents,Cbact04cEvery,Cbtrn01c,Cbtrn02c,Cbtrn02cDup,Cbtrn03c,Cbtrn03cStop,Cbtrn03cAny,Cbtrn03cEvery}.lean
- re-check: `cd "$C/Examples" && awk -f "$C/tools/evidence/lean_lines.awk" Cbact01c.lean Cbact02c.lean Cbact03c.lean Cbcus01c.lean Cbact04c.lean Cbact04cAny.lean Cbact04cAll.lean Cbact04cEvents.lean Cbact04cEvery.lean Cbtrn01c.lean Cbtrn02c.lean Cbtrn02cDup.lean Cbtrn03c.lean Cbtrn03cStop.lean Cbtrn03cAny.lean Cbtrn03cEvery.lean`
- expected: `5760`
- checked: 2026-10-24T23:36:27Z

### E4

- claim: Lean side, library (shared by all proofs, not program-specific): non-blank non-comment lines of Cobol.lean and Cobol/**/*.lean
- value: 6610 lines
- source: Cobol.lean, Cobol/
- re-check: `cd "$C" && awk -f tools/evidence/lean_lines.awk Cobol.lean $(find Cobol -name '*.lean' | LC_ALL=C sort)`
- expected: `6610`
- checked: 2026-10-24T23:36:27Z

### E5

- claim: Program-specific Lean lines per 1000 COBOL lines (integer division): E3 x 1000 / E1 (copybooks not counted) and E3 x 1000 / E2 (copybooks counted)
- value: 5760 Lean lines: 2001 per 1000 COBOL lines without copybooks (2878), 1783 per 1000 with copybooks (3229)
- source: rows E1, E2, E3 (same commands)
- re-check: `cd "$C/Examples" && l=$(awk -f "$C/tools/evidence/lean_lines.awk" Cbact01c.lean Cbact02c.lean Cbact03c.lean Cbcus01c.lean Cbact04c.lean Cbact04cAny.lean Cbact04cAll.lean Cbact04cEvents.lean Cbact04cEvery.lean Cbtrn01c.lean Cbtrn02c.lean Cbtrn02cDup.lean Cbtrn03c.lean Cbtrn03cStop.lean Cbtrn03cAny.lean Cbtrn03cEvery.lean); cd "$CD/app" && c=0; w=0; for p in CBACT01C CBACT02C CBACT03C CBACT04C CBCUS01C CBTRN01C CBTRN02C CBTRN03C; do n=$(awk -f "$C/tools/evidence/cobol_lines.awk" cbl/$p.cbl); c=$((c + n)); w=$((w + n)); for x in $(awk '{s = substr($0, 8, 65)} s ~ /COPY/ {for (i = 1; i <= NF; i++) if ($i == "COPY") {y = $(i + 1); gsub(/\./, "", y); print y}}' cbl/$p.cbl | LC_ALL=C sort -u); do f=$(ls cpy | awk -v c="$x" 'toupper($0) == toupper(c) ".CPY"'); [ -n "$f" ] && w=$((w + $(awk -f "$C/tools/evidence/cobol_lines.awk" cpy/$f))); done; done; echo "$l Lean lines: $((l * 1000 / c)) per 1000 COBOL lines without copybooks ($c), $((l * 1000 / w)) per 1000 with copybooks ($w)"`
- expected: `5760 Lean lines: 2001 per 1000 COBOL lines without copybooks (2878), 1783 per 1000 with copybooks (3229)`
- checked: 2026-10-24T23:36:27Z

