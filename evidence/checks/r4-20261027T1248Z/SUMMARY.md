RESULT: CONFIRMED with notes. cc9e349: hashes, sources, regeneration (Aeneas, Jimple, all 22 statements) and records (60/60, 300/300) as delivered; Rust.rust (Equiv) and Java.java (Sim, partial correctness) carry the 3 announced assumptions plus generated premises not in the announced list (section 7); 62/62 new modules compiled from source; 19/19 rows on the standard axioms; closure 411/411 kernel-replayed, controls behave. 0fd209e: diff = 16 Java/Term modules + JavaRun + README only; 17/17 compiled; java_terminates and java_total have runSpec.pre as their only hypothesis; 21/21 rows on the standard axioms; the 17 changed modules replayed rc 0, the other 410 of the 427 reused as the same files.

# Check of R4 CBSTM03B translation theorems (equiv-lean r4-cbstm03b cc9e349, partial Java; delta to 0fd209e, total Java)

Checked by a fork of the evidence owner, 2026-10-27 12:48Z-14:29Z (date -u). Check dir ~/fv_paper/evidence/checks/r4-20261027T1248Z;
copies in ~/fv_paper/replay/r4-20261027T1248Z (equivlean/ = rsync -rtL of the kit tree ~/equivlean_freeze_cc9e349-r4 without
.git/.tmp; equivlean_work/ = rsync -rtL of the four vendor packages and the Aeneas backend the lakefile names; 0 symlinks; hard
links became separate files). Every job ran under coreh_guard_v2 (logs in guard/).

## 1. Hashes and commits
- Kit manifest SHA256SUMS_cc9e349-r4.txt (sha256 9a3033a23ca72947..., 4359 lines; copy kit_SHA256SUMS_cc9e349-r4.txt): 4359/4359 OK in
  the kit tree before (manifest_check_before.txt; run with the kit tree as working directory, read-only) and after (absolute
  paths, 14:24:44Z, manifest_check_after.txt), and in my copy before my compile (manifest_check_copy.txt, absolute paths).
- Tracked files: git ls-tree -r cc9e349 = 2489 files; git hash-object of each file in the kit tree = the commit's blob, 2489/2489
  (tracked_vs_cc9e349.txt). ~/equivlean has no promisor or partial clone; git read-only with GIT_ALLOW_PROTOCOL=file.
- cc9e349 vs 751764f (the migration theorems): 1348 added, 38 modified files (diff_751764f_cc9e349.txt). Modified: lakefile.toml and
  lake-manifest (JimpleLean pin 0149Z -> 2312Z, as checked for the Java total-correctness work), 30 JL modules of the Java proofs of
  CBACT02C, CBACT03C and CBCUS01C (snapshot path and termination additions; diff_JL_751764f_cc9e349.txt), tools/modernize/genstmt.py
  (+311, -0 lines), genall.sh, RECIPE.md, README.md, HANDOFF, scripts/lean1.sh. No statement module of the 16 migration theorems
  changed, and the generator regenerates all 22 committed statements byte for byte (section 3).

## 2. Statements (fresh process; stmt/stmt.out, stmt/defs.out)
- Both statements share the COBOL side: for every environment env, every storage m of 2248 bytes, every state fs of the four files
  and all integers k, v such that every TRNX record has 350 bytes, XREF 50, CUST 500 and ACCT 300; for a keyed READ (operation byte
  K at 1216) of CUSTFILE or ACCTFILE, KEY-LN (4 bytes at 1244) decodes to k with 1 <= k <= 25; for a keyed READ of ACCTFILE, the
  first k key bytes (at 1219) decode as digits to v; and Domain env m fs k v (the hand-written domain: for a keyed READ of ACCTFILE,
  the first k key bytes are the CP037 digits 0xF0-0xF9). These binders and hypotheses are exactly those of coblean's
  cbstm03b_call (printed side by side in defs.out), plus Domain. The COBOL run is EquivLean.Cobol.run CardDemo.Cbstm03b env 50
  (st0 m fs) = coblean's Program.run with fuel 50 (defs.out: `{ res := P.run env fuel st }`).
- Rust.rust : Rust.Statement: additionally for every open-outcome array oe, translation state st and parameter area q1 with
  EnvRel oe env (each OPEN outcome equals Env.openError of that file, and every failure status c satisfies c < 100), StateRel st
  (st0 m fs) (the four files' open flag, records, read position and end-of-file flag; the four FD record areas and the four FILE
  STATUS items at their storage offsets, with valid field values) and LkM03bAreaRel q1 (st0 m fs).mem: Equiv Rust.Rel
  (cbstm03b.call oe st q1) (the COBOL run). Equiv = Sim both ways (Core/Sim.lean: Sim R t s := Safe s -> Safe t /\ every outcome
  of t has a related outcome of s); Rust.Rel requires the Rust call to return .ok (no panic), the COBOL run to stop with GOBACK,
  and the new state and area to be related as before.
- Java.java : Java.Statement: additionally for every JVM state sigma and addresses oe, st, q1 with EnvAt (a 4-element array:
  null = the OPEN succeeds, or a boxed Integer c with c < 100 = Env.openError), StateAt (as StateRel, the records as Java arrays
  with fewer than 2^31 elements and positions below 2^31, plus NotRecOf: the FD record objects of CUST-FILE and ACCT-FILE are not
  elements of their files' record arrays), LkM03bAreaAt, and 11 class-initialization premises (sigma.initOf C = .done for
  Cbstm03b and its 10 inner classes): Sim (Java.Rel st q1) (the call of call(Integer[],State,LkM03bArea)) (the COBOL run) -
  partial correctness: when the COBOL run is safe, the Java run is safe and every terminating Java run returns normally
  with the state object and parameter area holding the COBOL state at GOBACK.
- Against the three announced assumptions: (1) open failures below 100: in EnvRel / EnvAt (both languages), as announced;
  (2) digit-only ACCT keys: the Domain premise of both statements (the one hand-written part), as announced; (3) Java only, the
  CUST/ACCT FD record objects are not elements of their files' record arrays: NotRecOf inside StateAt, as announced. Not in the
  announced list but part of the generated Java statement: the 11 class-initialization premises (the call happens after the
  translation's classes are initialized) and the JVM array bounds inside StateAt (fewer than 2^31 records, positions below 2^31).
  Both statements also require valid field values in the related translation state, and the COBOL side runs with fuel 50.

## 3. Provenance (prov/, rustregen/, jimpleregen/, stmtregen/)
- Sources = veriforch's finals (prov/sources_ir_copy.txt): examples/rust/mod_cbstm03b/src/lib.rs 17a74e6e = guided/rust/v4 (the
  final of versions.json) = the delivered rust/; Cargo.toml 3b919836 likewise; examples/java/mod_cbstm03b/Cbstm03b.java dab52857 =
  guided/java/v1 = the delivered java/. versions.json lists v5-v8 as harness retries excluded (NOTE.md).
- Aeneas regenerates (scripts/rustregen.sh, Charon + Aeneas fdebf20 binaries from equivlean_work/dl/rel/aeneas_bin, on a copy of the
  crate): charon rc 0, aeneas rc 0; Types.lean and Funs.lean of EquivLean/Demo/Gen/Aeneas/ModCbstm03b and cbstm03b.llbc (95d45c02)
  byte-identical (rustregen/result.txt).
- Jimple regenerates (scripts/jimpleregen.sh: javac --release 17 -nowarn and Soot 4.7.1 -pp -allow-phantom-refs -f J, the
  invocation of build_jimple.sh, outputs in the check dir): 11 classes, diff -r against EquivLean/Demo/Gen/Jimple/mod_cbstm03b
  empty (jimpleregen/result.txt).
- Statements regenerate (scripts/stmtregen.sh: tools/modernize/genall.sh with no arguments, in my copy; the copy's statement files
  made writable first): rc 0, all 11 rows; the 22 *Statement.lean files under EquivLean/Modernize, including CBSTM03B's Java and
  Rust statements and those of the 16 migration theorems, are byte-identical to the committed ones (stmtregen/regen_vs_orig.txt).
- IR: examples/cobol/carddemo/cbstm03b.ir.json 38fa862f = the checked snapshot coblean-pin2306Z-cbstm03b-20261027T0112Z's IR
  (checks/cbstm03b-20261027T0113Z showed it regenerates from the unmodified CBSTM03B.CBL with --sub).
- COBOL theorem copy: EquivLean/Demo/Cobol/Cbstm03b/Prog.lean vs the snapshot's Examples/Cbstm03b.lean (36018f28): only 3 added
  header comment lines and the IR path in the cobol_program line differ (prov/cobol_copy_diff.txt); cbstm03b_call prints exactly
  the standard axioms here too (defs.out).
- Java proofs: the 43 files of JimpleLean's package CBSTM03BJava-20261027T0929Z (SHA256SUMS 07a70325, copy prov/
  jl_pkg_SHA256SUMS_07a70325.txt; 42 modules of Modernize/Cbstm03b/Java and JavaRun.lean) equal the tree's copies, 43/43.

## 4. Build, axioms and kernel replay (closure/, compile/, axioms/, replay/, replay_controls/)
- Closure: Lean's env.allImportedModuleNames from the modules of Rust.rust and Java.java (closure/Mods*.lean), restricted to the
  project packages as in the earlier checks (Mathlib, Batteries, Init, Lean and Std excluded): Rust 336, Java 392, union 411 =
  Aeneas 249, AeneasMeta 17, Cobol 41, Jimple 27, EquivLean 77 (62 added in cc9e349, new_modules.txt; 15 unchanged since 751764f).
- Compile from source: the 62 new modules, compiled from the committed sources in my copy level by level (16 levels), 2 at a time
  within the compile (section 7 for its overlap with the replay), one thread each, with the lakefile's options
  (autoImplicit=false, relaxedAutoImplicit=false, Elab.async=false) and the repository root as working directory, against the
  copied oleans of the other 349: 62/62 rc 0, no error and no sorry (509 linter-warning lines), 4968 s in total (Java.Trnx
  2239 s), 13:00-14:12Z. My oleans replaced the copied ones in my tree; the axioms and the replay below use them. Against the
  producer's: 0/62 byte-identical (olean_diff_strings.txt). 59 differ by 80 or 96 bytes; their string tables differ only in the
  package name `equivlean` that lake records and, in 8, the module's own absolute source path (my copy's instead of the freeze
  tree's). Java.HFit, HFresh and HZeroPad also differ in auxiliary proof terms (other _proof_N numbering and omega lemma names;
  45760, 45760 and 4152 bytes). My compile is reproducible (Java.HZeroPad recompiled byte-identically, determinism.out), so
  these differences come from the producer's lake build; I did not trace them further.
- Axioms (axioms/rows/, one fresh lean process per row, after the compile): the 17 headline rows, Rust.rust and Java.java, 19/19,
  each depends on exactly [propext, Classical.choice, Quot.sound], rc 0.
- Kernel replay (tools/leancheck1lp.sh = leanchecker of v4.35.0, one module per process, 2 at a time within the replay, own guard each):
  411/411 rc 0; the replayed names equal the closure (replay_vs_closure.txt empty). The 349 unchanged modules were replayed on the
  copied oleans (done 13:20:57Z), the 62 new ones on mine (done 14:16:13Z); no earlier replay was reused. Controls: BadCtl (a
  theorem of type False added with debug.skipKernelTC) rc 1, "(kernel) declaration type mismatch, 'badCtl' has type True but it
  is expected to have type False"; GoodCtl (2 + 2 = 4 by rfl) rc 0.

## 5. Translation records (difftest/records.txt)
- Rust v4: attempt.json n 60 pass 60 and final n 300 pass 300, executions_disagree 0 (native and Aeneas-in-Lean), 474 model lines,
  0 human lines; 4 versions, 3 compile errors (Aeneas stage); $0.8991 for v1-v4. Java v1: 60/60 and 300/300 (JVM and JimpleLean),
  0 disagreements, 427 model lines, $0.1962. Java v2 (second guide, not used by the theorems): 60/60 and 300/300, 416 lines, $0.2009.
- The case files hold 60 round and 300 final inputs per run (counted); the 300 final cases are distinct and none equals a round
  case. The records keep no per-case outcomes, so the pass counts come from attempt.json; I did not re-run the differential.

## 6. Delta to the total commit 0fd209e (delta_0fd209e/)
- Kit manifest SHA256SUMS_0fd209e-r4t.txt (sha256 2cef6d1fe050400f..., 4391 lines; copy kit_SHA256SUMS_0fd209e-r4t.txt):
  4391/4391 OK in the kit tree before (manifest_check_before.txt) and after (absolute paths, 14:24:44Z,
  manifest_check_after.txt). Tracked files: git ls-tree -r 0fd209e = 2505 files, each equal to the commit's blob in the kit
  tree and in my delta tree (tracked_vs_0fd209e.txt, tracked_copy_vs_0fd209e.txt).
- Diff cc9e349..0fd209e (diff_cc9e349_0fd209e.txt): the 16 new modules Java/Term/{Acct, AcctDefs, AcctDigit, AcctEntry,
  AcctLoop, Call, Cust, CustDefs, CustEntry, CustLoop, Helpers, KCallees, KeySubF, Total, Trnx, Xref}.lean, JavaRun.lean and
  README.md, nothing else. JavaRun (diff_JavaRun.txt) imports Term.Total, proves java as statement_of_sat run_sat (same type
  Statement; JavaStatement.lean, JavaProof.lean and Domain.lean unchanged), and adds java_terminates and java_total.
- Delta tree ~/fv_paper/replay/r4-20261027T1248Z/equivlean_0fd209e: a hard-link copy (cp -al) of my cc9e349 copy, after my
  compile; JavaRun.lean, README.md, JavaRun.olean and JavaRun.ilean were moved aside (mv) before the 0fd209e versions were
  written, so no linked file was written to. Everything else is the same file (same inode) as in the cc9e349 check: the other 61
  of the 62 compiled oleans (re-hashed at the end: all 61 equal the hashes taken right after the compile, new_oleans_mine.tsv),
  the 15 unchanged EquivLean oleans, and the 334 vendor modules (the leanpath after its first entry is the same).
- Compile from source (compile/, compile_one.sh's command with the delta tree's paths, 10 levels): 17/17 rc 0, no error, no
  sorry, no warning, 812 s in total (Term.Trnx 133 s), done 14:25:33Z. Against the producer's 0fd209e oleans: 0/17
  byte-identical; each differs by 96 bytes and only in the package name `equivlean` (olean_diff_strings.txt). My compile is
  reproducible: Java.HZeroPad recompiled to the same bytes as my first compile (determinism.out), so the byte differences come
  from the producer's lake build, not from run-to-run variation.
- Statements (fresh process, Stmt.out, rc 0), as printed:
  java_terminates : ∀ (args : List Jimple.Value) (σ : Jimple.State), Java.runSpec.pre args σ → Jimple.MTerm Java.Gen.prog
    Java.callRef args σ
  java_total : ∀ (args : List Jimple.Value) (σ : Jimple.State), Java.runSpec.pre args σ → (∃ o, Jimple.MExec Java.Gen.prog
    Java.callRef args σ o) ∧ ∀ o, Jimple.MExec Java.Gen.prog Java.callRef args σ o → Java.runSpec.post args σ o
  In words: for every argument list and JVM state satisfying the contract's precondition, every execution of
  Cbstm03b.call(Integer[], State, LkM03bArea) terminates (MTerm, JimpleLean Termination.lean: every execution terminates and
  one exists); and the call has an outcome, and every outcome (MExec, the big-step semantics) satisfies the postcondition: a
  normal return without a value, the State object holding the model's state after the call ((Model.call oeM s a).1), SepM still
  holding, and the parameter area holding the model's area ((Model.call oeM s a).2); exceptional and wrong outcomes are excluded
  (Spec.of maps them to False).
- Hypotheses: runSpec.pre only. The printed types have no other binder, no instance argument and no section variable; no
  further hypotheses. runSpec.pre says the arguments are references oe, st, q such that: oe is a 4-element array of null (the
  OPEN succeeds) or a boxed Integer c with c < 100 (EnvAtM; assumption 1); st holds a model state s (StateAtM, with record
  arrays of fewer than 2^31 elements and positions below 2^31); SepM, the FD record objects of CUST-FILE and ACCT-FILE are not
  elements of their files' record arrays (assumption 3); q holds a valid area a (JRecAt, LkM03bArea.Valid); Glue.ValidSt s
  (valid field values, two-character statuses); Glue.KeyOk a (for a keyed READ of CUST or ACCT a key length in 1..25, and for
  ACCT the first k key bytes decode as a number and are the CP037 digits 0xF0-0xF9; assumption 2); InitsDone σ (the 11
  class-initialization premises). The postcondition is stated against the model Model.call; Glue.call_run relates the model to
  the COBOL run. java's type is unchanged (Java.Statement), and statement_of_sat builds runSpec.pre from that statement's
  hypotheses (JavaProof.lean:248), so the termination result covers the statement's whole domain; the commit does not state
  that composition as a theorem of its own.
- Axioms (axioms/rows/, the 21 rows of the 0fd209e audit, one fresh process each, on the delta tree): 21/21 (the 19 rows of
  section 4 plus java_terminates and java_total) depend on exactly [propext, Classical.choice, Quot.sound], rc 0
  (axioms/rows21_results.txt).
- Closure at 0fd209e (mods_java_delta.out): Java 408 = cc9e349's 392 plus the 16 Term modules, none dropped; the Rust closure
  is unchanged (no Rust, Aeneas or COBOL file changed); union 427, whose EquivLean part (93) equals the producer's
  replay_closure_0fd209e.txt.
- Kernel replay: the 17 changed modules (16 Term + JavaRun) on the delta tree, 17/17 rc 0 (replay/, done 14:27:35Z). The other
  410 of the 427 are the same files as in my cc9e349 replay (same inodes in the delta tree, the same vendor directories), each
  replayed there with rc 0, so they are reused.

## 7. Discrepancies, disclosures, compute
- Statement premises beyond the three announced assumptions (all generated, none hand-written): the Java statement's 11
  class-initialization premises (sigma.initOf C = .done for Cbstm03b and its 10 inner classes; InitsDone in runSpec.pre) and the
  JVM bounds inside StateAt/StateAtM (record arrays with fewer than 2^31 elements, positions below 2^31); in both languages valid
  field values in the related translation state (ValidSt) and, for keyed READs of CUST and ACCT, a key length in 1..25 (from
  coblean's cbstm03b_call); the COBOL side runs with fuel 50. Worth listing next to the three assumptions wherever they appear.
- Oleans: none of my 62 + 17 compiled oleans is byte-identical to the producer's (sections 4 and 6 say what differs). The
  statements, axioms and replay here rest on my own compiled oleans for every module added or changed since 751764f.
- Records: the run records keep no per-case outcomes, so the 60/60 and 300/300 come from attempt.json; the differential was not
  re-run.
- Rule exceeded: the limit of 2 parallel Lean jobs. Two 2-wide pipelines overlapped, so 3-4 single-threaded Lean processes ran
  at once for 1179 s in total: 13:02:32-13:20:56Z (the cc9e349 compile with the replay of the 349 unchanged modules) and
  14:13:41-14:16:11Z (the axiom rows, then the delta compile, with the replay of the 62 new modules); guard_intervals.txt. Every
  process stayed under its own guard and no cap was reached; the results do not depend on it.
- My procedure: (a) the first manifest check of the cc9e349 kit ran with the kit tree as working directory (read only; the
  after-checks use absolute paths); (b) compile attempt 1 used each module's directory as working directory and failed at
  JavaGen (jimple_import paths are relative to the repository root); I stopped my own process tree by PID, kept its outputs in
  compile_attempt1/ and recompiled all 62 from scratch; (c) I made my copy's statement files and build directories writable
  (chmod u+w) for the regeneration and the compile; (d) the 19 cc9e349 axiom-row guards shared one name, so 10 log files hold
  their logs, two per file (19 starts, 19 exits with rc 0); (e) the delta tree is a hard-link copy (section 6).
- Both kit trees unchanged at the end: sha256sum -c with absolute paths, 4359/4359 OK (cc9e349) and 4391/4391 OK (0fd209e) at
  14:24:44Z (manifest_check_after.txt, delta_0fd209e/manifest_check_after.txt). Nothing was written into either kit tree or into
  ~/equivlean; git was read-only with GIT_ALLOW_PROTOCOL=file; no lake command ran anywhere.
- Compute: 2.305 core-h metered by coreh_guard_v2 over 586 guarded jobs (578 logs; per-job caps 0.02-1.0 core-h, none reached),
  12:49:07-14:27:35Z: compile 1.400 (with attempt 1), replay 0.605, delta compile 0.225, everything else 0.075.
