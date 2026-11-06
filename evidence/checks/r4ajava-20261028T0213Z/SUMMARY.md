RESULT: CONFIRMED with notes. In equiv-lean 8ed869e (master, unified), EquivLean.Modernize.Cbstm03a.Java.{java : Statement, java_terminates, java_total, java_composite} depend on exactly [propext, Classical.choice, Quot.sound], with 0 sorry. java is the generated statement (Sim, partial correctness), with no hypothesis beyond it. The 252 changed modules of the 1,370-module closure compile from source with JimpleLean's precompiled library (as lake builds them) and replay rc 0: 252 replayed, 1,118 reused from the r4a replay. 8ed869e = a50f10e + exactly the Java maintainer session package + java_composite + README.

# Check of the CBSTM03A Java translation theorems (the JimpleLean maintainer session package cbstm03a_java_20261028T0124Z; equiv-lean 8ed869e)
An agent of the evidence-owner session, stamp 20261028T0213Z, 02:13Z-04:30Z (date -u). Method of checks/r4-20261027T1248Z and checks/r4a-20261028T0107Z.
Replay copy ~/fv_paper/replay/r4ajava-20261028T0213Z (cp -r of the r4a copy, 0 symlinks). Inputs read only (package, producer's replay dir,
equiv-lean worktree via git ls-tree/cat-file/diff, GIT_ALLOW_PROTOCOL=file, no fetch). Lean jobs under coreh_guard_v2, ulimit -v 32 GiB,
LEAN_NUM_THREADS=1, pjobs_v3 N 8 450 150 2. (This file was written by the evidence-owner session from the fork's final report, because the file tool refused report
files from the fork; content verbatim, condensed in layout.)

## 1. Package, overlay and merge commit: PASS
- Package: 243 .lean files + MANIFEST.md + REPLAY_SUMMARY.txt + SHA256SUMS; sha256sum -c 243/243 OK; 0 symlinks; MANIFEST table (243 rows) = SHA256SUMS.
- Overlay on a50f10e (2656/2656 = a50f10e blobs): 236 new, 6 identical, 1 replaced: Java/Iface3.lean (writeTransSpec precondition
  t.length < 10^6 instead of < 2^31; a helper contract, outside the statement).
- a50f10e..8ed869e changes 239 paths: the 237 package paths that differ from a50f10e; Composite.lean (only import Cbstm03a.JavaRun,
  Cbstm03a.Java.java_composite and one #print axioms line); README.md. All 243 package files = 8ed869e blobs; JavaRun 561ab352 = package's.
- Claimed hashes JavaRun 561ab352, Composite b660a2d2, RustRun 2063be2f (unchanged), README 1e276773 match. Copy moved to 8ed869e: 2892/2892.
- 8ed869e pins JimpleLean-20261026T2035Z (vendor SHA256SUMS 146/146). 9,495 oleans in 13 trees (Aeneas backend 269 incl. AeneasMeta,
  Mathlib 8,643) byte-identical to the r4a copy's.

## 2. Provenance: PASS
- Java source examples/java/mod_cbstm03a/Cbstm03a.java 08402d30 = veriforch runs/modernize/CBSTM03A/java/ = guided/java/v3 (first guide,
  attempt 3). The second guide's final (3eadd7a0) is not used.
- Jimple: javac 17 (--release 17 -proc:none -g -encoding UTF-8) + Soot 4.7.1 regenerate the 6 classes byte for byte; with build_jimple.sh's
  flags (no -g) local names differ; this kit's recipe is the producer's prep_v1.sh (with -g).
- Statement: JavaStatement.lean 6ebb42b4, same in a50f10e and 8ed869e, = the r4a check's regeneration (genall 24/24); a50f10e..8ed869e
  changes no generator input or generated file.

## 3. Statements (fresh process, stmt/print.out 8849268c)
- java : Statement; conclusion Sim Rel <Gen.prog, runRef, [.ref a1 .. a4], σ> (Cobol.run Stm {addrSpace := asp} (n+100) (initState initMem
  [(3..6, vals_i.map encode)])). 17 hypotheses over vals1..4, n, σ, a1..a4: 4 x valid field values; Domain (hand-written: transactions
  nonempty, sorted by card, <= 50 card groups of <= 10, < 10^5 cross-references; nothing requires customers or accounts to be found); fewer
  than 2^27 records in all (Rust: 2^28); n > number of records; 4 file premises (each file a Java array of its record class, < 2^31 elements,
  objects holding the record's values); 6 class-init premises (ClinitRan Cbstm03a; initOf = done for $Result, $AccountRecord,
  $CardXrefRecord, $CustomerRecord, $TrnxRecord). Rel: normal return of a Cbstm03a$Result with displays = COBOL displays minus the first 11,
  stmtFileWrites = writes to file 1, htmlFileWrites = writes to file 2, abended = 1 exactly when the COBOL run abended.
- java_terminates: ∀ args σ, runSpec.pre args σ -> MTerm Gen.prog runRef args σ.
- java_total: ∀ args σ, runSpec.pre args σ -> (∃ o, MExec ... o) ∧ ∀ o, MExec ... o -> runSpec.post args σ o; runSpec = Spec.of pre normal
  (exceptional and wrong outcomes excluded); normal = the returned Result's three line lists and abended flag are Model.run's outputs.
- java_composite: same 27 binders as Statement; Safe c ∧ MTerm ∧ ((∃ o, MExec) ∧ ∀ o, MExec -> runSpec.post) ∧ Sim Rel (Call.mk Gen.prog
  runRef args σ) c; proof via java_composite_of from Glue.cobol_outputs, java, java_terminates, java_total.

## 4. Axioms (fresh process): PASS. java, java_terminates, java_total, java_composite, Rust.rust, Rust.rust_composite: exactly [propext,
Classical.choice, Quot.sound]; no sorryAx, no Lean.ofReduceBool (jauto's last fallback is bv_decide, so this rests on the print). All 277
in-module #print axioms lines of the compiles are within these three.

## 5. Compile and kernel replay: PASS (recipe note)
- Closure Cbstm03a.JavaRun + Composite at 8ed869e: 1,370 modules (EquivLean 1,050, Aeneas 249, Cobol 43, Jimple 28; AeneasMeta not followed,
  identical in the package check). 1,119 in the r4a pass list; 251 not (236 new, Iface3, 14 a50f10e Java-side modules outside the r4a closure).
- Compiled: those 251 + Composite = 252, in 18 levels. Source scan: no native_decide, ofReduceBool, sorry, admit, axiom, extern,
  implemented_by, unsafe or skipKernelTC; 182 hits are decide +kernel.
- Attempt 1 (bare lean, as in r4/r4a): 105 rc 0, then Java/Mem/Rd_past deterministic heartbeat timeout (maxHeartbeats 4000000 at
  Rd_past.lean:17:70). Cause: JimpleLean's lakefile sets precompileModules = true, so lake and the producer pass
  --load-dynlib=libJimpleLean_Jimple.so; without it JimpleLean runs interpreted and counts more heartbeats; jauto (Jimple/Tactic.lean:1232)
  is a `first` over maxHeartbeats-bounded attempts. With the library loaded (sha256 09e02883): Rd_past rc 0 in 186 s, olean 8c4bfc19 =
  producer's.
- Compile 2 (all 252 with the library): 252/252 rc 0, 03:23:58Z-04:26:39Z, 9,777 s; 0 errors, 0 sorry, 1,108 warnings.
- Oleans vs the producer's replay (20261028T0133Z): 175 byte-identical; 76 differ only outside the declarations (imports, constant names
  and order, kinds, level parameters, types and values equal; scripts/OleanCmp.lean with controls; the byte difference is the absolute
  source path in linter messages); Composite has no producer olean.
- delta_reuse against the r4a copy and pass list (1,119 = 45 replayed + 1,074 reused): 1,370 = 252 to replay + 1,118 reused; replay list =
  the 252 compiled modules. leanchecker 252/252 rc 0 (1,269 s). BadCtl rc 1 (kernel declaration type mismatch), GoodCtl rc 0.

## 6. java_composite exists in 8ed869e only (Composite.lean, namespace Cbstm03a.Java), not in the package or a50f10e.

## 7. Proposed text: see the fork's report (sec-migration replacing "CBSTM03A has no Java theorem yet."; intro "both to Rust and to Java";
appendix item; tab:replay2 row "CBSTM03A to Java (4 theorems) & 1,370 & 252 + 1,118 & equiv-lean 8ed869e").

## 8. Notes and compute: (i) the replay recipe needs --load-dynlib for JimpleLean (or lake); not a proof gap (leanchecker does not load the
library; replayed constants equal the producer's); (ii) regenerating the Jimple needs javac -g; (iii) Iface3 strengthens a helper
precondition only; (iv) one compile run stopped at level 2 and restarted detached. Compute 4.952 core-h guarded (attempt 1 1.815; library
compile 2.752 + Rd_past test 0.052; replay 0.326; other 0.007). Unguarded: hashing, package comparison, delta_reuse, git reads.
