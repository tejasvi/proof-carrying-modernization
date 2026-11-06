# Early freeze checks (started 2026-10-24, user via the coordinating session: check landed results now; Tue 06:00Z re-checks deltas)


## A: the five Rust translations (equiv-lean copy eq-20261024T1406Z = commit ff881ed96df5de23ca1512ac0d6ef0bd73019107)
- Copy: tracked files identical to the commit (git hash-object over git ls-tree); vendored pins JimpleLean-20261024T1029Z,
  coblean-20261024T1149Z, strictts-a15926a, cirlean-88e6008, Aeneas backends; lake build --no-build of the five RustRun
  modules: all 1891 jobs up to date.
- Axioms (fresh #print axioms in the copy, checks/eqA-20261024T1406Z/axcheck): 15/15 standard: Rust.rust and Rust.run_spec for
  Cbact02c, Cbact03c, Cbcus01c, Cbact04c, Cbtrn01c; COBOL side cbact02c_lists, cbact03c_lists, cbcus01c_lists,
  cbact04c_events, cbtrn01c_verifies_all.
- The proved crate is the LLM's final crate (veriforch runs/modernize/<P>/versions.json rust.final): byte-identical
  sources for all five; CBACT04C's Cargo.toml renames the package cbact04c -> cbact04c_t (lib.rs identical).
- Charon 0.1.293 + Aeneas nightly-2026.10.23-fdebf20 re-run in my scratch on those crates: Types.lean/Funs.lean
  byte-identical to the committed extraction for all five (CBACT04C with -max-recdepth 100000, as regen.sh documents).
- Statements regenerated with tools/modernize/genstmt.py from veriforch's mapping.json (copied), the IR, init_mem.hex
  and coblean's theorem files: byte-identical for all five. The only hand-written hypothesis is CBACT04C's Domain
  (every keyed READ succeeds; < 999999 category records; Modernize/Cbact04c/Domain.lean).
- IR: equiv-lean's examples/cobol/carddemo/<p>.ir.json = veriforch's = coblean 1149Z's examples/carddemo; equal to
  coblean's front-end output on CardDemo 59cc6c2f: CBTRN01C with the 1149Z front end; the other four with the
  20261024T0254Z front end (the 1149Z front end adds three file fields: dependsOn, maxLen, minLen).
- COBOL theorems in equiv-lean (Demo/Cobol/<P>/*.lean) = coblean 1149Z Examples files except a 3-line header and the
  IR path.
- Kernel replay of the import closure (56 EquivLean modules, 266 Aeneas library modules, 39 coblean library modules;
  50 import-only prefix roots skipped): 311/311 modules rc 0 (checks/eqA-*/replay/, one leanchecker run per module).
  Mathlib not replayed.

## B: undefined behaviour the binary does not show (re-run from my copies, checks/B-20261024T1432Z-v2)
- Sources: git archive of tiny-regex-c f2632c6 and cJSON 6d9f244 from veriforch's clones; drivers copied
  (drivers.sha256). gcc 15.2.0, -g -O0.
- tiny-regex-c test1 (tests/test1.c + re.c): default ASan+UBSan and +pointer-overflow silent; +pointer-compare,
  pointer-subtract with detect_invalid_pointer_pairs=2 or 1: invalid-pointer-pair at re.c:409 in matchstar.
  Standalone driver (re_match("a*$","Xaa")): silent in all configurations, including pointer-compare.
- cJSON misc_tests (Linux configuration of tests/CMakeLists.txt): default and +po: 30 tests, 0 failures, no report;
  pointer-compare (=2 and =1): invalid-pointer-pair at cJSON.c:457 in cJSON_SetValuestring. Driver: same.
- cJSON_SetValuestring has no call site in cJSON.c or cJSON_Utils.c; fuzzing/cjson_read_fuzzer.c calls only
  ParseWithOpts, Print, PrintBuffered, PrintUnformatted, Minify, Delete.
- Matches veriforch's REPORT.md (scratch/sanitize) in every cell.

## D: finished populations (copy replay/vo-D-20261024T1434Z: runs/prereg_d_estoolkit, runs/prereg_d_carddemo, deps strictts-ae0eee4 and coblean-20261024T0803Z, records)
- Pins in the records: StrictTS ae0eee4b03faf445fef28e8f06a21c551342a856, frozen copy D_20261024T105335Z (SHA256SUMS
  871ce181...), Lean 4.35.0; the sample file sha256 c712d4e4... = my frozen D/sample_estoolkit.tsv.
- Outcomes recomputed from results.jsonl with my own R6 mapping (tools/d_outcome_check.py): 100/100 es-toolkit and 44/44
  CardDemo agree with veriforch's outcome column; units in sample order with matching keys.
  es-toolkit: 3 proved (mechanical: dim, blueBright, strikethrough), 11 partial, 85 blocked, 1 timeout.
  CardDemo: 3 proved (model-stated: CBACT02C, CBACT03C, CBCUS01C), 2 partial (CBACT04C, CBTRN02C), 35 blocked, 4 timeout.
- Axioms of all 22 claimed theorems (17 es-toolkit incl. the callee wrapAnsi, 5 CardDemo) from my copy: standard.
- Kernel replay of their closures (18 package + 38 StrictTS + 6 package + 39 coblean modules; the import-only root
  `Cobol` skipped): 100/100 modules rc 0 (checks/voD-*/replay/; a first attempt failed on the elan proxy and is kept
  in replay_failed_noPATH/).

## C1: complete (63/63; final records copied at 17:57Z to replay/vo-C-20261024T1438Z/c1/final_20261024T1757Z with
## c1_results.jsonl, the driver log, pins.json and the crash-fix diffs; the orchestrator session reported the end at 17:54:22Z)
- Outcomes recomputed from the per-function verdicts with the PREREG rule (tools/c1_outcome_check.py; table
  checks/voC-*/c1_final_outcomes_20261024T1757Z.tsv): every one of the 63 frozen units has exactly one record with
  the frozen commit and library, and the recomputed outcome equals the record's and c1_results.jsonl's: 0 problems.
  - cJSON (58): behaviour change shown 7, unknown 44, blocked: build 7.
  - tiny-regex-c (5): behaviour change shown 2, unknown 3.
  - Total: 9 / 47 / 7. Certified equivalent, certified conservative, partly certified: 0.
- Per changed function (69 in the buildable commits): behaviour_changed 11, unknown 58; no equivalent or
  changed_only_where_old_unsafe verdict, so there is no verdict theorem to replay.
- Unknown reasons (first clause of each detail): no distinguishing input found after the proof failed 34, heartbeat
  timeout 19, rewrite failed 3, maximum recursion depth 2.
- Cost: model $2.6741 = the sum of all C1 usage logs (92 calls, including the cjson_lib/tiny_regex_c_lib prepass
  calls); 59,469 core-s = 16.52 core-h. The driver's "spent $3.33" is model + compute at its assumed
  $0.04/core-h (prereg_c.py spend_of), not model cost alone. Within the $350 cap.
- All 11 behaviour_changed witnesses re-run from my copy (cert packages + cirlean 88e6008; checks/voC-*/witness):
  every one prints "VOW DIFF". In 10 of the 11 both versions return normally with different results:
  order 1 cJSON_Utils decode_array_index_from_pointer, order 2 tiny-regex-c matchrange, order 7
  cJSON_InsertItemInArray, order 28 print_array and print_object (1 -> 0); order 6 cJSON_DetachItemViaPointer
  (pointer -> NULL); order 40 parse_array and parse_object (input "[]" / "{}" at nesting depth 100000: 1 -> 0, the
  new depth limit); order 45 tiny-regex-c re_compile (pattern -> NULL); order 50 parse_string ('"a"' with the
  buffer length set to 2, so the closing quote lies past the length: the old version reads it and returns 1, the
  new one stops at the length and returns 0; hooks malloc/free/realloc).
  Order 34 parse_number differs another way: the old version returns 1, the new one reaches undefined behaviour
  (indirect call through a non-function pointer), because the witness's parse buffer carries null allocator hooks
  and only the new version allocates. cJSON's own callers copy the global hooks into the buffer, so the paper must
  say that this witness relies on a null-hook buffer.
- The 7 blocked builds are all cJSON under -std=c89 with clang -fclangir (the feasibility pass predicted 7):
  orders 12, 14, 27, 46 (implicit int-to-pointer conversion, an error in the pinned clang) and 48, 53, 55
  (FP_ZERO undeclared, a C99 macro).

## C2: jsmn finished (copy replay/vo-C2-20261024T1716Z of ~/veriforch/runs/prereg/C/c2/jsmn_lib, the directory the
## records cite as veriforch_frozen/C_20261024T104212Z/runs/..., a symlink to ~/veriforch/runs; records, guard logs,
## c2_results at 17:16Z)
- Step table recomputed from the copied ci.json files, llm/usage.jsonl (rows inside each step's window) and the
  per-step guard logs (tools/c2_step_check.py): 30 rows (baseline + 29 steps) x 11 fields, 0 mismatches with
  c2_results.jsonl (checks/voC2-*/c2_jsmn_steps.tsv).
- Totals over the 29 steps: 11 steps blocked: build (pre-header-only layout), changed 8, cached 6, rechecked 1,
  new without the model 1 (prev), new with the model 2, failed 20 unit-steps, regressions 0; 58 model calls, $31.34,
  7,255 core-s. Final state: jsmn_init and jsmn_fill_token proved, the other 4 functions stuck.
- The two proof scripts are byte-identical at every step from 25 to 29; fn_jsmn_fill_token changes at step 27
  (re-proved there with the previous script, new:prev).
- Axioms in all five proof packages (steps 25-29): jsmn_init_spec, jsmn_fill_token_spec and the two Assembly
  theorems (VO.lib.Assembly.jsmn_*_in_module): 20/20 standard (a first run asked for the Assembly names without
  their namespace and reported them missing; kept in axcheck_*; re-run in axcheck2_*).
- Kernel replay (closure 37 cirlean 88e6008 + 8 Gen + 3 VO modules per package; the CIR root is import-only):
  36 cirlean modules once + 5 x 11 package modules = 91/91 rc 0. The cirlean 88e6008 build in the C2 frozen copy is
  identical (sources and oleans) to the one in my C1 copy, which the replay used.

## C2: tiny-regex-c steps 0-12 (in progress; latest copy replay/vo-C2-20261024T1716Z/c2_trc_20261025T0049Z)
- Step table recomputed for the 13 rows so far (baseline + steps 1-12): 0 mismatches (checks/voC2-*/c2_trc_steps_20261025T0049Z.tsv).
  Totals over steps 1-12: changed 13, cached 48, rechecked 5, new without the model 2, new with the model 9, failed 98
  unit-steps, regressions 2, blocked: build 2; 116 model calls, $43.82, 11,065 core-s.
- Regressions:
  - re_matchp partial -> stuck when it changed (step from 3cd275c9);
  - re_match partial -> gap with no change of its own (step from baf3a15d).
- How to read step 3: the previous head (step 2) did not build, so step 3 first verified its base revision
  (seconds_base 6,541; all 38 model calls), proving 5 functions and 1 partial, and the unchanged head reused them
  (seconds_head 4.8). The 10 "failed" are units stuck at the base and carried, not re-attempted. The paper's C2 text
  must define cached/failed this way and say that a step after a blocked step pays for its base.
- Proof packages (axioms, replay): when the library finishes.
## A: CBTRN01C -> Java (equiv-lean copy eq-20261024T1702Z = HEAD 2402b9da57e617a7aa750c8c06a0034838ca506c)
- The only Java theorem so far (veriforch proof_java.json; CBACT02C, CBACT03C, CBCUS01C and CBACT04C Java are open):
  EquivLean.Modernize.Cbtrn01c.Java.java : Statement, i.e. Sim Rel (Java call of Cbtrn01c.run) (COBOL run): when
  the COBOL run is safe, the Java call is safe and each Java outcome matches a COBOL outcome (displays as CP037 text,
  abended). One direction, partial correctness on the Java side (JimpleLean Sat); the Rust theorems are Equiv.
- Copy: tracked files match the commit except HANDOFF_20261023.md; lake build --no-build of JavaRun and RustRun:
  all 1959 jobs up to date. The copy now uses coblean snapshot 20261024T1455Z (source identical to
  ~/coblean_snapshots/coblean-20261024T1455Z), so the Rust theorems' COBOL side moved too.
- Provenance: Cbtrn01c.java = veriforch's final guided Java (versions.json java.final); javac 17 (--release 17) +
  Soot 4.7.1 re-run in my scratch: 8/8 Jimple files byte-identical to the committed ones; JavaStatement.lean and
  RustStatement.lean regenerated with genstmt.py (mapping.json unchanged since the Rust check): byte-identical;
  init_mem.hex = veriforch's.
- Axioms at this copy (checks/eqJ-20261024T1705Z/axcheck): 15/15 standard: Java.java, run_sat, statement_of_sat,
  formatDalytran_sat; the five Rust.rust and Rust.run_spec; cbtrn01c_verifies_all.
- Kernel replay of the Java closure (34 EquivLean + 25 Jimple + 39 coblean 1455Z modules; roots Jimple and Cobol are
  import-only): 96/96 rc 0 (checks/eqJ-20261024T1705Z/replay; slowest JavaProof 158 s). Mathlib not replayed.

## A: CBACT02C -> Java, and CBTRN01C -> Java again (equiv-lean copy eq-20261024T1830Z = HEAD
## f7c4d9088a4be403742e6e42a2a4288f5d27254f; pins JimpleLean 20261024T1546Z, coblean 20261024T1745Z)
- Copy: 636 tracked files; 630 equal the commit. The 6 that differ are uncommitted edits in ~/equivlean at copy time
  (the five RustProof.lean files and Demo/Cobol/Cbact04cRust/Sim.lean: the equiv-lean maintainer session's pending kernel speedup). None of them is
  in the closure of either Java theorem (57 EquivLean + 25 JimpleLean + 41 coblean modules). The Rust theorems are
  therefore NOT checked at this copy; they wait for the committed speedup.
- lake build --no-build of both JavaRun modules: all 176 jobs up to date. Vendored JimpleLean 1546Z and coblean 1745Z
  equal their snapshots (~/jimplelean_work/snapshots, ~/coblean_snapshots; sources, .lake excluded).
- CBACT02C provenance:
  - Cbact02c.java = veriforch's final guided Java (versions.json java.final, guided/java/v1);
  - javac 17 + Soot 4.7.1 in my scratch: 3/3 Jimple files byte-identical;
  - JavaStatement.lean regenerated with genstmt.py (mapping.json unchanged since the Rust check): byte-identical;
    init_mem.hex = veriforch's.
- The translation side (JL.run_sat) was proved by JimpleLean's session. The 12 JL/ files equal JimpleLean snapshot
  1546Z's Examples/CardDemo/Cbact02c*.lean apart from a 4-line provenance comment, the imports, the namespace,
  `CB.` -> equiv-lean's `Java.Gen.`, and Cbact02cProg dropping its own `jimple_import` in favour of equiv-lean's
  JavaGen. Checked mechanically after the renaming (Cbact02cRun also differs by one trailing blank line). JimpleLean's
  own Jimple files and Java source for CBACT02C are byte-identical to equiv-lean's and veriforch's. In any case the
  build checks the proofs against equiv-lean's Gen.prog.
- COBOL side: Demo/Cobol/<P>/Prog.lean = coblean 1745Z Examples/<P>.lean apart from the header and the IR path (both
  programs). IR: CardDemo 59cc6c2f re-run through coblean 1745Z's front end. CBACT02C, CBACT03C, CBACT04C and
  CBCUS01C are byte-identical to equiv-lean's IR (the re-pin moved them to this format: "using": [] and three null
  file fields). CBTRN01C differs only by the new top-level "using": [] field, which coblean's Lean loader never reads
  (Cobol/Frontend has no "using"; only the Python linker uses it), so the loaded program is the same.
- Axioms (checks/eqJ2-20261024T1830Z/axcheck): 9/9 standard: Cbact02c Java.java, sat_runSpec_of_J,
  statement_of_sat, JL.run_sat; Cbtrn01c Java.java, run_sat, statement_of_sat; cbact02c_lists, cbtrn01c_verifies_all.
- What the CBACT02C theorem says: Sim, the same one-directional partial-correctness form as CBTRN01C Java.
- Kernel replay of the union closure (121 modules; roots Cobol and Jimple import-only): 121/121 rc 0
  (checks/eqJ2-20261024T1830Z/replay), every closure module has a result.
- Replay times are not paper numbers yet. The same unchanged module (Cbtrn01c.JavaStatement) replayed in 98.6 s at
  17:14Z (load 300-650, cold cache) and in 9.6 s (old copy) / 6.6 s (new copy) at 18:37Z (load ~175). Loading the
  imports dominates. The earlier control (controls/lc_neg: a skipKernelTC-forged theorem is rejected, rc 1) shows
  leanchecker does check declarations. Check times for the paper must be measured at the freeze under stated
  conditions (load, warm cache, repeated runs).

## A: all 8 proved theorems at one commit (copy eq-20261024T1932Z = HEAD acde56c2540397696f9792dd29708a3fa39615ca,
## clean: 644/644 tracked files equal the commit; pins JimpleLean 1546Z, coblean 1830Z, Aeneas fdebf20)
- Theorems: Rust (Equiv) for CBACT02C, CBACT03C, CBACT04C, CBCUS01C, CBTRN01C, CBTRN02C; Java (Sim, partial correctness)
  for CBACT02C and CBTRN01C. lake build --no-build of the 8 theorem modules: all 2029 jobs up to date.
- New, CBTRN02C -> Rust:
  - the crate = veriforch's rust.final (guided/rust/v2, src and Cargo.toml identical);
  - Charon 0.1.293 + Aeneas re-run in my scratch: Types.lean and Funs.lean byte-identical (no extra flags);
  - hand-written Domain.lean: (trans.map tId).Nodup and trans.length < 10^9, i.e. distinct daily transaction ids and
    fewer than 10^9 transactions; the < 2^28 records bound is generated;
  - COBOL side cbtrn02c_posts (+ Glue.cobol_outputs).
- Statements: all 16 generated statements in genall.sh's table (8 programs x Java/Rust, proved or not) regenerated with
  genstmt.py from veriforch's current mapping.json files: 16/16 byte-identical.
- Sources of the other seven: Rust crates and Aeneas extractions unchanged since ff881ed (regenerated identical there);
  each crate = veriforch's rust.final (v1 for CBACT02C, CBCUS01C, CBTRN01C; v2 for CBACT03C; v3 for CBACT04C). Java
  sources and Jimple unchanged since copy eq-20261024T1830Z (regenerated identical there).
- COBOL side:
  - every Demo/Cobol/<P>/*.lean = coblean 1830Z's Examples file apart from the header, the IR path and import renames;
  - the vendored coblean 1830Z = its snapshot;
  - IR: coblean 1830Z's front end on CardDemo 59cc6c2f gives byte-identical IR for CBACT02C, CBACT03C, CBACT04C and
    CBCUS01C. For CBTRN01C and CBTRN02C (equiv-lean's IR = veriforch's copy) the only difference is the new top-level
    "using": [] field, which coblean's Lean loader does not read (CBACT04C's is "using": [136], also unread).
- Axioms (checks/eqA2-20261024T1932Z/axcheck): 23/23 standard. These are the 8 theorems, their run_spec / run_sat,
  and the COBOL sides cbact02c_lists, cbact03c_lists, cbcus01c_lists, cbtrn01c_verifies_all, cbact04c_events,
  cbact04c_all and cbtrn02c_posts.
- Kernel replay of the union closure (431 modules: 116 EquivLean, 41 coblean, 25 JimpleLean, 249 Aeneas):
  - 180 replayed, 180/180 rc 0;
  - 48 import-only prefix roots skipped;
  - 203 Aeneas library modules reused from the passing replay at eqA-20261024T1406Z (ff881ed): the Aeneas library's
    269 oleans are byte-identical (aggregate sha256 bc70b5f3...), and all 9,049 dependency oleans (Mathlib,
    batteries, aesop, ...) are the same inodes as in that copy.
  - Every closure module has a result or a recorded reason (checks/eqA2-*/replay_skipped.tsv).
- Freeze delta from here: re-copy at the freeze, then re-check only what changed. That means modules whose olean or
  any olean in their closure changed, plus statements, provenance and axioms for new or changed theorems.

## A: CBACT01C -> Rust added; all 9 at one commit (copy eq-20261024T2032Z = HEAD 510efd6d75194db172d03416d48130431f7ea668,
## clean: 656/656 tracked files; pins JimpleLean 1546Z, coblean 20261024T1933Z, Aeneas fdebf20)
- lake build --no-build of the 9 theorem modules: all 2042 jobs up to date.
- CBACT01C -> Rust:
  - the crate = veriforch's rust.final (guided/rust/v3, the third attempt);
  - Charon + Aeneas re-run: Types.lean and Funs.lean byte-identical;
  - no hand-written domain (generated < 2^28 bound);
  - COBOL side cbact01c_extracts;
  - CALL COBDATFT goes through coblean's hand-written model, Cobol/Ext/CardDemo.lean. The model is of an 84-line HLASM
    routine, written from its source; its error path, which copies 25 undetermined bytes, is unsupported. This is a
    trusted part of the A result.
- Statements: 16/16 regenerate byte-identical (genall.sh's table now names cbtrn03c_every / Every.lean for CBTRN03C).
- COBOL side: Demo/Cobol/Cbact01c/Prog.lean = coblean 1933Z Examples/Cbact01c.lean apart from the header and the IR
  path. Vendored coblean 1933Z = its snapshot. IR: coblean 1933Z's front end gives byte-identical IR for CBACT02C,
  CBACT03C, CBACT04C and CBCUS01C. For CBACT01C, CBTRN01C and CBTRN02C (equiv-lean's IR = veriforch's copy) the only
  difference is the unread "using": [].
- Axioms: 26/26 standard (the 23 above plus Cbact01c Rust.rust, run_spec and cbact01c_extracts).
- Kernel replay by delta (tools/delta_reuse.py, against the passing copy eq-20261024T1932Z):
  - union closure 444 modules;
  - 13 replayed, 13/13 rc 0: the 9 CBACT01C modules, its Aeneas Types/Funs, Demo.Cobol.Cbact01c.Prog and
    Cobol.Ext.CardDemo;
  - 383 reused: each passed on the older copy and has a byte-identical olean, as does every module in its import
    closure. coblean 1933Z's oleans are byte-identical to 1830Z's ("pins only").
  - 48 import-only roots skipped;
  - the 9,049 dependency oleans are the same inodes.

## A: CBTRN03C -> Rust added; all 10 at one commit (copy eq-20261024T2034Z = HEAD 5c3d3415419143c41ad6fe733dcc7bd66285e5c4,
## clean: 667/667 tracked files; same pins as above)
- Proved now: Rust (Equiv) for all 8 resolving programs (CBACT01C, CBACT02C, CBACT03C, CBACT04C, CBCUS01C, CBTRN01C,
  CBTRN02C, CBTRN03C); Java (Sim) for CBACT02C and CBTRN01C. lake build --no-build of the 10 theorem modules: all
  2067 jobs up to date.
- CBTRN03C -> Rust:
  - the crate = veriforch's rust.final (guided/rust/v1, the first attempt);
  - Charon + Aeneas re-run: Types.lean and Funs.lean byte-identical;
  - hand-written Domain: trans.length < 10^7 and parms != [] (fewer than 10^7 transactions, a date-parameter record);
  - COBOL side cbtrn03c_every. Per the equiv-lean maintainer session it covers the empty file, the early stop at the first out-of-range date, the
    lookup abends, leading blank cards and the EOF double count, a defect of the COBOL program that both
    translations reproduce.
  - Demo/Cobol/Cbtrn03c/{Prog,Every,Any,Stop}.lean = coblean 1933Z's Examples files apart from header, path and
    imports. IR = veriforch's copy; differs from the 1933Z front end only by the unread "using": [].
- Statements: 16/16 regenerate byte-identical (table unchanged since 510efd6).
- Axioms: 29/29 standard (the 26 above plus Cbtrn03c Rust.rust, run_spec and cbtrn03c_every).
- Kernel replay by delta against copy eq-20261024T2032Z:
  - union closure 469 modules;
  - 25 replayed, 25/25 rc 0: the CBTRN03C modules, its Aeneas Types/Funs, Demo.Cobol.Cbtrn03c.{Prog,Every,Any,Stop},
    EquivLean.Modernize.GlueKit and Cobol.Logic.LoopExit;
  - 396 reused (passed earlier; olean and closure identical);
  - 48 import-only roots;
  - dependency oleans the same inodes.

## D: tinyxml2 finished (copy replay/vo-Dtx-20261024T2047Z: records/tinyxml2, runs/prereg_d_tinyxml2 and _w1)
- Sample file sha256 047db6d7... = my frozen D/sample_tinyxml2.tsv. cirlean dep (~/veriforch/deps/cirlean-88e6008)
  = my copy (sources, oleans and the cirrun binary identical).
- Outcomes recomputed with tools/d_outcome_check_v2.py (R6; order-independent, rows without a status):
  - one row per sample unit, keys equal the frozen sample;
  - 100/100 agree with veriforch's outcome column;
  - counts and Wilson 95% intervals equal summary.json;
  - recorded counts: proved_model_stated 21, partial 5, refuted 2, blocked 50, timeout 20, infrastructure_error 2;
    model $48.06, 23,270 core-s.
- The 2 infrastructure errors are a driver misrecording (DEVIATIONS, same day): units 80 (StrPair::Set) and 88
  (XMLUtil::IsNameStartChar). Their verify logs say stuck (negative cache): three Lean attempts that failed inside
  units 40 and 53. Under R6 that is timeout, so tinyxml2 = timeout 22, infrastructure_error 0. The paper states both
  and the reason.
- The 21 proved functions all have closure size 1 (virtual casts and accessors such as ToElement, ToDocument, Parent,
  NextSibling, FirstChild, DynArray's constructor, XMLVisitor's destructor and Visit/VisitExit). The 5 partial
  units are proved assuming the contracts of stuck callees.
- Refuted (2), both inputs outside the calling convention (verdict missing_precondition), re-run from my copy with
  cirlean's cirrun on the run's unit.cir: every candidate's outcome equals the recorded replay (6/6 and 8/8).
  - ErrorIDToName(19 / 4294967295 / 31): out-of-bounds read of the 19-entry _errorNames (UB); in-range ids return
    normally;
  - XMLUtil::ToStr(int, buf, size) with size -1 or size 5 for a 2-char buffer: snprintf writes past the buffer (UB);
    convention-respecting inputs return normally.
- Axioms of all claimed theorems (18 modules on worker 0, 14 on worker 1; the units and their built closure callees):
  32/32 standard.
- Kernel replay with tools/leancheck1lp.sh (closure = Gen.v0_lib.Unit + the VO modules; the 36 cirlean modules are
  the oleans already replayed for C2): 34/34 rc 0. Gen.v0_lib.Unit (42 MB olean) replays in 0.9 s; a
  `leanchecker --fresh` run of it, which replays its whole import closure from scratch, also passes (rc 0, 1 m 43 s;
  checks/voD-*/tinyxml2/probe).

## A: CBCUS01C -> Java added; all 11 at one commit (copy eq-20261024T2113Z = HEAD b87bdc4656cfa20593420ef63fcd1aeb254aed21,
## clean: 679/679 tracked files; pins JimpleLean 20261024T2006Z, coblean 1933Z, Aeneas fdebf20)
- Proved now: Rust for all 8 resolving programs; Java for CBACT02C, CBCUS01C and CBTRN01C. lake build --no-build of
  the 11 theorem modules: all 2082 jobs up to date.
- CBCUS01C -> Java:
  - Cbcus01c.java = veriforch's java.final (guided/java/v1) = JimpleLean 2006Z's examples_java/cbcus01c/src;
  - javac 17 + Soot: 3/3 Jimple byte-identical; equiv-lean's Jimple = JimpleLean's copy.
  - Translation side cu_run_sat by JimpleLean's session. Modernize/JL/ (22 files: CBACT02C and CBCUS01C) is
    regenerated identically from snapshot 20261024T2006Z by tools/modernize/import_jl.py --check. The transform only
    rewrites imports, the program alias -> equiv-lean's JavaGen and the namespace, and adds a header. Vendored
    JimpleLean 2006Z = its snapshot.
  - The bridge sat_runSpec_of_J is in Modernize/Cbcus01c/JavaRun.lean. COBOL side cbcus01c_lists.
  - Statement: Sim (one direction, partial correctness), as for the other Java theorems.
- Statements: 16/16 regenerate byte-identical.
- Axioms: 32/32 standard (the 29 above, with CBACT02C's run_sat now EquivLean.Modernize.JL.run_sat, plus Cbcus01c
  Java.java, sat_runSpec_of_J and JL.cu_run_sat).
- Kernel replay by delta against copy eq-20261024T2034Z:
  - union closure 484 modules;
  - 66 replayed, 66/66 rc 0: 59 EquivLean, the Java-side modules and the moved JL files; 7 JimpleLean modules
    changed by the re-pin;
  - 370 reused (passed earlier; olean and closure identical);
  - 48 import-only roots;
  - dependency oleans the same inodes.

## coblean CardDemo evidence package (snapshot coblean-20261024T2117Z; full copy replay/cobE-20261024T2147Z)
- docs/EVIDENCE_carddemo.tsv sha256 593875866e2a9eedc0d8ec6e006de360b83d8e04b23455ea265e807983df02db and the .md
  5b8c26a7... match the values the COBOL maintainer session sent. 167 claims: artifact 5, trust 9, semantics 4, theorems 69, coverage 48,
  validation 27, effort 5.
- Commands and helper scripts reviewed before running: writes only under $OUT; recheck_lean.sh runs lean without -o;
  A4 is a read-only git status of the CardDemo checkout.
- Every row re-run from my copy (tools/cob_evidence_run.py: fresh OUT per row, one CPU via taskset, guarded;
  checks/cobE-20261024T2147Z/results/): 167/167 outputs equal the expected values, all rc 0.
  - TH0, the full rebuild from source in a copy under OUT: "Build completed successfully (114 jobs) | standard: 23 |
    bv_decide: 1", 19.3 min, 0.32 core-h.
  - Sum of row wall times 37.6 min. After the run my copy still equals the snapshot (diff -rq) and the CardDemo
    checkout is unmodified.
- Axioms: 23 of the 24 theorem-axiom rows are standard. TH4 (bincnt_equiv, the BINCNT example, not CardDemo) depends
  on bincnt_equiv._native.bv_decide.ax_7, the native-evaluation axiom bv_decide adds. It trusts Lean's compiler, so
  the paper must say so. T2's "0 files use native_decide or Lean.ofReduceBool" is literally true but must not be read
  as "no compiler trust".
- Numbers now re-checked (for the paper, with the package's definitions):
  - coverage: 44 programs = batch 14, cics 17, cics+db2 3, cics+ims 2, cics+ims+mq 1, cics+mq 2, db2 1, ims 4. Of the
    14 batch: front end ok 13, 0 unsupported 12, resolve 11, covered 10 (3,824 non-comment lines). CSUTLDTC counts as
    batch by the source-text rule but is a CICS-called subroutine.
  - validation (GnuCOBOL 3.2.0):
    - TRUNC(STD) 200 programs: 195 ok + 5 ok-negzero;
    - TRUNC(BIN) 200: 198 ok, 2 mismatch, traced to COMP-5 overflow past the PICTURE (an area the README lists as
      not validated);
    - control flow 100: 88 ok, 12 declined;
    - front end 100 and 60;
    - files 100: 99 ok + 1 ok-abend;
    - UNSTRING, INSPECT and STRING 60 each, all ok;
    - ACCTINT, BINCNT and RECSUM 100 each;
    - Java/Rust transcriptions 500.
  - effort: 2,878 COBOL lines without copybooks (3,229 with), 4,975 program-specific Lean lines, 6,610 library
    lines; 1,728 and 1,540 Lean lines per 1,000 COBOL lines.
- Superseded by snapshot coblean-20261024T2211Z (169 claims; TSV sha256 b8b8309e..., md ef37899b..., both verified):
  - the id-by-id diff against 2117Z gives exactly the COBOL maintainer session's list: new TH25.ax and TH25.st (CardDemo.Cbact04c.cbact04c_every);
    changed TH0, E3 and E5; claim text only for CV.CBACT04C and T2 (T2 now names bv_decide's native axiom);
  - the source diff is limited to Examples/Cbact04cEvery.lean, Examples.lean, docs and make_evidence.py;
  - full re-run of all 169 rows from my copy (replay/cobE2-20261024T2237Z; checks/cobE2-20261024T2237Z/results/): 169/169 match,
    all rc 0;
  - TH0 = "Build completed successfully (115 jobs) | standard: 24 | bv_decide: 1", 25.1 min;
  - TH25.ax standard; TH25.st sha256 2a3859a3...;
  - E3 = 5,758 program-specific Lean lines; E5 = 2,000 and 1,783 Lean lines per 1,000 COBOL lines (without and with
    copybooks);
  - only TH4 (bincnt_equiv, BINCNT) carries bv_decide's native axiom;
  - my copy equals the snapshot after the run and the CardDemo checkout is clean.
- Superseded by snapshot coblean-20261024T2306Z (170 claims; TSV sha256 d8559d86..., md 4951b321..., both verified):
  - the id diff against 2211Z gives exactly the COBOL maintainer session's list: new V.run.cbact04c; changed TH20.st (cbtrn02c_any's abend case
    now also states RETURN-CODE = 0 in storage), the TH20.ax source line, E3 and E5;
  - the source diff is limited to Examples/Cbtrn02cDup.lean, tools/evidence/sample_runs.sh (new cbact04c case,
    reviewed: writes in OUT), docs and make_evidence.py;
  - full re-run of all 170 rows from my copy (replay/cobE3-20261024T2338Z; checks/cobE3-20261024T2338Z/results/): 170/170 match,
    all rc 0;
  - TH0: 115 jobs, standard 24, bv_decide 1, 28.0 min; TH20.ax standard;
  - V.run.cbact04c = "signal=stop:Cobol.StopKind.goback events=251 displays=152 writes=5:50 rewrites=49
    default-group-retries=50": CBACT04C run by the semantics on CardDemo's own TCATBALF/CARDXREF/ACCTDATA/DISCGRP
    takes the DEFAULT-group retry for all 50 category records (a run-based confirmation of the data check);
  - E3 = 5,760; E5 = 2,001 and 1,783 per 1,000 COBOL lines;
  - my copy equals the snapshot after the run, and the CardDemo checkout is clean.

## A: CBACT03C -> Java added (in equiv-lean, not yet announced by the equiv-lean maintainer session); all 12 at one commit (copy eq-20261024T2248Z = HEAD
## fb1c6eb6ad146abfbd33fa0afed0882fff475d39, clean: 694/694 tracked files; pins JimpleLean 20261024T2110Z, coblean
## 20261024T2209Z, Aeneas fdebf20)
- Proved: Rust for all 8; Java for CBACT02C, CBACT03C, CBCUS01C and CBTRN01C. lake build --no-build of the 12 theorem
  modules: all 2094 jobs up to date. Vendored JimpleLean 2110Z and coblean 2209Z = their snapshots.
- CBACT03C -> Java:
  - Cbact03c.java = veriforch's java.final (guided/java/v1) = JimpleLean's examples_java/cbact03c/src;
  - javac 17 + Soot: 4/4 Jimple byte-identical (= JimpleLean's copy);
  - translation side JL.c3_run_sat by JimpleLean's session; Modernize/JL/ (30 files: CBACT02C, CBACT03C, CBCUS01C)
    regenerated identically by import_jl.py --check (aliases CB, C3, CU);
  - bridge sat_runSpec_of_J in Modernize/Cbact03c/JavaRun.lean; COBOL side cbact03c_lists.
- Statements: all 18 generated statements (genall.sh's table incl. the new variant column: CBACT04C/Every Java and
  Rust) regenerate byte-identical (new tools/genstmt_all_check.py; control: 16/16 at the previous copy).
- COBOL side:
  - all Demo/Cobol/<P>/*.lean copies with a provenance header = coblean 2209Z's Examples apart from the header, the
    IR path and imports. The files without a header are equiv-lean's own older CBACT04C demo
    (Demo/Cobol/Cbact04cRust/), not copies.
  - IR = coblean 2209Z's front end for CBACT02C, CBACT03C, CBACT04C and CBCUS01C. CBACT01C, CBTRN01C, CBTRN02C and
    CBTRN03C differ only by the unread "using": [].
- Axioms: 35/35 standard (the 32 above plus Cbact03c Java.java, sat_runSpec_of_J and JL.c3_run_sat).
- Kernel replay by delta against copy eq-20261024T2113Z:
  - union closure 496 modules;
  - 75 replayed, 75/75 rc 0: 71 EquivLean modules after the JimpleLean / coblean re-pins, 4 JimpleLean modules;
  - 373 reused;
  - 48 import-only roots;
  - dependency oleans the same inodes.
- CBACT04C: the re-based "every input" statements (variant Every, on cbact04c_every) are generated and identical; no
  proof of them yet. The direct-group restriction still applies to the CBACT04C Rust theorem (PAPER_PLAN_v2).

## A: CBACT04C -> Rust on every input added; all 13 at one commit (copy eq-20261024T2259Z = HEAD
## 584c1ba3a5091cff47089353a40ba58b6526dba4 = 03e908a + handoff, clean: 704/704 tracked files)
- The equiv-lean maintainer session announced 03e908a: CBACT03C -> Java (checked above at fb1c6eb; its modules' oleans are unchanged at this copy) and
  CBACT04C -> Rust on EVERY input, EquivLean.Modernize.Cbact04c.Every.Rust.rust.
- lake build --no-build of the 13 theorem modules: all 2107 jobs up to date.
- CBACT04C Every:
  - statement generated from cbact04c_every (genall.sh variant Every; all 18 statements regenerate byte-identical);
  - hand-written Domain (Modernize/Cbact04c/Every/Domain.lean): fewer than 999999 category records, and each
    account's records contiguous (for i < j < k, records i and k of the same account imply record j too);
  - no lookup is assumed to succeed. It covers CardDemo's sample-data path (blank ACCT-GROUP-ID -> DEFAULT retry).
    The crate and extraction are the same as for the restricted CBACT04C theorem: rust.final v3, Aeneas regenerated
    identical earlier.
- Axioms: 38/38 standard (the 35 above plus Every.Rust.rust, Every.Rust.run_spec and cbact04c_every).
- Kernel replay by delta against copy eq-20261024T2248Z:
  - union closure 509 modules;
  - 13 replayed, 13/13 rc 0: the Every modules, Cbact04c.ModelEvery and Demo.Cobol.Cbact04c.Every;
  - 448 reused;
  - 48 import-only roots.
- Paper: cite Every.Rust.rust for CBACT04C -> Rust. The restricted theorem remains in the repository. The
  direct-group sentence now applies only to Java, until a Java theorem on every input lands (PAPER_PLAN_v2).

## A: Java statements gain a generated bound (copy eq-20261024T2323Z = HEAD fdac1b41e5fe004c8912f01bbef5cfe1e2b85dea =
## 69126a5 + handoff, clean: 707/707 tracked files; coblean 20261024T2306Z = its snapshot, "pins only")
- Every Java statement now has the hypothesis "total input records < 2^27", generated (the Rust statements have
  < 2^28). Reason (the equiv-lean maintainer session): JVM collections are int-indexed, and JimpleLean's List.size would wrap at 2^31 elements where
  a real JVM throws OutOfMemoryError. In CBTRN01C's JavaStatement.lean the diff to the previous copy is exactly that
  one line.
- Statements: all 20 generated statements (the genall.sh table now has 20 rows) regenerate byte-identical.
- The 4 proved Java theorems keep their names. lake build --no-build of the 13 theorem modules: all 2107 jobs up to
  date. Axioms 38/38 standard.
- Kernel replay by delta against copy eq-20261024T2259Z:
  - union closure 509;
  - 34 replayed, 34/34 rc 0: the Java-side modules on the new statements;
  - 427 reused;
  - 48 import-only roots.
- Paper: state the Java bound (< 2^27 input records in all) and the Rust bound (< 2^28) with each theorem, and why the
  Java one exists.

## A: CBACT04C -> Java on the restricted domain added; all 14 at one commit (copy eq-20261024T2359Z = HEAD
## 2b5f6a97e21977544fdac20cf8990abc728e6e6d = 2579a43 + handoff, clean: 782/782 tracked files)
- New: EquivLean.Modernize.Cbact04c.Java.java on cbact04c_all's domain (every lookup found, KSDS order). Like the
  restricted Rust theorem, it does not cover the sample-data DEFAULT path. The equiv-lean maintainer session counts CBACT04C as Rust on every input
  plus Java restricted (12 of 16 fully proved).
- Cbact04c.java = veriforch's java.final (guided/java/v1); javac 17 + Soot: 8/8 Jimple byte-identical. All 20
  generated statements regenerate byte-identical.
- lake build --no-build of the 14 theorem modules: all 2184 jobs up to date. Axioms: 41/41 standard (the 38 above
  plus Cbact04c Java.java, run_sat and statement_of_sat).
- Kernel replay by delta against copy eq-20261024T2323Z:
  - union closure 586;
  - 77 replayed, 77/77 rc 0: the CBACT04C Java modules;
  - 461 reused;
  - 48 import-only roots.
- Paper: cite the Every versions for CBACT04C once both languages have one. Until then, the CBACT04C Java claim
  carries the direct-group sentence (PAPER_PLAN_v2).

## A: CBTRN02C -> Rust on any input added; all 15 at one commit (copy eq-20261025T0033Z = HEAD
## 2a71ed70d943f7845f1eabb939fa96602cd77c55 = 40c64d0 + handoff, clean: 789/789 tracked files)
- New: EquivLean.Modernize.Cbtrn02c.Any.Rust.rust (genall variant Any, from cbtrn02c_any in Demo/Cobol/Cbtrn02c/Dup.lean).
  Repeated transaction ids are covered: the second WRITE fails with status 22 and the run abends 999, keeping the
  earlier updates. Hand-written Domain (Modernize/Cbtrn02c/Any/Domain.lean): trans.length < 10^9 only, plus the
  generated < 2^28 bound.
- Rust now holds on each program's widest domain: CBACT04C Every, CBTRN02C Any, CBTRN03C every input, and the five
  original programs. Java: CBTRN01C, CBACT02C, CBCUS01C and CBACT03C on their statements; CBACT04C restricted only.
- All 20 generated statements regenerate byte-identical. lake build --no-build of the 15 theorem modules: all 2194
  jobs up to date. Axioms: 44/44 standard (the 41 above plus Any.Rust.rust, Any.Rust.run_spec and cbtrn02c_any).
- Kernel replay by delta against copy eq-20261024T2359Z:
  - union closure 596;
  - 10 replayed, 10/10 rc 0: the Any modules, Cbtrn02c.ModelAny and Demo.Cobol.Cbtrn02c.Dup;
  - 538 reused;
  - 48 import-only roots.
- Paper: cite Any.Rust.rust for CBTRN02C -> Rust. The distinct-ids theorem stays in the repository.

## D: commons-lang3 finished, NOT final (copy replay/vo-Dl3-20261025T0047Z: records/lang3 and the units of the 3 worker dirs)
- Sample sha256 2489eb8b... = my frozen D/sample_lang3.tsv; one row per sample unit, keys equal.
- Recorded: proved 0, blocked 29, timeout 29, infrastructure_error 42; model $25.62, 32,580 core-s (front end 5,962 core-s).
- The 42 infrastructure errors are tool crashes (DEVIATIONS, 2026-10-25):
  - 34: TypeError, JimpleAdapter.assemble() has no n_lookups parameter, after the units had statuses (18 proved with
    replay PASS, 6 conditional, 4 stuck, 4 blocked, 1 partial, 1 budget);
  - 8: a generated module (EventCountCircuitBreaker StateStrategyClosed.isStateTransition) does not check.
- PREREG allows a recorded crash fix and a re-run of the affected units; the orchestrator session informed. Recomputation agrees on the
  66 non-crash rows. The 34 crash rows differ only because my mapping does not apply the crash override.
- No claimed theorem as recorded, so nothing to replay yet.

## A: CBACT04C -> Java on every input added; all 16 theorems at one commit (copy eq-20261025T0114Z = HEAD
## a7da222af6e6ea2e5b7491b1db6762e13bf88886 = 3fd8581 + handoff, clean: 868/868 tracked files)
- New: EquivLean.Modernize.Cbact04c.Every.Java.java (variant Every, from cbact04c_every; no lookup assumed, no KSDS
  order). CBACT04C is now proved on every input in Rust and Java (domain: fewer than 999999 category records, each
  account's records contiguous).
- On their widest domains: Rust 8/8; Java CBTRN01C, CBACT02C, CBCUS01C, CBACT03C and CBACT04C (13 of 16 targets).
  Also present: restricted CBACT04C Rust/Java, and distinct-ids CBTRN02C Rust.
- All 20 generated statements regenerate byte-identical. lake build --no-build of the 16 theorem modules: all 2276
  jobs up to date. Axioms: 47/47 standard (the 44 above plus Every.Java.java, run_sat and statement_of_sat).
- Kernel replay by delta against copy eq-20261025T0033Z:
  - union closure 678;
  - 82 replayed, 82/82 rc 0: the CBACT04C Every Java modules;
  - 548 reused;
  - 48 import-only roots.

## A: CBACT01C -> Java added; all 17 theorems at one commit (copy eq-20261025T0127Z = HEAD
## 56c64b8dde939ced5bd331723e9748c317a989f5 = 3d0b3bc + handoff, clean: 894/894 tracked files)
- New: EquivLean.Modernize.Cbact01c.Java.java.
  - Translation: Cbact01c.java = veriforch's java_v2.final (guided_v2/java/v1, made with styleguide_java_v2.md). It
    is NOT the first guided Java (guided/java/v1), so the paper must name the translation per program.
  - javac 17 + Soot: 5/5 Jimple byte-identical.
  - Domain: valid account records plus the generated < 2^27 bound. COBOL side cbact01c_extracts with the COBDATFT
    model.
- 14 of 16 targets on their widest domains: Rust 8/8; Java CBTRN01C, CBACT02C, CBCUS01C, CBACT03C, CBACT04C (every
  input) and CBACT01C. Open: CBTRN02C Java (any input), CBTRN03C Java.
- All 20 generated statements regenerate byte-identical. lake build --no-build of the 17 theorem modules: all 2313
  jobs up to date. Axioms: 50/50 standard (the 47 above plus Cbact01c Java.java, run_sat and statement_of_sat).
- Kernel replay by delta against copy eq-20261025T0114Z:
  - union closure 715;
  - 37 replayed, 37/37 rc 0 (slowest JavaRunRead 20 s);
  - 630 reused;
  - 48 import-only roots.

## A2: the AI-error numbers, reproduced (copy replay/a2-20261025T1200Z)
- Copied runs/modernize (records only; no .lake/target) and veriforch's orch/veriforch/modernize/a2.py into a mirror;
  ran `python3 -m veriforch.modernize.a2` there.
- Output A2.json equals veriforch's A2.json in all 2,712 leaf values except the 99 `dir` paths (my copy's paths).
- So the A2 numbers follow from the run records with veriforch's definitions:
  - 92 runs (3 excluded: two not applicable, one harness artifact);
  - first version that ran differed from cobolrun: 32/92 = 34.8% [25.8, 45.0];
    - plain prompt 20/42 = 47.6% [33.4, 62.3];
    - style guide v1 10/47 = 21.3% [12.0, 34.9];
    - style guide v2 2/3;
    - Java 15/48, Rust 17/44;
  - v1 did not build 12/92, all guided Rust (Aeneas/Charon rejections, 12/23);
  - v1 not a passing translation 43/92 = 46.7%;
  - root causes by arm and language: collating sequence 31, verifier language 12, uninitialized storage 6, other 1.
- Still to do at the freeze: an independent recomputation of the headline rates from the per-run summaries with my
  own code, not veriforch's (a2.py's reading of "first version that ran" and "differed").
- "Testing passed, proof failed": 0 of 16, per equiv-lean and veriforch. Proof-side findings: the platform bounds
  (Rust < 2^28, Java < 2^27), the ClinitRan class-initialization statement, and the INTO padding of the DATE-PARMS
  record.


## D1: zlib finished (copy replay/vo-Dz-20261025T1140Z: records/zlib and the 3 worker run dirs with oleans)
- Outcomes: `python3 -I tools/d_outcome_check_v3.py <copy>/records/zlib/results.jsonl prereg/D/sample_zlib.tsv
  <copy>/records/zlib/summary.json` -> checks/voDz-20261025T1140Z/zlib_outcomes_check.txt: 100 rows = the frozen
  sample, 100/100 agree, counts and Wilson intervals = summary.json. Recorded: proved_model_stated 10, conditional 4,
  blocked 23, timeout 57, infrastructure_error 6.
- R6 reading (DEVIATIONS 2026-10-25T11:51Z): 5 of the 6 infrastructure errors (orders 55, 71, 81, 87, 95) are the
  negative-cache misrecording -> timeout; order 99 is a genuine tool crash, not re-run -> stays infrastructure_error.
  zlib under R6: proved_model_stated 10, conditional 4, blocked 23, timeout 62, infrastructure_error 1.
- Claimed theorems (vo2 batch, checks/vo2-20261025T1141Z): the 14 claimed units (10 proved, 4 conditional) all have
  their `<unit>_spec` theorem in a checked module (tools/d_claimed_coverage.py -> coverage_zlib_d1.txt: 14/14).
  Axioms: 16 + 15 + 15 theorems over the 3 workers, all standard (zl_zlib*_axcheck.log). Kernel replay
  (tools/pkg_replay_jobs.py + leancheck1lp.sh): worker 0 185/185 modules rc 0, workers 1 and 2 17/17 each (their 167
  Gen oleans are byte-identical to worker 0's: cmp 167/167, replayed there). Closure check
  (tools/closure_verdicts.py: every module in the import closure of the theorem modules has an rc 0 verdict): 220,
  219, 219 modules, all rc 0 or import-only (the 36 cirlean 88e6008 modules from voC2's replay_cir).

## D1: commons-lang3 after crash fix 2 (copy replay/vo-Dl3b-20261025T1149Z)
- `d_outcome_check_v3.py` -> checks/voDl3b-20261025T1149Z/lang3_outcomes_check.txt: 100 rows = the frozen sample,
  100/100 agree (v3: a wall kill is a timeout whatever status was recorded, as veriforch maps it), counts and Wilson
  = summary.json. Recorded: proved_model_stated 19, partial 4, conditional 4, blocked 29, timeout 42,
  infrastructure_error 2; the 2 (orders 59, 64) are the negative-cache misrecording -> under R6 timeout 44, infra 0.
- Claimed theorems: oleans pruned by veriforch before my copy; axioms + replay need a rebuild from the kept sources
  and pins (at the freeze). Not yet checked.

## C1b: pass 2 finished (copy replay/vo-2-20261025T1141Z/prereg C1b records; checks/voC1b-20261025T1141Z)
- `tools/c1_outcome_check.py` on the copied order list and records -> c1b_outcomes.tsv: 54/54 recomputed = record:
  behaviour change shown 1 (order 14), unknown 53; 76 functions (4 behaviour_changed, 72 unknown); reasons 46
  heartbeat, 17 no distinguishing input, 6 rewrite failed, 3 recursion depth; $2.4043, 13.02 core-h.
- Order 14's 4 witnesses re-run (cert Gen modules rebuilt on cirlean ec40522: o14_gen_build.log, 133/133): each
  prints VOW DIFF, but the commit adds 3 hook globals that the old module's initial memory lacks, so the witnesses
  are harness artifacts -> reported as unknown (DEVIATIONS 11:49Z). C1b: 0 new behaviour changes, 7 of 7 formerly
  blocked builds now build (1 of them recorded as behaviour change -> unknown, 6 unknown).

## D2: es-toolkit re-run and held-out, tinyxml2 re-run (copy replay/vo-2-20261025T1141Z/prereg/D2)
- `d_outcome_check_v3.py` per file (held-out against prereg/D2/heldout_<pop>.tsv) ->
  checks/vo2-20261025T1141Z/d2_outcomes/*_check.txt: 3 x 100 rows, all agree, counts and Wilson = summary.json.
  - es-toolkit re-run: proved_mechanical 8, proved_model_stated 1, partial 11, blocked 78, timeout 2.
  - es-toolkit held-out: proved_mechanical 6, proved_model_stated 3, partial 5, blocked 85, timeout 1.
  - tinyxml2 re-run: proved_model_stated 29, conditional 1, partial 8, refuted 2, blocked 17, timeout 43.
- Claimed theorems: every claimed unit has a checked `<unit>_spec` (coverage_es_d2.txt 34/34, coverage_tx_d2.txt
  38/38). Axioms all standard (es 19 + 28, tinyxml2 47 + 49). Kernel replay: es 20 + 29, tinyxml2 50 + 52 modules,
  all rc 0. Closure check: es 64 and 73 modules (44 StrictTS 44d6b9b each), tinyxml2 87 and 89 (38 cirlean d9ae8e5
  each), all rc 0 or import-only.
- Dependency replays (every built module of the dep copies): StrictTS 44d6b9b 50/61 rc 0, cirlean d9ae8e5 41/58 rc 0.
  The 11 + 17 failures are stale example oleans (StrictTS Async/Hash/Invariant/Maps/Refactor/Summarize/Testing,
  cirlean Examples.*: type mismatches against the rebuilt library); none is in any claimed closure (closure check).
- Transitions vs D1, order 91 real_bug and the refuted -> proved unit: DEVIATIONS 2026-10-25T12:00Z.
- Still running (live tree, 12:10Z): tinyxml2 held-out 32/100, lang3 re-run 56/100, zlib re-run 30/100; lang3 and
  zlib held-out not started.

## C2: final (budget stop; copy replay/vo-2-20261025T1141Z/c2)
- `tools/c2_step_check.py` on tiny-regex-c steps 0-20: 0 mismatches (c2_trc_final_steps.tsv); steps 21-32 have no
  ci.json (unattempted, as recorded). Steps 1-20: changed 25, cached 89, rechecked 5, new without the model 3, new
  with the model 17, failed 187, regressions 5, blocked 2; 239 calls, $119.21, 16,657 core-s. C2 total $150.55 (cap
  $150; the step in flight finished). jsmn 30/30 steps; cJSON 0 of 50 attempted.

## B: the two defects on the C semantics (checks/Bsem-20261025T1222Z; unit files copied from veriforch's runs, SHA256SUMS)
- tiny-regex-c tests/test1.c (unit.cir of runs/tiny_regex_c/v0/tests_test1), `cirrun <unit> main`, cirlean 88e6008 and
  d9ae8e5 from my copies, 1 CPU, guarded: "UB: pointer arithmetic out of bounds" with both (= matchstar.json: the
  `text--` past the start of "Xaa" on vector 32; the 32 earlier vectors run without UB).
- cJSON tests/misc_tests.c (unit.cir of runs/cjson/v0/tests_misc_tests): `main` stops at Unity's setUp (no model), so
  the test functions are run directly. cjson_set_valuestring_should_return_null_if_strings_overlap: "UB: relational
  comparison of unrelated pointers" with both versions (= cJSON_SetValuestring.json); likewise
  cjson_set_valuestring_to_object_should_not_leak_memory, which also calls cJSON_SetValuestring. Controls in the same
  unit that do not call it (cjson_get_string_value_should_get_a_string, cjson_set_number_value_should_set_numbers)
  return normally.

## A: 16 of 16 (copy eq-20261025T1158Z = HEAD a572cf661bf907e690aada32ddcb727466e93d56, clean: 1093/1093 tracked files
## equal their blobs, re-verified 12:30Z; JimpleLean 20261025T0149Z; checks/eqA8-20261025T1158Z)
- New since eq-20261025T0127Z: CBTRN02C -> Java on any input (EquivLean.Modernize.Cbtrn02c.Any.Java.java, domain
  < 10^9 transactions, COBOL side cbtrn02c_any) and CBTRN03C -> Java (EquivLean.Modernize.Cbtrn03c.Java.java, domain
  < 10^7 transactions and a date-parameter record, COBOL side cbtrn03c_every). Both translations are veriforch's
  java_v2 finals (guided_v2/java/v2, styleguide_java_v2.md).
- The 16 headline theorems: Rust Cbact01c/02c/03c/Cbcus01c/Cbtrn01c/Cbtrn03c .Rust.rust, Cbact04c.Every.Rust.rust,
  Cbtrn02c.Any.Rust.rust; Java Cbact01c/02c/03c/Cbcus01c/Cbtrn01c/Cbtrn03c .Java.java, Cbact04c.Every.Java.java,
  Cbtrn02c.Any.Java.java. Also checked: the restricted Cbact04c.Rust.rust, Cbact04c.Java.java, Cbtrn02c.Rust.rust.
- Provenance:
  - every proved source equals veriforch's final of its run byte for byte (16/16; cmp against
    runs/modernize/<PROG>/<final>; Rust finals guided v1/v2/v3, Java finals guided v1 or guided_v2 v1/v2 per
    versions.json; read from the live tree at 12:1xZ, again from a copy at the freeze);
  - javac 17 + Soot 4.7.1 regeneration of CBTRN02C (8/8 .jimple) and CBTRN03C (9/9) byte-identical (the other six
    as at earlier copies);
  - all 20 generated statements regenerate byte-identical (genstmt/result.tsv);
  - JimpleLean copies: import_jl.py --check against snapshot 0149Z, all same.
- lake build --no-build of the theorem modules: all 2522 jobs up to date.
- Axioms (axcheck/axcheck.tsv): 54/54 standard, among them the 16 headline theorems and the 3 restricted ones.
- Kernel replay by delta against copy eq-20261025T0127Z (tools/delta_reuse.py): union closure 924 modules; 481
  replayed, 481/481 rc 0 (slowest Cbtrn03c.JavaTop.CalEbc 54.5 s); 395 reused (olean and closure byte-identical to a
  passed module of the earlier copy); 48 import-only roots.

## A2: independent recomputation (my code, not a2.py; checks/A2ind-20261025)
- `python3 -I tools/a2_recompute.py replay/a2-20261025T1200Z/runs/modernize checks/A2ind-20261025/a2_runs.tsv`
  (definitions in the tool's docstring: first version that built; differed = a failing case in its round or its
  300-case final check; exclusions = "not applicable" status or an annotations.json harness artifact).
- Result equals A2.json in every cell: 92 runs of record (excluded: CBACT01C plain java/rust s1, not applicable, packed
  output field; CBACT04C guided rust s1, harness artifact per annotations.json: Aeneas killed by the runner's core-hour
  cap, empty error sent to the model). First version that ran differed 32/92 = 34.8% [25.8, 44.9]; plain 20/42, guide
  1 10/47, guide 2 2/3; Java 15/48, Rust 17/44; v1 build failure 12/92 (all guided Rust, 12/23); v1 not correct
  43/92. All arm x language cells equal.
- Root causes, counting causes marked fixed (excluding harness artifacts), over the 52 repair steps of the 92 runs:
  collating sequence 31, verifier language 12, uninitialized storage 6, other 1 (all labels incl. unfixed: 32/17/6/1);
  per arm x language as in A2.md.
- Executions: executions_disagree = 0 over 39,212 case executions (rounds + final checks) of all attempts.
- SAMPLECHECK.json (copy): 10 entries = the seed-1 v1 versions of the plain arm and guide 1 that failed on generated
  cases; sample_catches false for all 10 (one "crash" re-checked by veriforch as a jimple-run time limit). Not re-run
  by me (freeze item if time allows).
- All 95 run summaries record human_lines 0; translation wall time over the 95 runs 9.3 h.

## C2: tiny-regex-c proof packages (copy replay/vo-2-20261025T1141Z/c2/tiny_regex_c_lib/lean_v88e6008_rev, 20 packages;
## checks/voC2trc-20261025T1225Z)
- Jobs from tools/pkg_replay_jobs.py per package (LEAN_PATH = package + my cirlean 88e6008 copy + toolchain), run with
  pjobs_v3 (8, 450, 150, 2): 580 jobs rc 0.
- Kernel replay: 560/560 package modules rc 0 (Gen and VO of every package).
- Axioms: 219 theorems over the 19 packages that have VO theorems, all standard (11 packages x 11, 6 x 12, 2 x 13); the
  20th package (v52b0aeb4, 4 oleans) has no VO theorem.
- Closure check (tools/closure_verdicts.py; cirlean verdicts from voC2's replay_cir): every module in the import closure
  of every package's theorem modules has an rc 0 verdict or is import-only.

## Validation re-runs at the paper pins (C++ semantics)
- cirlean's tests/difftest/run.sh, copied with D/ROOT/W repointed to my copies (scratch under the check dir), g++ -O0
  native vs cirrun on clang -fclangir output with the cir2c libc++ headers, 1 CPU, guarded:
  - d9ae8e5 (copy vo-2/deps): 175 cases, MATCH 174, MISMATCH 0, UB 1 (t_gap_emplace: a reference returned by
    emplace_back, not modelled) — checks/val-cir-d9ae8e5-20261025T1243Z/difftest.log;
  - 88e6008 (copy vo-C/deps): 167 cases, MATCH 166, MISMATCH 0, UB 1 (same case) — checks/val-cir-88e6008-20261025T1244Z.
  (v1 at 89dddc6: 156 cases, 155/0/1.)
- TypeScript (StrictTS 44d6b9b, separate copy replay/ts-44d6b9b-val): `tools/run.sh 0.5 1800 node tests/difftest/run.js`
  -> checks/val-ts-44d6b9b-20261025T1246Z/difftest_corpus.log: PASS 180 / FAIL 0 / SKIP 0 = 138 programs agree with
  Node v22.22.1 line by line, 40 programs outside the subset rejected with their rule, 2 coverage tests. (v1 at
  a15926a: 140 = 111 + 28 + 1.) strdiff/f64diff re-run in progress.

## D1: commons-lang3 claimed theorems, rebuilt from the kept sources (replay/l3rb-20261025T1247Z; checks/l3rb-20261025T1247Z)
- veriforch pruned the oleans of the crash-fix-2 re-run, so I rebuilt in my copy: JimpleLean snapshot 20261024T1029Z
  (SHA256SUMS verified; its sha256 37607869... = pins.json bridge_snapshot_sha256sums; 49 sources identical to
  veriforch's deps copy) and the three worker packages' Gen/VO sources copied from runs/prereg_d_lang3{,_w1,_w2}, with
  only the lakefile's require path changed to my JimpleLean copy.
- Built exactly the 27 claimed units' VO modules (claimed_modules.tsv: 19 proved, 4 conditional, 4 partial; w0 12, w1
  6, w2 9): lake rc 0 for all (JimpleLean 75 jobs, workers 111/95/103), 0.08 core-h.
- Axioms: 27/27 standard (the `<module>_vc` theorem of each claimed unit; coverage_lang3_d1.txt 27/27).
- Kernel replay: 102/102 modules rc 0 (78 package modules + 24 JimpleLean modules); closure check: every module in the
  closure of the 27 theorem modules has an rc 0 verdict or is import-only (59/43/51 modules per worker).
- The 8 conditional and partial units carry no in-run replay in veriforch's records; this replay covers them.
- TypeScript numbers and strings (StrictTS 44d6b9b copy, guarded): strdiff with Node v22.22.1 references (seeds 20261023
  and 987654321): TOTAL 1,854,483 cases, 0 mismatches; f64diff float: 18 operations x 500,339-614,921 cases, 0
  mismatches; f64diff js 1 250000: 45 operations x 25,000-26,017 cases, 0 mismatches (scratch/f64 had to be created
  first; the first attempt with 25000 gave 1/10 of the cases, also 0 mismatches) — checks/val-ts-44d6b9b-20261025T1246Z.
- Java (JimpleLean 0300Z, copy replay/jim-0300Z, jimple-run built in the copy, 79 jobs): JVM difftest corpus 41/41 MATCH
  (stdout and exit status; inputs copied from ~/jimplelean_work/difftest/src) — checks/val-jim-0300Z-20261025T1244Z.
  (v1 at 0159Z: 37/37.)
- Post-hoc labelled count for the lang3 reader artifact (tools/lang3_reader_artifact.py; 1029Z LIBRARY_MODELS.md from my
  snapshot copy; per-unit closure tokens from prereg/D2/freq): 2 of the 29 blocked units are blocked only by methods that
  1029Z already models — order 36 BooleanUtils.toInteger(Boolean,int,int,int) (Boolean.booleanValue()) and order 73
  NumberUtils.max(double[]) (Double.isNaN(double)). 9 blocked units carry some boxed/Character token.
- Java at 0149Z (the migration study's JimpleLean; copy replay/jim-0149Z, jimple-run built, 79 jobs): the same 41-program
  corpus gives 39 MATCH and 2 DIFF. Both DIFFs are programs added at 02:17-02:22Z for the D2 fixes (CharSeqIface,
  CharFamily); at 0149Z the interpreter stops with "wrong: no model for library method" (CharSequence.subSequence,
  Character.isTitleCase), exit 3. No program disagrees on a modelled behaviour — checks/val-jim-0149Z-20261025T1251Z.

## A3: mutation test re-checked from copies (checks/A3-20261025T1236Z/A3_CHECK.md; copies replay/a3-20261025T1236Z)
- Inputs: equiv-lean's five A3 reports and work files copied read-only (5,114 files, SHA256SUMS_copy.txt); the 16/16
  copy eq-20261025T1158Z (a572cf6). Charon/Aeneas, Soot and JDK 17 executed with outputs under ~/fv_paper only.
- 100/100 mutants rebuild from the PROVED source plus the stored patch (patch scripts assert single occurrences;
  whole-file mutants diffed against the proved original). Counts per program equal the reports: Rust 6/5/6/6/6/6/8/7,
  Java 7/5/6/8/7/6/6/5.
- 100/100: the report's own native harness, re-run in my copy (cargo debug / javac+java 17), shows the stated output
  difference on its case; 100/100 controls (original vs a second build of the original) identical. Every
  distinguishing input is inside the statement's hypotheses (field pictures, domains, record bounds, clock form).
- Proof failures, sample re-run (regeneration from the mutant + lake build with statements and proofs unchanged, in a
  copy of the equiv-lean tree; the copy unmodified afterwards):
  - CBACT04C Rust A5: fails at Every/RustRun2.lean:85 and :454; the restricted Cbact04c.Rust.rust still builds against
    A5 (standard axioms);
  - CBTRN02C Rust B5c: fails at Any/RustRun1.lean:105, :134, :214, :240; restricted Cbtrn02c.Rust.rust still builds
    (standard axioms);
  - CBACT01C Rust M1 at RustRun1.lean:128; CBACT02C Java J3 at JL/Cbact02cFormat.lean:75;
  - CBCUS01C Java J4: hits the 35-min wall as reported; with a 20M-heartbeat cap (the original passes) it fails at
    Cbcus01cFormat.lean:128 after 44 min;
  - CBACT04C Java M5r (capped run): original passes, mutant fails at Seg184 with findDisc's precondition ("DEFUALT").
  - Regeneration controls byte-identical.
- Wording points taken into the paper: the three non-error rejections are J4 (~30 min), M5r (34 min) and CBACT01C Java
  M2 (stopped after 83 min); several first errors are structural (layout changes from Aeneas/Soot), not at the mutated
  statement. Minor: the on-disk CBTRN03C Java K5 file is an older variant; the reported (script-generated) K5 is the
  one the proof run used. 1.63 core-h.

## C -> Rust: tiny-regex-c (copy replay/eq-20261025T1449Z = equiv-lean HEAD f8fc84c = 751764f + README/handoff,
## clean: 1141/1141 tracked files equal their blobs; checks/eqT-20261025T1449Z)
- Theorems (all standard axioms: axcheck 55 std incl. re_match_equiv; axcheck2 for the Rust.* names):
  - EquivLean.Demo.XLang.TinyRegex.re_match_equiv : EquivOn (Long ∨ NulIn ∨ CUB cRe) (Same C.mlOf) rustRun cRe, i.e.
    for pattern and text that are C strings (no NUL) with text < 2^28 bytes, wherever the C run is safe in cirlean's
    semantics (CUB := ¬ Safe (cRun x): UB or non-termination), Rust re_match returns normally with C's return value
    and final *matchlength. The C run is re_match(p, t, &ml) from the module's initial memory (CReMatch.cRun).
  - EquivLean.Demo.XLang.TinyRegex.Rust.re_compile_eq (re_compile = the model's arrays, WF, for every pattern);
    Rust.re_match_total and Rust.re_matchp_total (Result.ok on every input of any length).
- Provenance:
  - Rust crate examples/rust/tiny_regex: Cargo.toml and src/lib.rs byte-identical to veriforch's delivery
    runs/c2rust/tiny-regex-c/rust/ (lib.rs sha256 5cb11c43956c9e08...), final = guided/v1 (seed 1, first attempt),
    style guide styleguide_rust_c_v1.1.md (sha256 def9ffcb...).
  - Charon + Aeneas (equiv-lean's pinned binaries, run read-only, outputs in my scratch): tiny_regex.llbc, Types.lean
    and Funs.lean byte-identical to the committed files (rustregen/).
  - C side: re.c and re.h identical to my git-archive copy of tiny-regex-c f2632c6; clang -fclangir (upstream
    4955d32b) regenerates re.cir identical up to the source path in loc attributes; cir2lean of cirlean 28e2380 (and
    of ec40522) on the committed re.cir gives Demo/Gen/Cir/TinyRegex.lean identical except the header comment; from my
    regenerated re.cir it differs only in that comment and the module's `name :=` source-path string (cregen/).
- lake build --no-build of the 3 TRX + 19 A theorem modules in the copy: all 2610 jobs up to date.
- Kernel replay by delta against eq-20261025T1158Z: union closure 1011 modules (EquivLean 652, Aeneas 249, Cobol 43,
  CIR 42, Jimple 25); 86 replayed, 86/86 rc 0 (slowest 54.7 s); 876 reused (olean + closure byte-identical, passed
  before; all A modules among them, so A is unchanged at 751764f); 49 import-only roots.
- Translation protocol (veriforch c2rust loop docstring, INTERFACE.md, REPORT.md; to re-read from a copy at the
  freeze): guided arm = C sources + the style guide verbatim; plain arm = C sources + the agreed API block; one model
  call per attempt; feedback = build messages or <= 3 counterexamples (cirrun reference, cirlean 739fb2c); pass =
  natively and in the Aeneas extraction evaluated in Lean, equal results on all defined-behaviour cases, normal return
  on all UB cases; round 3038 cases (2676 defined, 362 UB), held-out 3006 (2588, 418). Runs: guided s1-s3 passed at
  attempt 1 ($0.55, $0.65, $0.51); plain s1-s3 at attempt 3 ($0.90, $0.90, $0.98).
  - The guide is TARGET-SPECIFIC (to state in the paper): it fixes the tiny-regex-c Rust API (structs, sizes,
    signatures, how to write re_match), names the C's two UB sites (matchstar's text-- at the start of the text;
    &pattern[2] = &re_compiled[31] after a fully matched 29-object pattern), and gives code patterns for this
    library's recursion group and backward scans.
- Sizes: re.c 528 lines (405 non-blank non-comment), lib.rs 497 lines; proof 7,134 Lean lines (C side 3,369, Rust
  2,119, model 1,557, equivalence 89) + 3,090 generated (C module + Aeneas extraction).

## D1/D2 lang3: the jimple adapter's interface-skipping defect (checks/lang3iface-20261025; DEVIATIONS 15:3xZ)
- Fix diff sha256 cf63d882... (adapters/jimple/build.py, live tree 15:2xZ). Skipped lang3 classes: 97 entries = 79
  classes (72 public interfaces, 5 annotation types, 2 package-private interfaces) + 18 package-info entries without
  methods; the 79 equal the orchestrator session's regex-only list (diff empty).
- Population (the orchestrator session, D2 pin, read-only re-extraction): in scope 3,823/5,068 -> 4,153/5,258 units with the fix.
- Sample, my count (tools/lang3_iface_count.py over D-pin closure tokens): D1 lang3: of 29 blocked units, 4 carry an
  interface-method gap token and 2 are blocked only by such tokens (orders 23 AbstractConcurrentInitializer
  $AbstractBuilder.<init>() and 82 FastDatePrinter.applyRules(Calendar,Appendable)). The orchestrator session's re-extraction agrees: the
  same 100 units in D1 and the D2 re-run, 5 carry (#11, #17, #18, #23, #82; #17 a timeout in D1), 2 blocked only by
  them, both in scope with the fixed adapter under both pins. D2 held-out: after it runs.

## D1/D2 lang3: veriforch's bridge-method key collision (checks/lang3bridge-20261025; DEVIATIONS 15:54Z)

- veriforch's Java unit index keys units without the return type and keeps the last declaration; Soot prints a
  covariant-return bridge after its method, so `--only` reached the bridge. Count from the D-pin class Jimple cache
  (tools/lang3_bridge_count.py; positive control DiffBuilder$16.getLeft()/getRight() flagged, negative control
  DiffBuilder$16.<init> not flagged): 74 colliding keys in 50 lang3 classes (agrees with the orchestrator session's 50 classes).
- Affected sample units: D1 lang3 0/100 (99 found in the cache; order 89 has no unit, an interface method); D2 re-run
  of D1's units 0 (84/100 run so far, same keys as D1); D2 held-out lang3 2/100 (orders 50 DiffBuilder$1.getRight(),
  80 DiffBuilder$8.getLeft(); 3 interface static methods not in the cache). Neither has run yet.
- At the freeze: check that orders 50 and 80 of the held-out run were run with the fix (or re-run as a crash fix).

## cirlean type-punned access defect: static scan (checks/punscan-20261025; DEVIATIONS 16:35Z)

- equiv-lean's punscan_v1.py (614835dc...) flags bitcasts between pointers to scalars of different widths; its run on
  equiv-lean's 22 ClangIR files (punscan_v1_e26fef2.out, 4199ae0b...): 0 flagged. My stricter tools/punscan_fv.py
  also lists casts INTO a scalar pointer from void/record/array pointers (possible puns through void*).
- My copies: C (vo-C) HIT 0, INTO 4; C2 (vo-C2) HIT 0, INTO 0; D1 zlib (vo-Dz) HIT 21 in crc32_z (u8 buffer read as
  u32/u64 words: the braid code), deflate, deflateParams, deflateSetDictionary and lm_init (u16 head array to bytes for
  zmemzero, a memset that cirlean already refuses at byte level); D1 tinyxml2 (vo-Dtx) HIT 0, INTO 10; vo-2 (D2
  tinyxml2, C1b, examples) HIT 0, INTO 10,411 (mostly malloc results to char pointers in C1b's cJSON TUs).
- D1 zlib claimed units (10 proved, 4 conditional): no HIT function in any closure; INTO casts only in gz_error
  (malloc -> char*) and inflateCopy (zalloc -> u8*). Open: whether cirlean types malloc'd blocks so that such accesses
  match (asked of the C maintainer session with the scanner request); then the same closure check for D1/D2 tinyxml2, C1/C1b/C2 verdicts,
  the cJSON harness units, T2/T3 and H.

## D1/D2: per-copy recompilation of generated modules (checks/slotrecompile-20261025; DEVIATIONS 16:24Z)

- veriforch's marking (prereg_slot_recompile_timeouts.tsv sha256 03fb599a..., .md 4d0daac6..., snapshot 16:51:29Z): 281
  timeout records (D1 complete; D2 partial). Only lang3 is affected: 19 timeouts (D1 16 of its 42 recorded timeouts,
  D2 re-run 3 so far) spent 1,565-1,786 s of the ~1,800 s wall compiling generated modules (the module text embeds the
  frozen copy's slot path, so each (copy, slot) pair recompiled ~6,080 modules); zlib, tinyxml2 and es-toolkit
  timeouts spent 0 s on it.
- My re-check of the 19 rows from the unit guard logs (check_gen.py -> check_gen_v2.out): all within 5 s of veriforch's
  values once commands live at the kill are counted to the kill; in none of the 19 did a proof check (cap 0.250) start
  inside the wall; all were killed at the wall.
- Paper: sec-sample now has one paragraph on the three Java tooling defects (interfaces, per-copy recompilation:
  \dSlotUnits = 16 of D's 44 lang3 timeouts, bridge methods: no D unit). FREEZE: refresh D2 counts when D2 ends.

## equiv-lean freeze commit = 751764f (announced by the equiv-lean maintainer session, 16:57Z)
- My checks at copy eq-20261025T1449Z (751764f; tracked 1141/1141) cover it: TRX theorems standard, delta replay
  86/86 + 876 reused + 49 import-only over the union closure of 1,011 modules; all A modules byte-identical to the
  a572cf6 checks. master after 751764f (c97775c at 16:35Z): README and HANDOFF only (git diff --stat).
- The equiv-lean maintainer session's clean freeze build (843/843 modules from an empty build dir, 7.69 core-h, 2 h 03 min; audit 26 rows standard;
  sweep Demo+Test 4480 theorems, 4472 standard + 8 Popcount bv_decide; Modernize 5827 standard): records copied to
  checks/eqfreeze-751764f (RESULT.md d9534df2..., checktimes.txt 71bc52bd..., times.csv 5f33977f...). Their module
  times vary about 20% between runs (import loading); tab:effort uses my sequential single-core clean build
  (eqclean, 350/607 at 16:59Z) and cites theirs as a cross-check.
- Paper: appendix pins now name 751764f for the migration study and add the C-to-Rust pins; tab:replay gains the
  C-to-Rust row (1,011 modules) and C2 tiny-regex-c (560/560).

## Assumption ledger (equiv-lean's tool, branch `ledger` 4c2a8db; checks/ledger-20261025T1724Z)
- Inputs verified: Ledger.lean 904caf00... (git show 4c2a8db), ledger_run.py c943ecf3..., ledger_lean.sh 31b44cad...,
  rows headline.tsv 392a8bfe... (26 rows: 17 A + 9 TRX). Run on a hard-link copy of my 751764f copy
  (replay/eqledger-20261025T1724Z): Ledger.lean compiled with `lean -o` into new files only (no lake, so no rewrite of
  linked artifacts); ledger_lean.sh's vendor root pointed at my copy's equivlean_work (diff recorded, ledger_lean.sh
  57501acb... in the check dir). 26/26 rows ok, 0.043 core-h.
- The per-theorem part (`sed -n '/^#### /,$p' ledger.md | sha256sum`) = 01bd7c96f93c24137640dcb73f4b160fa987568056e54400e6c483e0bb5fd866,
  identical to the equiv-lean maintainer session's. Findings (theirs, reproduced): no non-standard axiom; only opaque Aeneas.Std.wrapped (13 Rust
  rows); COBDATFT in the 2 CBACT01C rows; CP037 in 17 rows; the 9 Java rows use native models of Object, String,
  StringBuilder, ArrayList, List; re_match_equiv has the one hypothesis not (Long or NulIn or CUB).

## coblean evidence package: check-pattern gaps (from the COBOL maintainer session, 17:41Z) vs my re-run
- coblean found that make_evidence.py's `must` patterns at 2306Z were weak (V.stm `AGREE$` accepts DISAGREE; V.hand
  counts only equal lines; S4 accepts sorryAx). My cob_evidence_run.py compares the full output with the expected value
  exactly, so it does not inherit the patterns; and my copy's raw V.hand output (out/V.hand/hand.txt) has 0 "!! " lines,
  4 programs and 28 compared lines; V.stm's value ends in "same AGREE". No claim changes.
- NIST finding relevant to trust: the pinned front end drops DECLARATIVES with only a warning; no CardDemo batch
  program uses DECLARATIVES or USE (my scan of the 12 CB* programs), so the CardDemo theorems are unaffected.

## N: NIST COBOL85 run (b) census (checks/nist-20261025; PREREG_N_v1 + ADDENDUM_N_inputs)
- coblean's manifest nist_clb_final_manifest.sha256 (7d16fc6f...) verified against ~/nist_work (all OK); final.json and
  results.json of the six modules copied. My recount from final.json: 309 programs, pass 84, fail 46, unsupported 152,
  undefined 1, timeout 1, error 25; NC 95 (28/8/58/1 undefined), SQ 85 (36/25/15/1 timeout/8 error), IX 42 (9/11/13/9
  error), SM 17 (7/2/8), IC 25 (2/0/17/6 error), IF 45 (2/0/41/2 error): equal to coblean's table. Per-test matches
  (coblean): 2,419 of 2,525 GnuCOBOL entries over the 130 programs that ran to the end.
- Open (per the coordinating session): the COBOL trust claim waits for the cause labels of the 46 fails and 25 errors and their check against
  the theorem programs' paths (8 CardDemo programs, ACCTINT, BINCNT, RECSUM). Run (a) (2306Z front end) still running.

- N run (a), the labelled run with 2306Z's unmodified front end (copied to checks/nist-20261025/cla, hashes as sent by
  The COBOL maintainer session): my recount: 309 programs, pass 6, unsupported 279, error 24. By mechanism: frontend-unsupported 204 (199 stop
  at WRITE ... ADVANCING, my count from results.json; 5 at an earlier statement: NC302M, SQ303M, IF401M, IF402M,
  IF403M), frontend-reject 74, frontend-crash 1 (IX108A); the 6 passes write no report line in either system. The
  paper's 2306Z sentence must give this split.

## D2 lang3 re-run (copy replay/vo-Dl3r2-20261025T1735Z; checks/vo2l3-20261025T1739Z)
- Copy (17:35Z): worker dirs runs/prereg_d2_lang3{,_w1} with oleans, records/lang3/rerun (summary.json bd3d63b0...,
  outcomes.tsv 358de241...); JimpleLean 0300Z dependency copied from veriforch's deps: its SHA256SUMS (133 entries)
  checks and hashes to 5d577584... = pins.json bridge_snapshot_sha256sums; its 24 Jimple sources equal the 0300Z
  snapshot's.
- `d_outcome_check_v3.py` against prereg/D/sample_lang3.tsv -> d2_outcomes/lang3_rerun_check.txt: 100 rows = the
  frozen sample, 100/100 agree, counts and Wilson = summary.json: proved_model_stated 17 (0.109-0.256), conditional 4,
  partial 7, blocked 26, timeout 46; proved_mechanical, native, refuted, infrastructure_error 0. No infrastructure_error
  row, so the negative-cache reading does not apply; 21 unit logs mention the negative cache, all in rows already timeout
  (15), blocked (4) or partial (2) (negative_cache_grep.txt).
- Transitions vs D1 (same 100 keys; D1 orders 59 and 64 as timeouts under the negative-cache reading;
  transitions_lang3.txt): of D1's 19 proved, 14 stay proved, 2 become partial (orders 51, 76) and 3 time out (86, 87,
  96); 3 D1 timeouts are now proved (1, 4, 22); all 26 blocked units were blocked in D1 (D1 blocked 29: 26 stay, 1
  partial, 2 timeout). No refuted unit in either pass.
- Claimed theorems (17 proved, 4 conditional, 7 partial; worker 0: 16, worker 1: 12): every claimed unit has a checked
  `<module>_vc` (coverage_lang3_d2rerun.txt 28/28); axioms 28/28 standard (16 + 12). Kernel replay of the claimed
  closure (leancheck1lp.sh, explicit LEAN_PATH, guarded pjobs_v3 8/450/150/2): package modules 47 + 37 and JimpleLean 24
  (the import-only root Jimple skipped), 108/108 rc 0, 0.018 core-h. Closure check (closure_verdicts.py): 72 and 62
  modules per worker, all rc 0 or import-only.
- Interface defect, labelled post-hoc count (lang3_iface_count.py, D-pin closure tokens, 79-class list): of the
  re-run's 26 blocked units, 4 carry an interface token and 2 are blocked only by such tokens (orders 23, 82), the same
  two as in D1.

## cirpun scan of claimed C/C++ theorems (checks/cirpun-20261025; 2026-10-25T17:50Z)

- Tool: my copy of cirlean's flow-aware scanner cirpun (commit f365f63; SHA256SUMS 7e20b47d... verified; controls pos
  and neg PASS); driver tools/cirpun_claims.py; one run per claimed unit (or witnessed function) with the unit's
  ClangIR files linked as in its run; per-run TSV and summary per study, all rows in all_summary.tsv. Clean = no FLAG,
  CHAR, AGG or NOOBJ row.
- D1 zlib (vo-Dz; 15 library .cir, identical in the 3 workers): 14 claimed, 13 clean. inflateCopy's one ASSUME row
  (z_stream's internal_state used as inflate_state) is fixed by its statement (hst types the state block
  `.record "inflate_state"`). gz_reset: 3 NOOBJ rows in gz_error on the msg != NULL path, which gz_reset never takes
  (it passes NULL, gzlib.c:79; gz_error returns at `msg == NULL`); NOOBJ is UB at every pin, not a one-element meaning.
  No claimed closure reaches crc32_z's braid loads.
- D1 tinyxml2 (vo-Dtx; w0 and w1 unit.cir equal up to paths): 28 (21 proved, 5 partial, 2 refuted), 26 clean.
  PushDeclaration (#15) and PrepareForNewNode (#67), both partial: FLAG only for unresolved virtual calls (vptr loaded
  from the root `this`) and their function-pointer loads; the in-TU targets XMLPrinter::Write(const char*, size_t) and
  Putc, scanned as roots, give no rows.
- D2 tinyxml2 re-run (vo-2): 40 (29 proved, 1 conditional, 8 partial, 2 refuted), 37 clean. PushAttribute (#85,
  partial) and XMLConstHandle::ToElement (#95, proved): FLAG only for unresolved virtual calls; all in-TU targets (six
  ToElement implementations, Write, Putc) scanned as roots: no rows in their bodies. ToUnsigned (#91, refuted, the
  sscanf %u finding): NOOBJ 2 in SkipWhiteSpace through its null line-counter argument (guarded), not a pun.
- C2: tiny-regex-c, 121 proved or partial unit-steps over 26 commit directories, all clean; jsmn, 10 proved
  unit-steps, all clean.
- C1: the 11 functions with a behaviour-changed verdict (9 commits), old and new. The ClangIR of 6 of the 9 commits is
  no longer in veriforch's run tree, so all 18 versions were regenerated with the pinned clang (upstream-4955d32b) and
  the C1 targets' flags from git archives (c1/regen_c1_cir.sh); the regenerated files equal C1's surviving ones for 3
  commits (6 cJSON files, 2 tiny-regex-c files, identical up to paths). 22 scans, 18 clean; parse_array and
  parse_object (e0d3a8a, both versions): FLAG 2 each, both in get_decimal_point reading the result of localeconv (an
  unmodelled external), which the nested-array witness never reaches. C1b claims nothing (no verdict, no behaviour
  change).
- B: tiny-regex-c test1 (root main): FLAG 3, all for printf's extern FILE argument (unknown object); the cJSON overlap
  test (its entry function): NOOBJ 2 in cJSON_ParseWithLengthOpts (null return_parse_end, guarded), no FLAG, CHAR or
  AGG. For the record, the whole cJSON test program (main, 151 functions) shows AGG 35 and NOOBJ 37 from the analysis
  merging cJSON allocator heap objects across the other tests (e.g. Unity's string assertions over
  h:cJSON_New_Item); they are not on the claimed test's call graph.
- C to Rust (re.cir at 751764f): re_match, re_matchp, re_compile clean (SIGN only).
- Overall: in 242 scans, no claimed C/C++ theorem or UB finding reaches a data access of another width or kind; the
  only flags are unresolved virtual calls (their in-TU targets scan clean), reads of unmodelled externals' results
  (localeconv, FILE), and null-guarded NOOBJ paths. Pending: D2 zlib re-run and held-out, tinyxml2 held-out, the cJSON
  harness (veriforch), T2, T3, H.
- D1 lang3 update (17:50Z): order 59 is an infrastructure error (kernel deep-recursion crash; the 1728Z fix does not apply to D1 JimpleLean 1029Z; DEVIATIONS 17:49Z). D1 lang3 by R6: 19 proved, 4 conditional, 4 partial, 29 blocked, 43 timeout, 1 infrastructure error. Paper tab:sample and sec-sample updated.

## JimpleLean model-to-theorem demo: Math.floorMod (checks/floormod-20261025T1741Z)
- Inputs re-derived: Math.class extracted by me from the local JDK 17.0.20.1 jimage = 66d16712... (= the demo's);
  Soot 4.7.1 (jimplelean toolchain jar 7389c0e6...) on it regenerates java.lang.Math.jimple byte-identical
  (c04312c3...). FloorModLib.lean f232b86f... (demo SHA256SUMS OK).
- My own build of the JimpleLean 20261025T1728Z snapshot (copy replay/jim1728-20261025T1741Z; lake build Jimple, 75
  jobs, rc 0); the demo file with its jimple_import path pointed at my copy (one-line diff) compiles (rc 0);
  Demo.FloorMod.floorMod_implements_model depends on [propext, Classical.choice, Quot.sound]; leanchecker
  FloorModLib rc 0 and all 24 Jimple modules + the Jimple root rc 0.
- Statement: every terminating execution of the JDK 17 bytecode of Math.floorMod(int,int) ends in the outcome of
  JimpleLean's native model (floor modulus for y != 0; the same ArithmeticException object for y = 0).
- Licence: the Jimple is derived from OpenJDK (GPLv2 with the Classpath Exception); not for a public artifact without a
  licence check and the user's go. The paper may describe the result.

- coblean UNSTRING tester gap (from the COBOL maintainer session, 18:00Z): at 2306Z, unstringtest.py's generated DISPLAY line is 86 columns, so
  columns 73+ (the final POINTER, the TALLYING count and the overflow phrase) fall in the identification area that both
  GnuCOBOL and the front end ignore: V.us's 60/60 compared receivers, DELIMITER IN and COUNT IN only. No CardDemo batch
  program or example (ACCTINT, BINCNT, RECSUM) uses UNSTRING. The fixed tester (live tree, unstringtest.py dc3a4ef7...,
  same random stream) gives 60/60 for seeds 1 and 2 with pointer, tally and phrase compared, and kills M survivor #22's
  edit in a control. Paper: tab:fidelity's UNSTRING row must not be read as covering POINTER, TALLYING or OVERFLOW.
- coblean column-72 scan (from the COBOL maintainer session, 18:03Z): only the pinned unstringtest (60/60 programs) has text past column 72; the other generators (V.st, V.in, V.dt_std/bin/fe, V.ct, V.ct_fe, V.ft) and the 26 example and hand-written sources have none (scan script ~/coblean_runs/col72/col72_scan_v1.py); fresh --keep runs on the live tree reproduce the evidence tallies exactly. coblean plans an independent review of what each tester compares.

## M, coblean semantics: final (checks/Mcoblean-20261025)
- ANALYSIS_M_coblean_v1.md a89030d9..., pop_v1_analysis.tsv caf91bff... (copied). My recount from the per-mutant table:
  orders 1-30, none stillborn, 15 killed / 15 survived = 0.500 [0.332, 0.668]; harness status 14/16, one change under
  the 17:37Z reading (#9 StringInto.lean:80:10:CND, V.stm DISAGREE); per family tested/killed AOR 8/6, CND 3/2, LIT 9/4,
  LOG 1/0, ROR 7/2, STS 2/1; 11 sorries in 8 mutants; median 190 core-s per mutant.
- #4 (Arith.lean:65:8:ROR, quotExact `0 <= e` -> `0 < e`) labelled equivalent: Equiv4.lean (1fb87bf5...) defines exactly the
  mutated function (compared with the pin's quotExact) and proves quotExactMut_eq; it compiles against the 2306Z
  snapshot's oleans with [propext, Classical.choice, Quot.sound] (my run). Headline stays 15/30; the label is reported
  next to it. To do at the freeze: recompute the statuses from the raw outputs with analyze_v2.py (b0f6ad28...).

## N: NIST triage (triage_v3.md 751011ec...; final_census_b d3e78f86..., final_census_a c7ed10e9...)
- Fails: (i) dropped with a warning 34 (DECLARATIVES 33, ALPHABET 1), (ii) 11 (C1 NOT ON SIZE ERROR without ON SIZE
  ERROR 6, unclear standard; C2 INSPECT of a signed DISPLAY item 1; C5 FD record area from the first 01 2; C7 COPY IN
  ignored 1; C8 OPTIONAL status 05 1), producer 1; none (iii) or (iv). Errors 25, all front-end bugs (first-01 record
  area 12, RECORD data-name without KEY 5, link.py 6, ', -n' read as subtraction in MOD/REM 2).
- Theorem paths: no cause occurs in the 8 CardDemo theorem programs or the 3 examples (triage's IR walk); my spot check
  of the 8 sources agrees (no FD with two 01s, no COPY in the FILE SECTION, no NOT ON SIZE ERROR, DECLARATIVES, ALPHABET,
  COLLATING, SELECT OPTIONAL or COPY IN/OF; FUNCTION MOD with two arguments). Per-test 2,419/2,525 recomputed from
  results.json. The coordinating session's condition is met: the paper's COBOL validation text now gives the NIST census and the triage.

## D2 tinyxml2 held-out (copy replay/vo-Dtxh2-20261025T1813Z; checks/vo2txh-20261025T1814Z)
- `d_outcome_check_v3.py` against prereg/D2/heldout_tinyxml2.tsv and summary.json (948fba26...): 100 rows, keys = frozen
  sample, 0 disagreements; counts and Wilson = summary.json (driver: proved_model_stated 24, conditional 1, partial 11,
  refuted 2, blocked 16, timeout 44, infrastructure_error 2).
- Orders 60 (DynArray<char,20>::EnsureCapacity) and 64 (XMLUtil::ToFloat): unit logs "stuck (negative cache, 3 earlier
  attempts)"; their negative-cache entries (runs/prereg_d2_tinyxml2/cache/proofs/negative/9aae7438..., 23ac792d...)
  hold ordinary proof failures (a proposal parse error, an elaboration maxRecDepth error, a type mismatch, unsolved goals
  closed by sorry), no crash. Under the negative-cache reading both are timeouts: by R6, proved_model_stated 24 (95% CI
  16.7-33.2), conditional 1, partial 11, refuted 2, blocked 16, timeout 46, infrastructure_error 0.
- Refuted units, every recorded candidate re-run with cirlean d9ae8e5's cirrun (my copy, sha256 ac99f3bf... = veriforch's
  dep) on the worker's unit.cir: 16/16 outcomes equal the recorded replays (tx_refuted/rerun.out).
  - Order 5 XMLUtil::ToInt64, real_bug: convention-respecting decimal strings out of int64 range ("99999999999999999999",
    "9223372036854775808" = INT64_MAX+1) reach "UB: sscanf: format outside the modelled subset, or a value out of the range
    of its object": sscanf %lld of a value that is not representable is undefined (ISO C 7.21.6.2p10), the same class as
    the re-run's order 91 ToUnsigned. The hex candidates and "0x" hit the same generic message, which also covers formats
    outside the modelled subset, so only the decimal witnesses are citable; "", "-5" and "abc" return normally.
  - Order 79 XMLUtil::ToStr(bool, char*, int), missing_precondition: the 6 convention-respecting candidates return; only the
    2 convention-violating ones (bufferSize -1; bufferSize 20 for a 3-byte buffer) reach "UB: snprintf: destination is
    not a char range of the length needed". Not a library defect under its convention.
- Claimed theorems: coverage 36/36 (`<unit>_spec` checked; coverage_tx_d2heldout.txt); axioms of every VO theorem in both
  packages standard (w0 69, w1 65; the packages also hold the re-run's units); kernel replay 140/140 package modules rc 0
  (w0 72, w1 68); closure check: w0 109 modules (VO 69, Gen 1, CIR 38 rc 0 + 1 import-only), w1 105 (VO 65, Gen 1, CIR
  38 + 1), CIR verdicts from the d9ae8e5 dependency replay of checks/vo2-20261025T1141Z (dependency oleans byte-identical
  to veriforch's pinned dep). 142 guarded jobs, 0.166 core-h.
- cirpun (type punning) over the 36 claimed and 2 refuted units: 31 clean; non-clean rows are only unresolved virtual
  calls (#27 XMLHandle::ToDeclaration, #39 XMLPrinter::SealElementIfJustOpened, #84 XMLElement::FloatText, #93
  XMLElement::Name; their in-TU targets ToDeclaration x2, XMLPrinter::Putc, ToText x4, ToDocument x4 each scan clean
  as roots) and NOOBJ on XMLUtil::SkipWhiteSpace's null-guarded line-number pointer (#5, #42, #78, #84, #93). The
  eleven target scans ran without the core-hour wrapper (sub-second each).
- coblean tester review (18:27Z, from the COBOL maintainer session; verified items): V.ft never generates START (the package claim lists it); the 7 ok-negzero cases are 3 negative zeros (dt_std T00093, T00148, T00120) and 4 unsigned COMP-3 moved to signed (dt_std T00065, T00081; dt_fe T00012, T00013; nibble F vs C); V.in and V.us zero their counters before each statement (accumulation untested at 2306Z; live variants 240/240 agree, with a store-instead-of-add positive control); V.stm does not compare the control-block walk (by design); V.hand drops its header row. Paper tab:fidelity cells corrected (sign wording, counters from zero); no paper claim depended on START.

## H part one (checks/H-20261025; PREREG_H_v1 + ADDENDUM_H_selection; DEVIATIONS 16:41Z/16:59Z/17:39Z)
- Records copied: H_part1.md f1b609b2..., H_part1_results.tsv d226fdf2..., TRIAGE.tsv c7ab3630..., SUMMARY.tsv c889e5f4....
  My recount of H_part1_results.tsv (70 inputs): cgif_file_fuzzer 46/46 and cgif_rgb_fuzzer 9/9 stop at "memcpy:
  byte-level access not modelled" in readdata (the harness copies 2 input bytes into a uint16_t field: defined C, class
  (ii) model limit; all four sanitizer builds silent); yajl-ruby json_fuzzer 1/1 normal end; cjson_read_fuzzer 14/14
  normal end, but every seed ends in a newline so the harness returns at its first check; bzip2 no public corpus.
  Locator 70/70 and runner byte-equality 37/37 equal. Outcomes: cgif x2 blocked (memcpy limit named); yajl and cJSON
  "no UB on the corpus" (cJSON with the note); bzip2 "no public corpus". Part two: yajl-ruby only (starts after the
  cJSON stretch result). Note: yajl's one input was run early (DEVIATIONS 17:39Z).
- coblean corrected evidence TSV (declared later change; snapshot unchanged): EVIDENCE_carddemo_corrected_20261025.tsv
  58d1fdc3..., note EVIDENCE_corrections_20261025.md cd624bd5... (copies in checks/cobcorr-20261025); my diff against the
  2306Z TSV: 170 ids, only the claim texts of V.ft and V.st_negzero changed. Further verified tester limits (no claim
  change): filetest compares only the abending statement in an ok-abend program; difftest records IF and SIZE ERROR
  outcomes in one flag byte, so only the last write is compared; stm_check ignores exit statuses and RETURN-CODE (fresh
  OUT dirs in the recorded runs); RECSUM's WS-COUNT is never written.

## M, cirlean: final (checks/Mcirlean-20261025)
- results_cirlean.jsonl 0bb0039e... (ids = order positions 1-34, checked), .tsv 29b12c0e..., equivalence_labels.tsv
  5e4e3f0f.... My recount: 34 attempted, 4 stillborn (orders 12, 27, 28, 31: a definition no longer elaborates: ctzNat's
  termination proof; missing match cases after fuel-pattern literal changes), 30 tested: 7 killed, 23 survived = 0.233
  [0.118, 0.409]; per family tested/killed AOR 2/0, CND 2/1, LIT 12/4, LOG 3/0, NEG 1/1, ROR 9/1, UBG 1/0.
- Equivalence labels (apart from the headline): order 9 (Eval.lean:624, `sz > 0` -> `sz >= 0`): Order9.lean (3f1f5d5d...)
  proves the guards equivalent and the two ifs equal; the guard text equals the pin's line 624; compiles with core Lean,
  axioms [propext] (my run). Order 19 (Float.lean:216, fmtG 2^e -> 3^e): a written argument plus an exact replay, no
  Lean proof.
- 13 of the 23 survivors are float, printf or strtod code, which the 175-case suite barely exercises.

## T1 C/C++ rescan at cirlean ffab71e (T2's pin; a labelled second measurement)
- T1_cxx_ffab71e_units.tsv b711d865..., .json 7c5b9a4f... (copied). Frame (language, unit, path) byte-identical to T1's.
  My recount: C++ 2,054/4,608 = 44.6% [43.1, 46.0] (compiler 921/2,539 = 36.3%; library 1,133/2,069 = 54.8%; protocol
  426/699, transport 473/827, server 161/382, other 73/161); C unchanged 150/589. Paper: sec-thrift text + a rescan row
  in tab:thrift.

## M, JimpleLean: final (checks/Mjimplelean-20261025; DEVIATIONS 18:27Z)
- Re-run of the three false stillborns with run_mutants_v3.py (v2->v3 diff a7704f5c...; 421-proof validation
  1996817b...): Numeric:64:18:LIT:58 killed (8 proofs sorried), Numeric:260:58:LIT:275 and Numeric:204:14:CND:235
  survived (records 334a7e3a...). Final set M_jimplelean_final.jsonl 3f4b1b34...: orders 1-30 (checked), every status
  equal to its source record (v2 or v3); 16 killed / 14 survived = 0.533 [0.361, 0.698]. Non-counting attempts 31-33
  (76d128f3...) reported apart. One survivor labelled equivalent (Semantics:144:83:ROR:341, refEq's nondeterministic
  choice: the outcome set is unchanged, the definitions differ pointwise); reported beside the headline.

## V: LLVM test programs (checks/V-20261025; PREREG_V_v1 + ADDENDUM_V_sample)
- results.tsv ac02a5a3..., results.jsonl 034c4d9e... (copied; ids = the frozen sample, 200 unique). My recount:
  cir_kind MATCH 95, UNSUPPORTED 52, UB 25, EXIT 13, TIMEOUT 8, MISMATCH 5, CRASH 2; native_kind NATIVE_OK 177,
  NATIVE_FAIL 21, REF_DIFF 2. Primary shares among NATIVE_OK: MATCH 95/177 = 53.7% [46.3, 60.9], UNSUPPORTED 31,
  UB 25 (7 UBSan-confirmed), EXIT 13, TIMEOUT 8, MISMATCH 3, CRASH 2; MATCH among verdicts 95/123 = 77.2% [69.1, 83.8].
  Pending: the two stack-overflow programs re-run with an unlimited stack (crash fix, DEVIATIONS 18:38Z).
- Hex floating-point front-end bug (found by V, ieee/inf-1): float/long double hex constants are read as double bit
  patterns. My grep of every claim ClangIR copy: 0 files with `#cir.fp<0x` (D1/D2 zlib and tinyxml2, C1, C2, B, TRX,
  C1 regen). equiv-lean's 22 files: no `#cir.fp<` at all (the equiv-lean maintainer session). veriforch: Thrift TUs at ffab71e have 4 hex FP
  constants, all double (not affected); yajl 2, both double; cJSON harness none (the orchestrator session).
- coblean front-end fixes (declared later change; snapshot coblean-20261025T1839Z, from the COBOL maintainer session): my comparison with 2306Z: the 8 CardDemo IRs and cbstm03ab.ir.json byte-identical, all 43 Cobol oleans identical; diff -rq (without .lake, third_party) lists only the front end (cobolfe.py, copybook, datadiv, lexer, link, parser, source), new tests, docs and the fixed unstringtest. Paper sec-limits gains one sentence (later front end stops such programs; CardDemo representations byte-identical).
- cirlean M sorry step (from the C maintainer session, 18:48Z): run_mutant_m_v3.py re-lexes after every edit and edits bottom-up with an assertion; production order 33 had 2 theorems sorried in one pass with a clean rebuild; a non-population dry check broke 3 adjacent proofs and all were handled. Sorries per mutant are in results_cirlean.jsonl (6 mutants; see my check). No effect on the result.

## cJSON harness theorem (copy replay/cjh-20261025T1854Z; checks/cjh-20261025T1854Z)
- Copy of veriforch runs/cjson_parse/lean_v266d1ed (with oleans) and deps/cirlean-266d1ed; `diff -rq` against both
  originals is empty (copy_identity/). Records (15 units, assumed.json `[]`, verify.json) and the two logs copied;
  cJSON.cir 896f25d9..., cjson_parse_fuzzer.cir 1a8a051d... (= the announced hashes). SHA256SUMS in the check dir.
- Axioms (axcheck.py --leanpath, fresh process): 36/36 VO theorem names std, none with sorryAx (axcheck.tsv
  7b0d7b81...). VO.v0.cjson_parse_fuzzer.LLVMFuzzerTestOneInput_spec, the other 14 unit theorems (11 `<unit>_spec`,
  cJSON_parse_{array,object,value}_spec of scc_cJSON_parse_array) and cJSON_parse_array_scc_ind: exactly [propext,
  Classical.choice, Quot.sound]. No `axiom` declaration in the package's sources (Gen, GivenPA, VO, VerifOrch) or in
  cirlean's CIR; the sorry/native_decide hits there are comments and debug tactics.
- Kernel replay (leancheck1lp.sh via pkg_replay_jobs.py; pjobs_v3 8 450 150 2): 249/249 rc 0 (206 package modules,
  including the 58 GivenPA modules that the tool's normal mode leaves out, and the 43 CIR modules of the closure).
  closure_verdicts: the harness module's closure has 247 modules, Gen 127, GivenPA 58, VO 17, VerifOrch 1, CIR 43, all
  rc 0, plus the import-only CIR root (closure_harness.tsv 6b7a9585...); with every VO theorem module as a root, 249
  (VO 19). 250 guarded jobs, 0.084 core-h; the harness module replays in 4.9 s, the largest (Gen...Unit) in 81.6 s.
- Statement (statement/STATEMENT.md; `#check` in check_statement.out 8bff5111...): forall data size m, InitExt module m
  -> 0 <= size /\ size <= 2^64-1 -> ReadableBuf module.initMem.next m data size -> Returns ctx
  fn_LLVMFuzzerTestOneInput.sym [.ptr data, .int size] m (fun _ _ => True); sym = "LLVMFuzzerTestOneInput" by rfl; the
  binders are only the input, the memory and the three preconditions. In words: for every well-formed memory that keeps
  the globals at their initial values, and every live uint8_t[size] block after the globals holding bytes 0..255 with
  size < 2^63 (ReadableBuf's bound, tighter than hsize's 2^64-1), the call terminates, reaches no undefined behaviour
  (cirlean's ub also covers calls without a body or model) and returns normally; nothing is said about the result. It
  inherits the semantics' limits: malloc's model never fails (CIR/Std/Models.lean:451), and strtod, strncmp, strlen
  and the like run cirlean's models. Statement origins in the records: harness mechanical, units 6 llm and 8 given.
- Variant (DEVIATIONS 16:59Z): not visible in the statement. Visible in the ClangIR: the harness module is
  veriforch/scratch/cjson_parse_harness/cjson_parse_fuzzer.c, whose header says "Parse-only variant of cJSON's OSS-Fuzz
  harness fuzzing/cjson_read_fuzzer.c", and its only callees are cJSON_ParseWithOpts and cJSON_Delete; locales off:
  get_decimal_point returns the constant 46 (cJSON.cir:9003-9008), and neither .cir mentions localeconv. The run dir
  holds no build-flag file.
- cirpun f365f63 (--root LLVMFuzzerTestOneInput, both .cir): closure 15 functions (= the 15 units); FLAG 0, CHAR 0,
  SIGN 53, AGG 0, NOOBJ 2, ASSUME 0. The 2 NOOBJ rows are the stores through return_parse_end in
  cJSON_ParseWithLengthOpts (cJSON.c:1189, 1217), each under `if (return_parse_end)`, and the harness passes NULL:
  null-guarded and untaken. `#cir.fp<0x`: 0 in both files (6 FP constants, all decimal doubles).
- Proof size (tools/cjh_proof_lines.py with proof_lines.py's line rule; the harness closure): generated (Gen) 12,910
  lines in 127 modules; entry definitions 21; theorem headers 34 in 13 unit modules (one-line binders); proof scripts in
  the unit modules 1,251 (harness 126, parse_number 443, ParseWithLengthOpts 258); proof modules supplied whole
  (GivenPA 58, VO *_given 4) 6,756; cirlean library 11,492 in 44 modules, apart.
- Core-hours: the final run (guard_266d1ed_po1.log, 17:24:57-18:53:18Z) 1.585 core-h; it reused cached unit results,
  and the eleven 266d1ed guard logs in the run dir sum to 6.05 core-h (bundle builds of the owners elsewhere not
  included). Not done: regenerating Gen from the .cir files (the Gen headers name both).

## Pass 2026-10-25T19:15Z: V round 2, M-coblean set 2 release, N2, COBOL defects, cJSON paper text
- V crash fix round 2 (checks/V-20261025/crashfix2; runner v7 982b23d3... = v5 + env + --orders, diff read): orders 43
  and 84 TIMEOUT at 120 s, NATIVE_OK. Final counts (final_counts_crashfix2.txt): CRASH 0, TIMEOUT 10; NATIVE_OK 177:
  MATCH 95 (53.7% [46.3, 60.9]), UNSUPPORTED 31, UB 25, EXIT 13, TIMEOUT 10, MISMATCH 3; MATCH among verdicts 95/123
  77.2% [69.1, 83.8]. Paper: sec-stack LLVM paragraph updated (10 time out; two overflowed the stack first).
- M-coblean set 2: all 810 manifest lines re-hashed (checks/Mcoblean2-20261025/manifest_check.txt; base/ = 2306Z
  snapshot except CobolRun.lean and cobolrun = ws/base), new baseline rows 100/100 ok (baseline_check.txt), 12 old
  rows identical to baseline_v2, V.hand/V.stm same outcomes. S2M released: ADDENDUM_M_coblean_set2.md 40560565...;
  order2.tsv 8e8d5f9a... recomputed (order2_recompute.txt). coblean started the runs.
- N2 (checks/nist-20261025/cln2, n2_recount.txt): 85/13/193/1/0/17; per test 2,687/2,767 over 98 programs; run b
  recount unchanged (2,419/2,525 over 130). Paper: sec-stack NIST paragraph gains the labelled N2 sentences.
- Three COBOL semantics defects (C9 Edit.lean, M-syncsub Layout.lean, M-pos File.lean): coblean's walk 15 IRs 0 flagged;
  my regex and file-use walk agree (checks/cobdefects-20261025/NOTE.md). Paper: sec-limits sentence; FREEZE marker for
  the fix snapshot and coblean's re-check.
- cJSON parse-only theorem in the paper (sec-ub paragraph): statement, limits, 247-module replay, origins (mechanical 1,
  model 6, agents 8 + the entry's proof script), model's share of proof lines under 3% (PROOF_SIZE 227/8,056; my 225).
  sec-limits comment: cirpun row for the harness. No size or cost comparison with Theorem's proofs is made (the coordinating session's two
  rules apply if one is added: all-in agent cost; matching categories with the differences stated).

## Pass 2026-10-25T19:40Z: Java float model, FloatSem post-hoc count, T2 resume, cJSON full-harness bound
- JimpleLean Double.compare fault (9 wrong cases, NaN second argument or both NaN) in every pinned snapshot (1029Z,
  0149Z, 0300Z, 1728Z), fixed 1918Z; Float.compare and compareTo unmodelled (calls go wrong); equals correct. Claims check
  (checks/dcompare-20261025, controls pass): no claimed lang3 unit of D1/D2 reaches Double/Float.compare; A's Java
  translations have no float type. Paper: one sentence in sec-limits (validation by testing). T2/T3 Java: FREEZE_PLAN 17.
- FloatSem post-hoc (checks/Mjimplelean-20261025/posthoc_float; labelled, not independent): baseline at the 0300Z pin
  6,019 of 6,038 cases kept (19 Double.compare NaN cases dropped), 8 of the 9 float survivors killed, Numeric:241 (dcmpl
  NaN result -1 -> -2, sign-preserving) survives; 0.169 core-h. For the M paragraph: 16/30 headline + this labelled line.
- T2 crash fix 2: copy T2_20261025T191617Z 154/154 OK, only the driver differs (9ef65fef...); diff read; superseded units
  4 and 13 (Rust, workers 3 and 12, $0), in-flight 16/22/23/25 re-run; spend from usage logs ($0.37 not in ledger.json).
- cJSON full harness: bound size < 2^61 (rule fixed), 2^63 counterexample class by inspection; line references at
  acc76239 checked (checks/cjfull-bound-20261025/lines.txt) and window arithmetic (arithmetic.txt).

## Pass 2026-10-25T20:53Z (cron): C2, D, A, coblean 2014Z evidence rows
- (1) C2: no new step (C2 ended at its budget earlier; no file in runs/prereg/C/c2 newer than this summary).
- (2) D: no population finished: D2 zlib re-run 88/100 (20:38Z), lang3 held-out 46/100 (20:39Z); lang3 re-run finished
  earlier (checked). Watcher on both drivers (the orchestrator session).
- (3) equiv-lean: HEAD 7fed16b; 751764f..HEAD changes only HANDOFF_20261023.md and README.md (no Lean content, lakefile
  or manifest), so no new A theorem and nothing to replay.
- (4) coblean evidence snapshot coblean-20261025T2014Z (tester strengthening): full copy replay/cobE4-20261025T2048Z
  (diff -rq empty); the 22 changed and 4 new rows of EVIDENCE_carddemo_live_20261025T2014Z.tsv (0feb3ace...) re-run with
  tools/cob_evidence_run.py under the guard via pjobs_v3 (4 jobs): 26/26 match their expected values
  (checks/cobE4-20261025T2048Z/results), V.dt_bin {"mismatch":3,"ok":197}. Writes of every command reviewed (all under
  $OUT; bin_trace.sh and stm_check.sh work in $OUT).
- E: cJSON parse-only theorem cost verified end to end (engineers $112.96, cirlean helpers $240.91, shared $66.80,
  cirlean lead $810.39 unattributed); sec-ub sentence added.

## D2 zlib re-run (copy replay/vo-Dz2r-20261025T2256Z; checks/vo2zr-20261025T2256Z; checked 2026-10-25T23:11Z)
- Copy (22:56Z, while the zlib held-out driver ran in the same worker dirs): runs/prereg_d2_zlib{,_w1} with oleans,
  records/zlib/rerun (summary.json 65ca82e5..., outcomes.tsv d3b2ac29... = the announced hashes); dependency
  veriforch/deps/cirlean-d9ae8e5 copied, its 60 oleans byte-identical to the copy replayed in checks/vo2-20261025T1141Z.
- d_outcome_check_v3.py against prereg/D/sample_zlib.tsv: 100 rows = the frozen sample, 0 disagreements, counts and
  Wilson = summary.json: proved_model_stated 19 (0.125-0.278), conditional 1, partial 4, blocked 23, timeout 53;
  proved_mechanical, native, refuted, infrastructure_error 0. Five units killed at the 30-minute wall (orders 14, 17, 37,
  48, 69) are timeouts. No infrastructure_error row, so the negative-cache reading does not apply; 33 unit logs mention
  the negative cache, all in rows already timeout (21) or blocked (12). No refuted unit.
- Transitions vs D1 as recorded (transitions_zlib.txt; same 100 keys): D1 proved 10 -> 8 stay proved, 2 time out; 8 D1
  timeouts, 2 D1 conditionals and 1 D1 infrastructure error are now proved; all 23 blocked units were blocked in D1.
- Claimed theorems (19 + 1 + 4; worker 0: 10, worker 1: 14): every claimed unit has a checked _spec theorem (coverage
  24/24); axioms of every VO theorem in the claimed closures standard (w0 14, w1 16; no sorryAx). Kernel replay of the
  claimed closures (leancheck1lp.sh, explicit LEAN_PATH, guarded pjobs_v3 8/450/150/2): package modules 181 + 183,
  364/364 rc 0, 0.068 core-h. Closure check (closure_verdicts.py): w0 220 modules (Gen 167, VO 14, CIR 38 rc 0 + 1
  import-only), w1 222 (Gen 167, VO 16, CIR 38 + 1); CIR verdicts reused from the d9ae8e5 dependency replay of
  checks/vo2-20261025T1141Z (byte-identical oleans; all 38 rc 0).
- cirpun over the 24 claimed units: 12 clean; 9 clean with ASSUME rows only, all opaque-handle casts (gzFile_s used as
  gz_state, 5 units; z_stream's internal_state used as inflate_state, zlib's state idiom, 6 units incl. two non-clean
  ones), each statement fixing the state block by its record type or by its field values for any block type; NOOBJ in
  gzclearerr and gz_reset: gz_error's strlen/snprintf on state->path (gzlib.c:551, 557), untaken since both pass msg =
  NULL; FLAG in inflateBack (conditional): 19 unresolved indirect calls through the caller-supplied in/out callbacks
  (NEEDBITS/PULL/ROOM), on paths the theorem excludes: it covers only strm = NULL, which returns -2 at once.
- memcpy (overlap gap): one site in the claimed closures, inflateBack's infback.c:334 zmemcpy, on the same excluded
  path. Hexadecimal FP constants: 0 (no FP constant at all in the 15 library .cir files).
- Correction to the cirpun line above (same pass): the ASSUME rows sit in 11 units, gzFile_s as gz_state in 5 (orders 10, 15,
  23, 53, 67) and internal_state as inflate_state in 6 (5, 30, 40, 87, 93, 99): the 9 clean-with-ASSUME units plus the two
  non-clean ones (23 gzclearerr, 99 inflateBack).

## D2 lang3 held-out (copy replay/vo-Dl3h-20261026T0056Z; checks/vo2l3h-20261026T0056Z; written 2026-10-26T01:22Z)
- Copy: worker dirs with oleans + records (summary.json 7484d746..., outcomes.tsv a3611d1a... = announced); JimpleLean 0300Z
  dependency SHA256SUMS 133/133 OK, = pins bridge_snapshot_sha256sums 5d577584...; sample heldout_lang3.tsv 990ad46b... = frozen.
- d_outcome_check_v3: 100 rows = the sample; 99/100 agree; order 50 record status proved vs outcome blocked. Readings:
  order 84 negative-cache stuck after 3 ordinary proof failures -> timeout; orders 50, 80 (bridge collision) -> infrastructure
  errors pending veriforch's crash-fix re-run (heldout_bridgefix). Driver: proved 14 (0.085-0.221), cond 7, partial 6, blocked
  31, timeout 41, infra 1. R6: proved 14 (0.085-0.221), cond 7, partial 5, blocked 30, timeout 42, infra 2 (pending).
- Claims 26 (14/7/5): axioms std; kernel replay 687/687 rc 0 overall, claims' closure w0 24 + w1 55 + JimpleLean 25 all rc 0 or
  import-only. Double/Float.compare: 0/26 reach them (order 56 append(ZZ) name-level hit cleared by its body). Interface
  (post hoc): 30 blocked, 3 carry an own-interface token, 1 only by them (order 10). 1.12 core-h.

## java-total 9f0e5fb (pass 2026-10-26T02:28Z; fork check; copy replay/eqjt-20261026T0209Z; checks/eqjt-20261026T0209Z)
- Copy: cp -al of the equiv-lean maintainer session's clean-build worktree ~/equivlean_freeze_9f0e5fb-jtotal plus full copies of the vendor dirs
  (cirlean-28e2380, strictts-a15926a, coblean-20261024T2306Z, JimpleLean-20261025T2312Z, aeneas backends/lean). Tracked
  files 1322/1322 = 9f0e5fb (blob ids); JimpleLean 2312Z vendor sources 144/144 = snapshot SHA256SUMS c1808513....
  Unfollowed packages: same 9 git revisions and olean counts as the 1449Z copy, Mathlib.olean identical.
- Provenance: 751764f..9f0e5fb = 181 added files + 35 modified: 30 JL copies (only the provenance comment, snapshot
  0149Z -> 2312Z), HANDOFF, README, lakefile.toml / lake-manifest.json / scripts/lean1.sh (JimpleLean 0149Z -> 2312Z).
  No headline statement or proof file outside JL changed. Termination files: tools/termpk_check.py, 179/179 manifest
  entries with delivered sha256 = the Java maintainer session's manifests and integrated text = delivered text under the declared rename after
  the provenance line; the 6 other added files are JL Term copies; import_jl.py --check vs 2312Z: 36/36 same. #print with
  full names: each run_total = Jimple.total_of_sat_mterm with the same run_sat (or sat_runSpec_of_J of the same JL sat) as
  the headline java := statement_of_sat; statement forall args s, runSpec.pre -> (exists o, MExec Gen.prog runRef args s
  o) /\ forall o, MExec ... -> runSpec.post.
- Axioms (fresh process, tools/axcheck.py --leanpath): 32/32 std (8 run_total, 8 run_term, 16 headline).
- Kernel replay: union closure of the 8 run_total modules 655 modules (585 EquivLean, 43 Cobol, 27 Jimple); delta
  against the 1449Z copy: 578 replayed with leanchecker, all rc 0 (slowest 40.5 s), 77 reused (olean and whole closure
  byte-identical to modules that passed there); 2 import-only roots; closure_verdicts.tsv covers all 655. 0.75 core-h.
- Note: the headline statements' text is unchanged, but on this commit they are elaborated against JimpleLean 2312Z
  (newer models and tactics than the headline's 0149Z); the separate result rests on that later semantics version.

## T2 final (checks/t2-20261026T0321Z; fork; 2026-10-26T04:08Z)
- Records copied, 8 hashes = announced; 1,000 records = sample_T2.tsv by order and unit. Independent R6 recount: 991 agree;
  9 units (35, 65, 489, 523, 599, 770, 867, 890, 997) were killed at the 10-minute wall with no recorded status and mapped
  "blocked" by the driver from their static gap scope; the frozen reading gives timeout (blocked 459 / timeout 311 vs the
  driver's 468 / 302). EVIDENCE OWNER DECIDES which mapping the text uses. Proved counts unaffected.
- Proved (mechanical + model-stated), stratified [95%] and unweighted: all 18.7% [16.3, 21.1], 197/1000; C 16.0% [9.2,
  22.8], 21/127; C++ 13.9% [10.9, 16.8], 74/520; Java 25.6% [20.0, 31.2], 59/230; Rust 42.1% [32.8, 51.4], 43/123
  (3 mechanical). Conditional 10, partial 22, refuted 1 (254, union punning: model limit, re-run confirmed).
- Cost: model per unit median $0.159 (IQR 0.036-0.359), mean $0.235; records $234.85, usage logs $236.21 (1,784 calls),
  ledger $234.98; compute from the driver's guard log 30.36 core-h (5 segments); 450 units over the $0.25 budget.
- Claims 229: 258 theorem modules compiled from copies (rc 0), 258/258 std axioms, closure replay 879/879 rc 0.
- Scans: Java 902 reaches Double.compare (statement claims only an int result and unchanged state: unaffected); C/C++
  cirpun 91 clean, ASSUME rows discharged by typed preconditions, FLAG rows unresolved indirect/virtual calls, 3 NOOBJ
  atomics; 1 memcpy (54) between distinct objects; hex FP only double infinities. Details in NOTE.md.

## D2 zlib held-out (copy replay/vo-Dz2h-20261026T0526Z; checks/vo2zh-20261026T0526Z; written 2026-10-26T05:39Z)
- Copy (cp -a, 05:26Z): worker dirs with oleans, records zlib/heldout (summary.json 9891f37e..., outcomes.tsv 7651f6f6...,
  results.jsonl ec3e9e35...), zlib.out 106c3a29..., zlib.guard.log e4ffb0f8..., ledger.json 227dbe9f... (all = announced);
  cirlean d9ae8e5 dependency = pins, 60 oleans byte-identical to the vo-Dz2r copy; sample heldout_zlib.tsv e38c343c...
- d_outcome_check_v3: 52 rows = the sample; 51 agree. Order 24 inflate_fast: status stuck, attempts 0, 3 model calls in
  the held-out run all ending with stop reason refusal ($0.40), detail "LLM: model declined the request"; driver
  infrastructure_error, the R6 tool's stuck -> timeout: the evidence owner rules. Counts with order 24 as infra (driver):
  proved_model_stated 9 (0.094-0.297), conditional 1, partial 1, blocked 14, timeout 26, infra 1; as timeout (tool):
  timeout 27, infra 0. Wall kills (timeouts): 13, 16, 18, 19, 32, 43.
- Claims 11 (9 proved, 47 gz_error partial, 48 _tr_flush_bits conditional), all model-stated statements; 7 cost $0
  (cached proofs from the re-run). Axioms: w0 27 + w1 26 package theorems std. Replay 391/391 package modules rc 0; claim
  closures w0 212 / w1 213 modules all rc 0 or import-only (CIR verdicts reused on byte-identical oleans).
- cirpun 11/11 clean (ASSUME only in gzerror and inflateReset: zlib's opaque handles, typed by the statements); memcpy
  0 sites; hexadecimal FP constants 0. 0.079 core-h.

## T4 final ac65118 (checks/eqt4-20261026T0559Z; copy replay/eqt4-20261026T0559Z; 2026-10-26T06:26Z)
- Copy = cp -al of the equiv-lean maintainer session's clean build (1531/1531) + full vendor copies; tracked files 2109/2109 = ac65118; against 751764f
  968 added files, all Thrift paths, and HANDOFF/README modified: headline and TRX files unchanged.
- ROWS.md table: 25/25 theorems in their named modules, statements printed (print_rows.out); inputs and conclusions =
  the native table (W1, W2, R1, R2, R3, V1, V2, L1, exNegSize); hypotheses = ROWS.md for all 25 except a documentation
  gap: rlb_uuid and rlb_exNegSize also take NoRedeclL (not listed), and thrift_coll_hyps proves NoRedeclL and NoRedeclS
  too (ROWS.md says Contains, NoRedeclW), so it is discharged for Thrift's program. Corollaries by decide +kernel / rfl;
  thrift_classes_length = 277, no axioms.
- Axioms 890/890 std (836 public Thrift theorems + 54 named audit rows). Kernel replay of the 990-module union closure:
  721 replayed rc 0, 269 reused (byte-identical, passed in 1449Z). About 1.12 core-h.

## Rally R6: es-toolkit refactoring audit (StrictTS; labelled; checks/r6-20261026T2004Z; fork; written 2026-10-26T20:18Z)
- Report R6_RESULTS.md 214521cb..., r6_table.tsv c2caa541..., R6_EVIDENCE_SHA256SUMS 328ea254... (1,184/1,184 verify),
  pair sources 3,642/3,642 (= prereg/R6/pairs_SHA256SUMS bf561176...); tool 10ec829 = f6a4ec0 + difftool files only;
  results commit 53f98fcd changes only tools/difftool/r6. SUMMARY.md d9a58134275e84cc...
- Coverage: the 415 frozen pairs once each; PROVED 46 (43 all-worlds, 3 allocated-arguments), REFUTED Lean-confirmed 9,
  REFUTED Node only 77, UNKNOWN 283; on the 79 provable pairs 46 / 9 + 4 / 20; chunk JSON verdicts = table for every pair.
- Theorems: 46/46 re-elaborated from a copy at 10ec829 (lake: build current): exactly [propext, Classical.choice,
  Quot.sound], no error or sorry inside the theorem; compile errors in the files only in the 8 provable "no proof"
  UNKNOWN pairs and in the all-worlds variants of the 3 allocated-arguments pairs; no axiom, native_decide or sorry in
  the sources. Three statements read (hash order): same outcome and same final world for every host model, every
  argument of the declared types and every world.
- Counterexamples: 86/86 reproduce in plain node v22.22.1, byte-identical to the producer's out.json (old != new each);
  9/9 Lean confirmations reproduce with Lean outcomes = node outcomes; the 9 highlighted changes trace to rows + replays.
- Record points (no count changes): replay.tsv prints "arguments after the call=undefined" on the 7 rows where final
  arguments differ (out.json, the table and my replay agree); trimEnd's Lean confirmation file is outside the evidence
  manifest (scratch/difftool/history-20261026T091833Z-2179242/lean/batch_00.lean 172d6ea6...); the PROVED pair greet is
  a helper in src/function/spread.spec.ts, one of the 29 fix/feat type-only changes; allocated-arguments statements
  also assume each argument array shorter than 2^32 (paper states it).
- Cost: lead tokens $29.13 (169 calls, 08:39:34-09:53:30Z; checks/r6cost-20261026) + 1.07 core-h; my check 0.128 core-h.

## Rally costs (checks/cost-20261026T2014Z; fork; transcript copies + transcript_spend.py; written 2026-10-26T20:22Z; SUMMARY.md c646552de3e76878...)
Opus 5.5 list prices, dedup by message id. Coordination sessions (veriforch lead, the coordinating sessions) and my checks not included.
- R1: veriforch workers $427.37 (1,662 calls, incremental from 10-25 18:53:18Z; $540.34 whole incl. the parse-only
  $112.96) + cirlean helpers $587.89 (9 helpers, 1,849 calls; windows from cirlean's 20:2xZ message, date-only starts
  pinned to lead-message times) + cirlean lead $119.60 = $1,134.86 incremental; vo model calls $0 (--no-llm).
  With the parse-only theorem's $394.17: $1,529.03 cumulative.
- R2-64: veriforch workers $29.59 + cirlean floatnan $14.90 + cirlean lead $16.89 (overlap 09:15-10:06Z split 50/50) = $61.38.
- R2-32: cirlean lead $11.26; a session ran 208 calls on another vendor's model in its window (tokens
  in 35.8M, out 0.13M, cache read 72.0M): not priced yet.
- R3: phase-2 agents $560.05 ($635.75 with an agent whole + w-theorem); phase-1 vo model calls $61.12 (1-h cache-write
  rate; $60.75 at the 5-min rate).
- R5: equiv-lean agents $262.37 (1,223 calls); lead $89.74 in the window (upper bound: also ran R7's clean build).
- R6: $29.13. R7: $42.74 (lead $32.04 to 10:07Z + helper $10.70; producer $42.52, window end).
- Shared tooling, not attributed: cirparser $6.13, cirstd $9.52, the string-walk helper (in the parse-only total).
- R2-32 addendum (2026-10-26T20:32Z): a session's 208 calls in 08:40-16:11Z, priced at its proxy's rates ($4 in, $20
  out, $0.20 cache read per MTok; ~/argon-proxy/argon_proxy.py:56): $160.20 from the transcript tally; the proxy's own
  request log gives $164.84 (219 requests). R2-32 total: cirlean lead $11.26 + $164.84 = $176.10.

## Rally R5: jsmn C -> safe Rust (equiv-lean r5-final 373874f; checks/eqr5-20261026T2004Z; fork; written 2026-10-26T20:32Z)
- Copy of ~/equivlean_freeze_373874f-r5final: 1,190 tracked files = 373874f blobs, nothing extra or missing; vendor pins
  = my 751764f copy; 51 files changed since 751764f: 34 new jsmn Lean modules, 15 example files, README/HANDOFF.
- Axioms (fresh process): 32/32 named rows exactly std (6 jsmn: jsmn_equiv, Rust.rust_spec, rust_rspec,
  C.jsmn_parse_pspec, C.parse_string_pspec, C.jsmn_parse_primitive_pspec; 9 TinyRegex; 17 Modernize); the 34 jsmn sources
  have no sorry, native_decide, axiom or kernel bypass.
- Kernel replay: jsmn_equiv's closure 340 modules: 92 replayed rc 0 (every jsmn module), 248 reused (byte-identical
  oleans, replayed in earlier checks); leanchecker negative control still rc 1. The 26 non-jsmn rows: axioms rechecked,
  modules not replayed in this tree (sources unchanged since 751764f).
- Provenance: jsmn.h = zserge/jsmn 25647e6 (c04533e9...; 353 of 471 lines non-blank non-comment); ClangIR + cir2lean at
  cirlean 28e2380 regenerate the committed files up to source-path strings and the header comment; Charon/Aeneas
  regenerate the committed .llbc, Types.lean, Funs.lean exactly; lib.rs has no unsafe.
- Statement wording: the exclusion is "the C run has undefined behaviour or does not terminate" (C-side theorem covers
  returning runs); the equiv-lean maintainer session's "only UB case met is num_tokens >= 2^32" is not a proved fact (num_tokens is a U32).
- Proof lines 6,076 (model 798, C 3,207, Rust 1,980, glue 91; the equiv-lean maintainer session counts RustDefs as glue: 1,949/122). Tests: seed-1
  differential rerun 32,245 cases, C and Rust output identical; not rerun: seed 2, the 322,775-input model-vs-binary
  test, the equiv-lean maintainer session's clean build and sweep. Check 0.36 core-h. SUMMARY.md 02d4dd06a0a2461e...

## Rally R7: T4 Java total correctness (equiv-lean t4-java-total 613c77c; checks/eqt4jt-20261026T2003Z; fork; written 2026-10-26T21:04Z)
- Copy: 2,343 tracked files = 613c77c blobs; 85c9806 adds exactly the 53 Demo/Thrift/Java/Term files = T4Term-20261026T0955Z
  package SHA256SUMS ad16b0c9 (53/53); 613c77c changes only ROWS.md and README.md; since ac65118 the only other Thrift change
  is ZzB.lean (two proofs, statements unchanged). JimpleLean 2312Z: snapshot sums c1808513 = 144 vendor files;
  import_jl.py --check 36/36; all 1,765 modules have build files dated inside the equiv-lean maintainer session's build window (10:12-12:15Z).
- Statements (Lean meta check, fresh process): 68/68 *_total = STATEMENTS.tsv, each (exists o, MExec P m args s o) /  (forall o, MExec .. -> C). 61: C = the partial theorem's conclusion, all its hypotheses present, extra binders exactly the
  termination premises (all 42 E/D/M table theorems by name + 19 method contracts). 7 contracts checked for form only:
  zz32/zz64/uzz32/uzz64_total (no named partial theorem), rv64_total (stated for rv64SpecI; a derived statement for rv64Spec
  elaborates with std axioms), rfiA_total, wi16A_total. Premises = STATEMENTS.tsv: none 12, TransportTerm + BConc 15,
  TransportTerm + TConc 22, TransportTerm + TRepConc 19; the 8 row totals carry exactly ROWS.md's premises.
- Axioms: 81/82 named rows exactly std, thrift_classes_length none; all 185 public Term theorems std; no sorry.
- Kernel replay: closure of the Term modules + named rows' modules 1,898 modules: 868 replayed rc 0 (slowest 144 s),
  1,030 reused (build file + whole closure byte-identical to modules passed in eqt4/eqjt/1449Z checks); none uncovered.
- The equiv-lean maintainer session's RESULT.md (1765/1765, 82/82 std) consistent; its full sweep not redone. Doc notes: README's new table omits 9
  callee-contract totals (gtt, rb, rfiA, uzz32, uzz64, wbd, wi16A, zz32, zz64); rv64_total is stated for rv64SpecI.
  Disclosures by the fork: one git status on the equiv-lean maintainer session's worktree before read-only git; one rm -f of its own intermediate file.
  Check 1.05 core-h. SUMMARY.md 8fd940fb4e8944fa...

## coblean live snapshot coblean-20261026T1055Z (later changes M-pos, C5; checks/cob1055-20261026T2004Z; fork; written 2026-10-26T21:22Z)
- Handoff ~/coblean_runs/handoff_to_paper_20261026.md 43d2a50c...; manifest a49973ce... sha256sum -c 305/305 OK; full copy =
  snapshot before and after the runs (diff -rq empty).
- Sources vs 2114Z: only M-pos (IR.lean FileSt.bound; File.lean fileOpen/fileRead/fileWrite/fileStart under
  d.access == .dynamic), C5 (parser.py: record area = largest 01; 01s of different lengths without RECORD = variable
  length), Logic/Eval.lean (two names added to the cobol_eval attribute list; in coblean's diffs, not named in its
  10:56Z message), new testers, docs and make_evidence.py rows; my diffs = coblean's diffs_live/diffs_final.
- TH0 from source on one core 1,600 s: "Build completed successfully (115 jobs). | standard: 24 | bv_decide: 1" (25 axiom
  lines = my 2114Z re-check). Cobol.olean be3132eb; 5 of 43 Cobol oleans differ from 2306Z (Edit, IR, Layout, Logic/Eval,
  Sem/File); 9 CardDemo IRs byte-identical; 19 theorem-module oleans changed with statements and axioms unchanged.
- TSV EVIDENCE_carddemo_live_20261026T1055Z.tsv 3309d648...: 95 rows re-run, all match (TH0, 50 TH ax/st, IR, IRFE, IRB,
  line counts T4 3128 / E4 6666 / T7 3234, the 20 new rows each exact-N); "171 identical rows" holds apart from the
  checked_utc column. Controls on unfixed 2114Z: pos_check 11/20, fpos seed 51 96/100 (= coblean's).
- NIST: C1 class (iii) from IBM Enterprise COBOL 6.4 "SIZE ERROR phrases" (quoted in full: without ON SIZE ERROR,
  truncation rules apply); C2 class (ii) from "INSPECT statement" table 1 (excerpts; a second fetch failed): signed
  external decimal inspected as if moved to an unsigned DISPLAY item. No theorem IR has an INSPECT tag (positive control
  passed); no theorem source uses INSPECT. Not checked: the NIST singles on the 14 C5 programs, the cov mutant-plant
  controls, the R4 (i) probe figures. Check 0.929 core-h. SUMMARY.md 17c4723d7b12f2b7...

## Rally R1 (checks/fh-r1-20261026T2003Z; fork; written 2026-10-26T21:48Z; SUMMARY.md c22d54bd461320ee...)
- 23/23 announced hashes; closure 32 units, all proved, assumes []; statement = the adapter's mechanical entry statement
  with size < 2^61; 90/90 VO theorems exactly std; kernel replay of the entry's 285-module closure rc 0 (242 package + 43
  CIR); sources = cJSON v1.7.18 tag files (unmodified upstream harness), ClangIR and Gen regenerate byte-identically;
  proof lines 15,849 (O 11,354, E 3,835, M 224, V 436; G 12,820); cirpun 32 functions, FLAG 2 (localeconv model reads),
  NOOBJ 2 (null-guarded, untaken); 1 hex FP constant outside the closure. Check 0.106 core-h (with R2-64: 0.212).

## Rally R2-64, EMBARGOED (checks/fh-r264-20261026T2003Z; fork; written 2026-10-26T21:48Z; SUMMARY.md 39f59bd3aa2e3c13...)
- 19/19 announced hashes; 32/32 units proved, assumes []; size bound only ReadableBuf's 2^63; 90/90 std; 285-module
  closure rc 0; source = v1.7.18 + one 7-line hunk in one function (FIX.diff sha256 only); ClangIR and Gen regenerate;
  vs R1 real changes only in the patched Gen function, its spec bundle (= cirlean's) and the three entry modules;
  proof lines 15,846. Not a public paper claim until the embargo ends.

## Rally R3 (checks/yj-r3-20261026T2007Z; fork; written 2026-10-26T21:48Z; SUMMARY.md 04cad3a0ce6d35cc...)
- 11/11 announced hashes; 42/42 unit theorems std, no axiom declarations; entry closure 193 modules rc 0 (192 replayed,
  1 import-only), 202 with all unit modules as roots; statement as announced (size < 2^31); 34 bundle files = frozen given
  copies (import prefix normalized), 39 tactic bodies verbatim; pin = T2 check's ffab71e, unchanged; the three noop units
  have no unit theorem (only generated definitions in the closure); orch snapshot SHA256SUMS lists itself (75 others
  verify). Pending (an agent): cirpun, ClangIR/Gen regeneration, proof-line recount. Check 0.125 core-h.

## Rally R2-32, EMBARGOED (checks/r232-20261026T2007Z; fork; written 2026-10-26T21:48Z; SUMMARY.md bb6dd6c33d79a176...)
- Tree sums 703/703; source/olean hashes; pin build manifest 113/113; 93/93 std; 285-module closure rc 0 (283 + 2
  import-only); size bound from ReadableBuf n < 2^31. Beyond the delivery's description: two more rfl lemmas of the same
  form as ctx_ptrBytes (cJSON_ParseWithOpts.lean:13, cJSON_ParseWithLengthOpts.lean:17; theorems, not axioms); simp-lemma
  renames (PrintObjectStep.lean:1078-1079); one doc comment; CIR.Logic.CJString compiled in the tree from the pin's source
  (my recompile: byte-identical olean). Other non-width changes = the four named sites. Not done: Gen regeneration, the
  i686 difftests. Check 0.106 core-h. Slip (fork): pjobs_v3 scheduler ran outside a guard (every job guarded).

## E: all-in model cost of the migration proofs (checks/costA-20261026T2150Z; fork; written 2026-10-26T21:54Z; SUMMARY.md c571a03b3fd5dddf...)
- Records: equiv-lean $2,398 (HANDOFF 10-25 14:00Z: total $2,801 minus TRX ~$407, split by agent); veriforch $159.37
  (A_SPEND.md 10-24 21:24Z; includes the $50.57 translation calls); coblean $343.58 (my recount, 10-24 08:30Z-10-25
  14:02Z); JimpleLean $281.33 (its ledger). Sum $3,182.28; proof work without translation calls $3,131.71 -> paper $3,130.
- equiv-lean transcripts (lead + 24 subagents, copies): $2,801.10 for 10-24 08:30Z-10-25 14:00Z (= ledger $2,801);
  12:00Z $2,674.75 and 15:20Z $2,820.55 also match; the A/TRX split is not reproducible exactly: A between ~$2,394 and
  ~$2,430 depending on the lead's share.
- Not in any record: equiv-lean 14:00-15:20Z $19.44 shared A/TRX (merge + 751764f freeze build); veriforch coordination
  after 10-24 21:24Z (~$3/h, ~$50 to the A freeze); work before 10-24 08:30Z; coordinating sessions; my checks.

## T3 final (150 commits; checks/t3-20261026T2147Z; fork; written 2026-10-26T22:13Z; SUMMARY.md 4cc24ff5c7decdb6...)
- Copy: small files + hard-linked lean_cert/lean_eqj/ci/unit.cir of the 26 witness/theorem run dirs (0 symlinks); deps =
  veriforch's frozen T3 deps (cirlean ffab71e, equiv-lean b171660 for C/C++, 751764f + JimpleLean 0149Z for Java); 7/7
  announced hashes; 150 records = prereg/T/t3_commits.tsv.
- Census (own code; per language by each language's own functions): C++ 7 bc / 9 partly / 44 unknown / 12 no changed
  function / 1 blocked; C 3 / 0 / 23 / 0 / 0; Java 6 / 0 / 25 / 3 / 0; Rust 0 / 0 / 17 / 3 / 0; total (commit once) 16 / 9 /
  106 / 18 / 1. veriforch's C row 3/1/22 (overall outcome per language touched; order 101). No-changed-function orders: 8,
  15, 22, 23, 37, 38, 39, 46, 56, 66, 67, 68, 69, 117, 132, 133, 140, 148; blocked: order 2.
- Verdicts: 54 equivalent (C++) in 13 commits (32, 50, 57, 58, 72, 77, 79, 89, 101, 105, 116, 138, 142; 50/58/72/77 also bc);
  108/108 theorems std; closures 197/197 rc 0. 38 behaviour_changed in 16 commits (C 3, C++ 18, Java 17), all reproduce.
- Scans: cirpun 74/108 clean; shared_ptr 64-bit counter load (shared_ptr_base.h:336) in 12 verdicts (TEvhttpServer::complete
  x11, ~TFileTransport); other flags library-result reads, unresolved virtual calls, setsockopt-failure paths; memcpy 18
  sites, distinct objects, error path. Double/Float.compare 0 hits. Unknown reasons tallied (outcomes/unknown_reasons.tsv).
- Spend: $189.77 (1,672 calls, 204 refusals) / kept $164.96; core-h 157.90 + 22.72 (072 superseded; veriforch said 22.404).

## Rally R3: the items marked pending above (checks/yj-r3-extra-20261026T2154Z; writer agent; written 2026-10-26T22:46Z; SUMMARY.md 315e5ae82e98a12e...)
- ClangIR (7 .cir files) and Gen (75 files) regenerate byte-identically from yajl-ruby 6501652d1135 (1.4.3) and OSS-Fuzz
  bd2ce21991a9's json_fuzzer.c (the commits Theorem's project.yaml pins). Proof lines E 7,196 + M 57 + V 432 = 7,685
  reproduced (193-module closure, 30,027 lines = the producer's table). cirpun: 45 functions, CHAR/AGG/ASSUME 0, FLAG 1103
  all on objects the scan cannot identify (allocator/callback pointers), NOOBJ 1 and SIGN 5 on an untaken branch: no
  wrong-width access found, none ruled out. memcpy: R3 closure 2 sites, R1 closure 5 sites, all between distinct objects.

## Rally R6: kernel replay of the 46 proofs (checks/r6replay-20261026T2241Z; fork; written 2026-10-26T22:54Z; SUMMARY.md 3eba1606c584d854...)
- The 15 proof files compiled to oleans in my dir (7 of them after leaving out 16 failing theorem blocks of unproved
  pairs, the same list as the r6 check's error list; the 46 proved blocks byte-identical); 15/15 replay rc 0, the proved
  theorems print exactly the standard axioms; import closure 47 StrictTS modules at 10ec829, 47/47 rc 0; lc_neg BadCtl
  rc 1, GoodCtl rc 0. 0.091 core-h. Closes claims-audit finding 3 for R6 (tab:replay row added).

## T4 UUID containers, native (checks/t4uuid-20261027; written 2026-10-27T00:24Z)
- equiv-lean's driver UuidListRoundTrip.java (743b840c) recompiled by me against thrift-java-f0eb8b84.jar (d7b84d85, the jar of
  checks/t4native-20261026) and run on JDK 17 and JDK 25: Java writes a list, a set and a map of UUIDs with TCompactProtocol and
  TBinaryProtocol and reads each back; all six reads throw TTransportException "unrecognized type code"; result lines = equiv-lean's
  output. Paper: one native-only sentence after the L1 row. The cause (a missing UUID case in getMinSerializedSize) not checked by me.

## Rally R6 erratum (StrictTS master 6ac88b4, R6_ERRATUM_20261027.md 5b4e9313; checks/r6erratum-20261027T0027Z; fork; written 2026-10-27T00:31Z)
- tscheck_cex.js re-run from copies (TypeScript 5.9.3, Node v22.22.1) byte-identical to tscheck.tsv 1dbd9852: 76 of the 86
  counterexample calls type-check against the public signatures in both versions (all 9 Lean-confirmed, 67 of 77 Node-only); 10
  check in neither (zip x2, zipWith x2, delay, repeat, random x2, template, orderBy), each outside every public overload by the
  old and new declarations. Perf/style highlights 6 -> 4 (uniq, toPath x2, areObjectsEqual: internal, its own any-typed
  declaration admits the call); docs/test/bench highlights stay; PROVED unaffected. Paper sec-fixes, abstract, intro updated.

## CBSTM03B all-input theorem (coblean; checks/cbstm03b-20261027T0113Z; fork; written 2026-10-27T01:25Z)
- Snapshot coblean-pin2306Z-cbstm03b-20261027T0112Z = 2306Z + Examples/Cbstm03b.lean 36018f28 + cbstm03b.ir.json 38fa862f;
  oleans identical to 2306Z (Cobol.olean be3132eb); IR regenerated from the unmodified CardDemo 59cc6c2f source (--sub) byte for
  byte; CardDemo.Cbstm03b.cbstm03b_call: exactly std axioms; 44-module closure replay rc 0 (43 Cobol + new), negative control
  rejected. Statement: every 2,248-byte storage and every state of the 4 files, record-length preconditions, KEY-LN 1..25 and
  ACCT digit keys for keyed reads -> run ends in GOBACK with the storage and file states of call3b. GnuCOBOL differential seed 1:
  720/720 agree; RC-mutant control 376/720 differ (= coblean). Fault outside the precondition reproduced (call 400: ACCT keyed read,
  9 digits with KEY-LN 11: coblean invalidData, GnuCOBOL continues). Paper: sec-migration opening paragraph.

## T4 nibbles 14/15, Java native behaviour (checks/t4nib-native-20261027; written 2026-10-27T01:40Z)
- The coordination session's driver NativeT4Nib1415.java (3104fd39) recompiled and run by me against thrift-java-f0eb8b84.jar
  (d7b84d85) on JDK 17, over TMemoryInputTransport and TMemoryBuffer: readFieldBegin on [1E]/[1F] and readListBegin/readSetBegin
  on [0E]/[0F] all throw TProtocolException "don't know what type: 14/15", consuming 1 byte (12/12 cases). The Lean package
  (t4-java-nibbles a9c8e23) is checked separately when equiv-lean's kit build reports.

## coblean live snapshot coblean-20261027T0050Z (INSPECT fix; checks/cob0050-20261027T0052Z; fork; written 2026-10-27T02:06Z)
- Manifest de3366e5 307/307 before and after; copies = snapshots; diff vs 1055Z only the fix (Inspect.lean, Exec.lean, 1 line of
  Eval.lean), the new tester, 2 rows, README/HANDOFF; TH0 115 jobs, 24 standard + 1 bv_decide (axiom lines = 1055Z); Cobol.olean
  be3132eb; 4 Cobol oleans changed (Logic/Eval, Logic/FuelMono, Sem/Exec, Sem/Inspect); 9 CardDemo IRs identical to 1055Z and
  2306Z; TSV 191 rows unchanged apart from checked_utc, 3 line counts, V.ins.s1/s2 60/60; 78 rows re-run, all match; controls:
  tester on 1055Z 0/60 and 1/60; NC216A 57/57 at 0050Z, 56/57 at 1055Z. Model: signed DISPLAY items inspected without their sign
  (separate sign byte excluded and kept; embedded sign removed and restored; a non-digit left in that byte unsupported). Paper:
  limits now list all four COBOL defects as fixed in later versions; appendix lists 0050Z.

## cirlean next e6ac99a (integration pin; checks/cirnext-20261027T0143Z; fork; written 2026-10-27T02:09Z; SUMMARY.md 5bb26395...)
- Records 15/15 and build manifest 126/126 match; build output read-only, HEAD e6ac99a; 8-step merge history and diff stats =
  the record (fuzzer266 c4ef58d, punning2 cbbf0b7, hexfp af0c0d4, ilp32 e00113f, unionpun ad01e8e; d8afb97, c674a7b); 36 files
  changed vs c4ef58d, 41 vs 28e2380. Regressions re-run from a copy: C++ cases 177 MATCH + t_gap_emplace UB, identical to
  c4ef58d; floats 1120/1120; punning 4 UB as labelled; unions 39 MATCH + 10 UB = labels (49); i686 and x86-64 13/13. 20 Examples
  statements only gain hypotheses (CHANGES_punning2.md), 6 unchanged, 2 new, all std. Census: static identical (2977); dynamic
  192/193 same, math_inv_sqrt UB reason -> type-punned access. Not re-run: older punning/union baselines.

## M JimpleLean set 2 (labelled; prereg/M/ADDENDUM_M_jimplelean_set2.md; records replay/jset2-20261027T0100Z/runs/set2; written 2026-10-27T02:20Z)
- Seed committed in DEVIATIONS before the suite existed; extended suite frozen (manifest 5e21e3e8, 2,364 files, re-verified;
  baseline 63/63 agree); seed released and order drawn by the evidence owner (order2.tsv 70390558, 419 candidates, independent
  recomputation equal). Runs by the evidence owner's agent: positions 1-30 all built; my recount from M_jimplelean_set2.jsonl
  (767ccf56; SHA256SUMS 57ea0618 verifies): detected by the old suite 20/30 (Wilson 48.8-80.8%), by the extended suite 24/30
  (62.7-90.5%), extended only 4 (Numeric:53 AOR, :201 LIT, :83 LIT, :84 LIT; float testers), 6 not detected. Controls: no-op not
  detected; known-bad Native.lean edit detected by 22 old programs (= set 1) + 6 new. Paper: sec-stack mutation paragraph.

## T2 re-check of units 132, 254, 566 at cirlean next e6ac99a (labelled; checks/t2union-20261027T0208Z; fork; written 2026-10-27T02:34Z; SUMMARY.md c9a77649...)
- Outside PREREG_T_v1 (another pin; final pass above the $0.25 per-unit budget). All three compile from copies against the
  frozen next pin, print exactly the three standard axioms, and replay: 45 modules per closure (48 distinct), all rc 0.
- 254 (thrift_bitwise_cast_gdouble): every guint64 whose bits are not a binary64 NaN (2^64 - 2^53 + 2 inputs), every memory:
  returns normally with some double and no caller block changed. 132, 566: every non-NaN double: returns normally an integer
  in [0, 2^64), no caller block changed. Values not characterised. NaN controls end in UB.
- T2 census unchanged (197 proved, 1 refuted = 254, 311 timeout incl. 132 and 566). Model spend $3.26 / 12 calls (first pass
  $1.83 out of budget, final $1.43). Producer hash prefixes in its message were wrong; real ones in the check SUMMARY.
- Paper: sec-thrift T2 paragraph (re-check sentences), appendix versions and replay table row.

## R6b: es-toolkit audit re-run with StrictTS 43132a8 (labelled, not pre-registered; checks/r6b-20261027T0150Z; fork; written 2026-10-27T02:39Z; SUMMARY.md 014cde07...)
- Delivery StrictTS d3208a8: R6B_RESULTS.md 884e0b87, r6b_table.tsv 0b7167cb, R6B_EVIDENCE_SHA256SUMS 7019a187 (1,180/1,180 OK).
  Inputs = the frozen 415/79 lists (cmp). Tool changes 10ec829 -> 43132a8: loose == / != against null accepted and lowered;
  DynNullish lemmas; ts_destruct splits optionals/unions; compat wrapper calls a widened new version through the old types.
- Counts (table and, independently, the 415 chunk records): PROVED 54 (51 all-worlds, 3 allocated-arguments; 25 at one
  instance), REFUTED Lean-confirmed 10, Node only 76, UNKNOWN 275. Changes from R6: 8 UNKNOWN -> PROVED (isNil x2, isNotNil x2,
  isArrayLike x2, endsWith, startsWith) and toString Node-only -> Lean-confirmed; the 86 refutations and replays byte-identical
  to R6 (erratum split 76/10 unchanged). All 9 changes are outside the frozen 79-pair list (excluded by the no-loose-eq rule);
  on the 79 nothing changed.
- 54/54 re-elaborated at 43132a8, exactly the standard axioms, no error/sorry in their blocks; kernel replay 15 proof modules +
  48-module StrictTS closure = 63, all rc 0; negative control rejected. 86/86 node replays, 10/10 Lean confirmations reproduce.
  Regressions at the exact commit: corpus 181/0/0, selftest pass, bench 43/44 + 23/23, 0 wrong.
- Qualifications: endsWith/startsWith proved only on the OLD parameter types (compat wrapper), not marked in the table; the 3 new
  fix-commit proofs (isNotNil, endsWith, startsWith) change code, not only types. Evidence gap: the toString, trimEnd and
  trimStart confirmation files are not in the R6b manifest (re-run from copies; asked StrictTS to freeze them).
- Cost: 0.837 core-h run + replays + recheck by guard logs (+0.484 development); $33.58 tokens reported, not checked.

## R6b addendum (StrictTS dd93572; R6B_ADDENDUM_20261027.md a849d147; verified by the evidence owner 2026-10-27T02:41Z)
- R6B_ADDENDUM_SHA256SUMS b7fc0a98: 22/22 OK in scratch/r6b; the toString, trimEnd and trimStart confirmation files in it
  (evidence_confirm/) equal the copies my checker re-ran (2a00ad63, 0065e9ba, 8e2681db). r6b_table_v2.tsv d19256bf adds a domain
  column: PROVED 54 = 52 full domain (49 all-worlds + 3 allocated-arguments) + 2 on the old parameter types (endsWith,
  startsWith); otherwise as r6b_table.tsv. The evidence gap of checks/r6b-20261027T0150Z is closed.

## T3 decision-B run of the 12 flagged verdicts at cirlean e6ac99a (labelled; checks/t3sp-20261027T0244Z; fork; written 2026-10-27T03:06Z; SUMMARY.md 66494608...)
- veriforch package runs/postfreeze/t3_shared_ptr_e6ac99a (SHA256SUMS 820ff672, 3,146/3,146 OK before and after); equiv-lean
  5ec2642-cirfrz (13 EquivLean modules in the closures source-identical to b171660).
- All 12 hold: verdict modules byte-identical to the T3 certificates up to the namespace rename; 24 Gen + 3 VerifOrch modules
  identical (no hypothesis changed); 24/24 theorems print exactly the standard axioms; closures 95 modules, kernel replay rc 0;
  controls as expected.
- Condition unchanged: at e6ac99a the punning check covers array elements, not record members; the 64-bit load over the two
  32-bit counter members still reads one element (probe: native 4294967297 for counts (1,1), 1 on both pins); cirpun output
  byte-identical to T3. The 12 verdicts stay conditional; the paper sentence that the later version treats the access as
  undefined was wrong for this access and is corrected.
- Producer: no model calls, 0.173 core-h. Discrepancies: producer replay log covers only the 12 verdict modules; 48 of 100
  guarded compiles exited 1 before the final pass without kept logs; the equiv-lean freeze directory received 328 new build
  files 02:45-02:53Z (none used by the verdicts).
- T3 decision-B note (2026-10-27T03:18Z): equiv-lean traced the 328 writes in its pin tree (02:45:27-02:53:19Z) to its own kit build calls c128-c136, still running when the tree was used and copied (636/660 when stopped at 03:08Z); read-only since 03:12Z. No file used by the 12 verdicts changed (checks/t3sp-20261027T0244Z).

## R6r: remeda refactoring study (StrictTS, labelled, not pre-registered; checks/r6r-20261027T0333Z; fork; written 2026-10-27T04:05Z; SUMMARY.md 4fc429e8...)
- Delivery: master 7907c5f, R6R_RESULTS.md de746d59; manifest R6R_EVIDENCE_SHA256SUMS a95639c9 (1,902/1,902); lists equal the
  addendum (prereg/ADDENDUM_R6r_remeda_inputs.md e19195aa); pair files 7,124/7,124; run on bbe90b4 = tool code 2ea47b8, dist dbe5a9c2.
- Counts (table and chunk records, 862/862): PROVED 54 (all-worlds; 35 at one instance; 7 test-file helpers), REFUTED 9
  Lean-confirmed + 55 Node only, UNKNOWN 744; provable 160 = 54/9/2/95, of which 81 have no translated target (const arrows
  nothing references; topFunDecl; probe re-run); es-toolkit R6/R6b: 1 of the 79 (startsWith 4c285773, UNKNOWN).
- 54/54 re-elaborated with exactly the standard axioms; kernel replay 18 proof modules + 48 StrictTS modules rc 0; controls;
  64/64 node replays; 9 Lean confirmations + 2 blocks with reasons; tscheck 27 both (24 internal, 3 exported) / 36 neither /
  1 new only; refactor/style/chore 27 PROVED, 3 refuted (zipWith() invalid in both; func1/func2 test helpers).
- Producer 1.13 core-h (guard logs); $26.27 tokens reported, not checked. Notes: StrictTS listing of the 24 internal calls
  incomplete (count right); 25 git objects appeared in ~/strictts at 03:49:11Z (HEAD unchanged; not from the check).
- Paper: sec-fixes remeda paragraph; intro clause; appendix versions, addenda sentence, replay row (66 modules).

## Scan coverage completed (checks/scancov-20261027T0424Z; fork; written 2026-10-27T04:31Z; SUMMARY.md 9737e7dc...)
- Coverage table of all claimed C/C++ theorem sets: three had neither the punning scan nor the memcpy check (T4 C++ side,
  T2 re-check at e6ac99a, musl refinements); scanned now with cirpun f365f63 (controls pass) and the memcpy-site check.
- T4 C++: 38 functions, 13 flags (6 unresolved TTransport virtual calls = contract hypotheses / vtProto; 1 u8 read of the
  borrowed buffer typed by ReadContract.borrow); no access of another width; no memcpy. T2 re-check: no flags, no memcpy.
- musl strlen: u64 loads over the char array in the word loop on covered paths (no hypothesis excludes the loop; module doc
  relies on the one-element reading) -> a second access of another width; musl memcpy word paths excluded by WordFree.
- Paper: sec-limits now says two accesses (shared_ptr counters; musl strlen word loop), T4 transport flags are hypotheses;
  sec-trust says the strlen refinement holds only for the one-element reading of its word loop; memcpy sentence restored.

## T4 Java nibbles 14/15 (equiv-lean a9c8e23, labelled; checks/t4nib-20261027T0520Z; fork; written 2026-10-27T05:48Z; SUMMARY.md d8f99596...)
- Manifest 56c59628 4238/4238 before and after; 2420 tracked files = a9c8e23; vs d35b1e4 only the 10 new Term/*All*.lean files +
  README/HANDOFF; vs 613c77c no existing Lean file changed.
- Statements (fresh #check; premises as R7: Contains, Valid env, NoRedecl, TransportTerm, TRepConc): gttAll_total (getTType total;
  returns the nibble's TType, throws TProtocolException only for nibbles 14 and 15); rfb/rlb/rsbAll_total (header reads total on
  every header byte); *_nib1415_total (a header with nibble 14/15 terminates and every run throws); *_nib1415_spec_total (our
  specification reads such a header as type 14/15 while Java terminates and throws; agrees with checks/t4nib-native-20261027).
- 10/10 modules compile; 108 rows exactly the standard axioms (thrift_classes_length none); kernel replay 111 modules: 72 replayed
  rc 0, 39 reused from the R7 check (byte-identical); controls. Producer 10.698 core-h (whole rebuild; new modules 578.5 s).
- Paper: T4 paragraph, after the checkpoint (spec-vs-Java difference, not a Thrift defect).

## coblean combined snapshot coblean-20261027T0518Z (intrinsic functions + PERFORM VARYING AFTER/alphanumeric-edited + DECLARATIVES; checks/cob0518-20261027T0520Z; fork; written 2026-10-27T06:10Z; SUMMARY.md 69e3d833...)
- Manifest 1c63b866 316/316 before and after; source changes since 0050Z = the three merges. TH0 from source (115 jobs): 25 axiom
  lines and 25 statement hashes = 2306Z. Nine CardDemo IRs byte-identical (2306Z, 0050Z); 15 oleans changed vs 2306Z, 13 vs 0050Z;
  Cobol.olean be3132eb. 91/91 rows match (incl. 7 changed, 12 new, IRFE x9). Controls as coblean reports (intrinsic planted errors
  re-created: 59/28/11 vs 59/33/11). NIST DECLARATIVES: 39 pass, 4 unsupported (other statements), program for program.
- Paper: sec-limits NIST paragraph (declaratives modelled in the latest version; 39 of 43 pass; USE GLOBAL rejected); appendix
  versions. Migration theorems stay at 2306Z.

## R6c and R6rb: third StrictTS tool version (const-arrow 9e54bdb; labelled; checks/r6c-20261027T0601Z; fork; written 2026-10-27T06:38Z; SUMMARY.md 1d653f43...)
- Inputs prereg/ADDENDUM_R6c_R6rb_inputs.md (6ecf67c4, 04:10:31Z, before both runs). R6c (es-toolkit 415): PROVED 60 (57 + 3 allocated;
  25 one-instance; 7 on old parameter types), REFUTED 10 + 76, UNKNOWN 269; exactly 6 changes vs R6b (first looks, disclosed);
  provable 52/79; no pair without target. R6rb (remeda 862): PROVED 59 (35 one-instance), REFUTED 9 + 55, UNKNOWN 739; exactly 5
  changes vs R6r (former no-target pairs); the 81 former no-target pairs = 5 / 75 outside the subset / 1 differing signatures.
- 60/60 and 59/59 exactly standard axioms; kernel replay 35 proof modules + 49-module StrictTS closure (DynOpt added) rc 0;
  refutation files byte-identical to R6b/R6r; compat-wrapper proofs cover one-argument calls of the old type only.
- Producer 0.861 / 0.917 core-h. Minor: results file 8716145 had a wrong table hash (fixed at 0f1e6b8 = delivered 28244e08);
  heartbeat-timeout axiom lines vary between runs (not PROVED theorems).
- Paper: sec-fixes paragraph after remeda; appendix versions, addenda sentence, replay row (84 modules).

## Prune of derived build artifacts in verified replay copies (written 2026-10-27T08:53Z)
- Only *.olean, *.ilean and .lake/build intermediates (c/trace/hash/o/json) deleted, files only, from 11 verified copies (t2, eqledger,
  eqt4jt, eqt4, t3, eqjt, t3sp, cob0050, vo-2, vo-Dl3h, vo-Dl3r2); sources, tables, logs and all other files kept; copies t4nib and
  cob0518 kept whole for later delta replays. In-use guard (process cwd/fd snapshot) before each delete pass; manifests per copy
  (size, link count, path) in /home/user/fv_paper/evidence/prune/prune_20261027T0840Z_run (an earlier attempt, prune_20261027T0837Z_run, was stopped by the g1 cap after 2,784 t2 files;
  those are listed in its manifest). Root free 939,070 MB -> 1,004,066 MB (about 65 GB; hard-linked files freed nothing). The
  checks' recorded hashes of these build files remain in their check directories.

## R6d: third later StrictTS version (master 25790c3; labelled; checks/r6d-20261027T0825Z; fork; written 2026-10-27T09:04Z; SUMMARY.md 50228440...)
- Inputs prereg/ADDENDUM_R6d_inputs.md (7c9230e1, 07:02:26Z, before the run). es-toolkit: 64 equivalences (60 + 4 allocated; 28
  one-instance; 9 compat wrapper, 1 return wrapper), 1 old-no-panic (not an equivalence), 10 + 76 refuted, 264 unknown. remeda: 60
  (36 one-instance), 2 old-no-panic, 9 + 55, 736. Changes vs R6c/R6rb: 5 and 3, all disclosed first looks. 65/65 and 62/62 theorems
  exactly standard axioms; kernel replay 38 proof modules + 49 closure rc 0; refutation files byte-identical. Table label note: the
  table's cat column calls the np pairs "PROVED (old-no-panic)"; counted apart in the paper (asked StrictTS to relabel).
- Paper: sec-fixes consolidated "three later versions" paragraph (replacing the R6b and R6c paragraphs) + remeda later-versions
  sentences; intro sentence; appendix versions, addenda, replay row (87 modules).

## zlib Adler-32 C -> safe Rust (equiv-lean ff07aac; labelled, scope frozen in DEVIATIONS 01:14Z; checks/adler32-20261027T0854Z; fork; written 2026-10-27T09:24Z; SUMMARY.md 262b9f6b...)
- Manifest 1b21658d 4269/4269 before and after; tracked 2444 = ff07aac; vs 9b15933: 34 added files + README (all adler32); 15 shared
  closure modules = 751764f sources. 17 new modules compile; 25 adler32 rows exactly standard axioms (adler32_combine__spec incl.).
- Statements: adler32_z/adler32 explicit forms: every adler, every buffer < 2^28 bytes (or Z_NULL, len < 2^28, len != 1): C returns
  without UB, Rust never panics, values equal; _equiv forms = frozen EquivOn form; combine/combine64: all inputs, both total. C run
  from the initial memory with the buffer as exactly len read-only bytes. Scope = the frozen entry.
- Kernel replay closure 323: 28 replayed rc 0, 295 reused (R5 check); controls. C files = the pre-registration's zlib 1.3.1 copy;
  ClangIR and Aeneas regenerate; cirpun clean; difftest reproduces; lines 157/837/825/117. Model-vs-gcc test not re-run; $165 not
  checked. Paper: sec-migration paragraph, intro sentence, appendix version and replay row.

## Whole cJSON harness theorem re-verified at cirlean e6ac99a (labelled; checks/r1next-20261027T0909Z; fork; written 2026-10-27T09:50Z; SUMMARY.md d8e66cc7...)
- Package r1_cjson_e6ac99a SHA256SUMS b8eeb5c6 492/492 before and after; 285 module hashes = RESOLUTION.tsv; 44 CIR modules = the frozen
  pin manifest (825e6dc0). Entry statement (#check with InitExt, ReadableBuf, Returns) byte-identical to the c4ef58d check; 32 unit
  theorems + FHEntry.entry_main exactly standard axioms; 285/285 modules replay rc 0; leanchecker --fresh on the entry rc 0; controls.
- 8 of 32 unit statements restated (Delete forestPrintable; New_Item hpun; skip_whitespace/parse_string/parse_hex4/utf16 typed byte
  buffers; print_number/print_string item block of record type cJSON; CJ.printable rt); all discharged inside the composition.
- Paper: sec-ub sentence (via an agent), appendix version and replay row. R1 at c4ef58d stays the primary statement.

## R6e: fourth later StrictTS version (master 4016a4a; labelled; checks/r6e-20261027T1138Z; fork; written 2026-10-27T12:13Z; SUMMARY.md fe54d4d3...)
- Inputs prereg/ADDENDUM_R6e_inputs.md (5e826840, 10:26:03Z, before the run). es-toolkit 70 equivalences (67 + 3 allocated; 28
  one-instance; 11 compat, 1 return wrapper), 1 old-no-panic, 10 + 76, 258; remeda 61 (37 one-instance), 2 old-no-panic, 9 + 55, 735.
  Changes vs R6d: 7 es (6 new proofs, xor extended; all first looks) + 1 remeda (doesNothing; classification from the rescan).
  71/71 and 63/63 standard axioms; replay 40 + 50 modules rc 0; typeof lemma proved; refutations identical. Producer 1.862 core-h.
- Paper: later-versions paragraph now four versions (54/60/64/70; remeda 59/60/61); intro counts 70/61; appendix versions,
  addenda, replay row (90 modules).

## CBSTM03A with CBSTM03B: all-input theorems (coblean; labelled; checks/stm03ab-20261027T1252Z; fork; written 2026-10-27T13:13Z; SUMMARY.md a0e236bb...)
- Snapshot pin2306Z-cbstm03ab-20261027T1251Z = 2306Z + StmCore; 43 Cobol oleans = 2306Z; linked IR regenerates byte for byte and
  equals 2306Z's; 28 new modules compile; four theorems exactly standard axioms; replay 71/71 rc 0; controls.
- stm_run_sorted: fixed address-space model (job, step, 9 DDs), OPENs succeed, 178,495-byte storage with PSAPTR null, TRNX nonempty
  valid 350-byte records sorted by card, <= 50 groups of <= 10 (program tables), XOk cross-reference records, fuel bound -> GOBACK,
  output = events + 11 walk lines, STMT/HTML by functional models, files closed. stm_run: without sortedness. Abort theorems:
  Fault.abend (-1) = no user code. V.stm differential AGREE 1212/6082; the 11 skipped DISPLAYs = the walk lines.
- Paper: sec-migration paragraph (every covered batch program has an all-input COBOL theorem); appendix version and replay row.

## es-toolkit difference and intersection, relational proofs (equiv-lean ts-esdiff 92f75e6; labelled; checks/esdiff-20261027T1415Z; fork; written 2026-10-27T14:24Z; SUMMARY.md 91695645...)
- Manifest 8496421f 4240/4240; tracked = 92f75e6; StrictTS pin a15926a checked separately. difference_equiv / intersection_equiv:
  every Impl, world, two number-array cells below w.next (aliasing allowed, no length bound): Equiv (ArrObs w.next) old new (console,
  heap cells below w.next, oracle indices, results; not the fresh Set, addresses, next, jobs/timers/clock); T := number via inst.ts.
  Slices = frozen R6 pairs; Gen files regenerate; exactly standard axioms; replay 35 modules rc 0; controls.
- Paper: sec-fixes paragraph after the later-versions paragraph; appendix version and replay row.

## CBSTM03B translations, Rust and Java (R4; equiv-lean cc9e349 partial + 0fd209e total; labelled; checks/r4-20261027T1248Z; fork; written 2026-10-27T14:33Z; SUMMARY.md cb34e75f...)
- Kits 4359/4359 and 4391/4391 before and after; tracked = commits; delta = 16 Java/Term modules + JavaRun + README. Rust.rust Equiv;
  Java.java Sim (partial); java_terminates (runSpec.pre -> every run terminates); java_total (an outcome exists, every outcome a
  normal return with the model's state). Hypotheses: c < 100, digit-only ACCT keys, NotRecOf/SepM (Java), + generated: 11 class-init
  premises, JVM bounds < 2^31, valid fields, key length 1..25, COBOL fuel 50 (not in the producer's announced list).
- Sources = veriforch finals (Rust v4, Java v1 of the first guide); Aeneas, Jimple, 22 statements regenerate; 19/19 and 21/21 rows std;
  replay 411/411 + 17 rc 0; records 60/60 + 300/300. Check slip: 3-4 parallel Lean jobs for 1,179 s (limit 2), guarded, no cap hit.
- Paper: sec-migration paragraph; appendix versions and replay row.

## V: labelled re-run of the LLVM sample at cirlean e6ac99a (checks/Vnext-20261027; an agent; written 2026-10-27T16:40Z; SHA256SUMS 2ffced77...)
- Inputs prereg/V/ADDENDUM_V_rerun_e6ac99a.md (72c9ff4e, 16:11:16Z; run started 16:11:46Z). Runner v8 d21f1ef2 = v7 + cirrun path +
  docstring + default stop (diff checked); cirrun 232b7a0d; environment and clang/gcc hashes as crash-fix round 2.
- runV_next_e6ac99a: SHA256SUMS 0aa52603, 3443/3443 OK; results.tsv e8f4129c, 200 rows = sample_V (d0f38820). Against runV (ac02a5a3):
  exactly 3 kind changes: order 31 inf-1 MISMATCH -> MATCH (NATIVE_OK; hex FP +inf constant; fix af0c0d4, ancestor of e6ac99a, not
  of ffab71e); orders 43/84 CRASH -> TIMEOUT = the crash-fix-2 rows (18bfdfce). native columns identical on all 200 rows.
- Counts at e6ac99a in the 177: 96 same status (54.2%, Wilson 46.9-61.4), 2 different, 25 UB, 31 outside, 13 exit, 10 timeout;
  96/123 = 78.0% (69.9-84.5); Wilson control reproduces 46.3-60.9 and 69.1-83.8. Core-h 0.411 outer (cap 1.5) + 0.040 smoke.
- Paper: sec-stack V paragraph (labelled sentence), appendix versions item and addenda sentence.

## Referee evidence (written 2026-10-27T17:19Z)
- Numeric items (an agent; checks/refnums-20261027T170719Z, SHA256SUMS 5 files): tab:sample statement kinds from the
  frozen results.jsonl outcome field (mechanical only for es-toolkit: 3/8/6 of 3/9/9; all other 166 proofs model-stated);
  interface-only blocked 1 of 31 (lang3 held-out after the bridge-fix re-run); Table 4 overlap (Java 786, shared 3,115 lines
  counted per program; 1,233 statement lines in eProofLines); replay-table conventions; remeda copy d57b59f vs run bbe90b4;
  costgaps cites T2 not tab:thrift; "42 Java theorems" = T4 E/D/M; T3 language counts 153 = 150 + 3 two-language commits;
  m4 not supported (both cite CBTRN03C); CBTRN02C 10^9 implied by the bound; proved runs = seed-1 final of each guide;
  proved CBACT04C Rust run is the excluded one; 52 repair steps, 50 cause labels.
- C++ difftest at the theorem pins (producer the C maintainer session; my check): dt_pins b45fcd2b (351/351), dt_pins2 c5a86341 (141/141): 174
  MATCH + 1 UB at 28e2380 (clean build, cirrun aa564f01), 266d1ed (d12dee10), c4ef58d (3cfd076e), ffab71e (01e5df80),
  e6ac99a (232b7a0d); case lines identical (0fc432e9).
- JVM suite at 1728Z, 2312Z, 2035Z (producer the Java maintainer session; my check): dtver/run_20261027T1708Z results.tsv d47412c6, 123/123 agree.
- C-side regeneration with clean cir2lean builds (an agent; checks/cir2lean-20261027T171248Z, 18 files): TRX, jsmn,
  Adler-32, musl, cJSON harness (266d1ed) byte-identical up to the header input-path comment (harness Gen 128/128 incl.
  headers); originals used 12d2c1ba binaries, never the leftover 913d792b.
- coblean package kernel replay (an agent; checks/cobreplay-20261027T1705Z, SHA256SUMS 0840bec4): 68/68 rc 0 (43
  library modules also inside the 924; 25 program-theorem modules); BadCtl rc 1, GoodCtl rc 0; 0.25 core-h.
- Java total correctness notion (the Java maintainer session): MTerm (every execution terminates, any nondeterministic choice, one exists);
  soundness theorem Jimple.TermVC.mterm (Termination.lean at 2312Z); T4 totals also prove MTerm per method.

## Re-pin of equiv-lean at cirlean e6ac99a + JimpleLean 2035Z (int-trial 7e7f28d; labelled; checks/repin-20261027T1552Z; an agent; written 2026-10-27T17:36Z; SUMMARY.md cfc006f3...)
- Kit 7e7f28d-replay2 manifest 4236/4236 before/after and in the cp -rL copy; 2419 tracked files = 7e7f28d; vendored cirlean =
  frozen e6ac99a sources (40/43 oleans equal; CJTree, Loops, Simprocs differ in bytes, replay rc 0); JimpleLean = 2035Z
  (146/146; vs 2312Z: TermSplitX = renamed Term/TermX, one lemma, a tactic change; no semantic definitions change).
- Byte-identical printed statements: re_match_equiv (+12 definitions), jsmn_equiv and 3 C rows, 9 Thrift C++ rows, T4 Java
  totals, nibble totals; C runs now evaluated under e6ac99a. Restated exactly as RESTATEMENTS.md (0af3d22a): TRX
  re_compile_spec, re_matchp_pspec, MPC +1 char-array premise; musl strlen_pspec/strlen_refines +1, memcpy_pspec +2;
  memcpy_cex_run -> memcpy_cex_ub (7-byte run has no outcome; was 1 2 3 4 0 0 0); strlen_aligned_ub new (char array, start
  index i with (i+1)%8=0 -> no outcome).
- Axioms 108/109 standard + 1 none (thrift_classes_length); Popcount bv_decide theorems outside every row's closure. Kernel
  replay 1,751 modules: 1,399 replayed rc 0 + 352 reused (byte-identical closures from t4nib/eqr5/eqT copies); controls ok.
- Checker slips: three hash steps and three one-line JSON reads ran without the core-hour guard (each < 20 s); 1.816 core-h
  metered.
- Paper: sec-trust musl sentences, sec-limits re-pin sentence, appendix versions item and replay row.

## Prune of derived build files in t4nib, adler32, r4 copies (written 2026-10-27T17:42Z)
- Same script as 08:40Z with a new allowlist (job tmp prune_derived_v2.sh; dry prune_20261027T1737Z_dry, run
  prune_20261027T1738Z_run with manifests): only *.olean, *.ilean and .lake/build intermediates, files only, in-use guard.
- Most of these copies are read-only (frozen by their checks), so rm removed only the files in writable directories: t4nib
  5,941 of 120,415, adler32 5,716 of 120,476, r4 6,346 of 236,066 (rest "Permission denied"). Root free 1,055.50 GB ->
  1,056.78 GB. The frozen copies were not unfrozen; whole-copy archiving or deletion stays with the user.

## Java termination theorems (an agent; checks/mterm-20261027T175220Z, SUMMARY.md 3fa7c000...; written 2026-10-27T18:00Z)
- TermVC.mterm: Valid P G -> callees ContractTerm -> TermVC -> forall args s0, pre -> MTerm; total_of_sat_mterm: Sat -> (pre -> MTerm) -> (exists o, MExec) and forall o, MExec -> post.
- Migration 8/8 run_term = pre -> MTerm; run_total = total_of_sat_mterm run_sat run_term. T4 68/68 totals apply the same method MTerm theorem under their own hypotheses (66 via the 22 *_term rows, wcb_total/wcb_E_total via wcb_termI). Paper: sec-migration termination paragraph, sec-thrift T4 totals sentence.

## coblean snapshot 20261027T1730Z (labelled; checks/cob1730-20261027T1734Z; an agent; written 2026-10-27T18:08Z; SHA256SUMS 3a0443a9)
- Files 12/12; manifest 6f20c167 365/365 in snapshot and cp -rL copy before/after; snapshot vs live = HANDOFF only.
- Source changes 0518Z -> 1730Z = the five declared (INITIALIZE (a) reference-modified and (b) own REDEFINES, SELECT OPTIONAL
  with status 05 and --absent, front-end items, USAGE INDEX / PERFORM VARYING index names, POINTER lowering); README documents
  each; junk tools/cobolfe/0 declared.
- TH0 from source (1 CPU, 1,628 s): 115 jobs, 24 standard + bincnt_equiv bv_decide = 0518Z; 25 TH*.st = 2306Z. Oleans: 15 vs
  2306Z (same set as 0518Z), 7 vs 0518Z, Cobol.olean be3132eb. Ten CardDemo IRs byte-identical (CBSTM03B 38fa862f).
- 503-program front-end identity: 492 identical, 11 changed, all USAGE INDEX / index names; none from the POINTER fix; no
  CardDemo change. TSV 34223c3f vs 0518Z: 203 identical, 5 value changes, 21 new; 61/61 re-run rows match.
- NIST: NC131A, NC133A, NC135A, NC206A, NC236A, NC241A, NC243A pass; IC106A, IC207A unsupported; IX217A, IX218A, NC211A pass;
  SQ203A passes with its producer SQ202A. INITIALIZE defects fixed: V.init.s1/s2, V.irchk, V.initptr.s1/s2, V.ptrchk.
- Paper: sec-limits INITIALIZE/SELECT OPTIONAL/USAGE INDEX/departures; sec-stack NIST status-05 clause; appendix snapshot.

## COBOL testers in the IBM variant (labelled; checks/ibmvar-20261027T181928Z; an agent; written 2026-10-27T18:23Z; SUMMARY.md eaed1cec)
- Plan prereg/ADDENDUM_IBMVAR_coblean.md (3853d1b4, 17:28:15Z); pre-run list baff99bb (DEVIATIONS 18:02:00Z); every run
  started 18:05:04Z or later. Seal 9e029500 221/221 (0 writable); runs 7777/7777.
- Testers = 2306Z files; runner 8625598f (v2 036f12db, one line, ctrltest only); table a99f6bfb = coblean cp037.
- 964 programs: 953 agree (4 ok-negzero, 7 ok-abend, 4 hv ok-hvbyte, 120 rawref ok from the receiver name R), 11 declined
  (PERFORM recursion/resume), 0 mismatch. CTL-A caught the 23 embedded-sign programs exactly; CTL-B (4 runs) and CTL-C (17
  runs) 0 missed, 0 extra. E1: IBM IR = cbstm03ab.ir.json (2c5ba72b); 1,212 + 6,082 records agree.
- Probes: GnuCOBOL prints a separate sign under all four flag sets (7 DISPSIGN operands untested as DISPLAY output);
  indexed keys in native order under EBCDIC flags (key order untested). Untested per program as listed. 0.051 core-h.
- Paper: sec-limits validation paragraph; abstract, intro, stack and conclusion caveats; appendix addenda sentence.

## M2: C mutation follow-up with the extended difftest suite (labelled; checks/m2-20261027T185803Z; an agent; written 2026-10-27T19:04Z; SUMMARY.md 0e179280)
- Addendum bf94540c (17:13:59Z), plan v2 67f301ef; blinding record 8649f149 (DEVIATIONS). Seal 05e0eb6a 808/808 (hash list).
- Suite = 175 original + 238 defined new cases (ub_* excluded); baseline rows 1-175 = M; new part 157 MATCH, 4 MISMATCH, 77 UB.
- M2a: 30/30 reproduce M (build, sorried, mutated sha, verdict); kills 7 -> 17 (10 new-only: 8 Float.lean, 2 Eval.lean);
  9 and 19 survive. M2b: orders 35-67, stillborn 41/56/59; kills 10 -> 24 (14 new-only, all Float.lean); order 37 = RSS
  watchdog (24.1 GiB, unmutated 0.32 s; same watchdog as M, never triggered there): 23/30 without it.
- Wilson: 7/30 .118-.409, 17/30 .392-.726, 10/30 .192-.512, 24/30 .627-.905, 23/30 .591-.882. Controls ok; ~2.30 core-h.
- Baseline classes (da9fec4c): ffab71e 157 pass / 43 missing model / 30 format or subset / 4 unsupported / 3 documented limit /
  1 wrong value; e6ac99a 158/43/30/1/6/0; 3 of 18 ub_* MATCH at both (# flag with %d, precision with %c, sprintf into itself).
- Paper: sec-stack mutation paragraph (C follow-up), sec-limits library-model sentences, tab:trust C row, appendix addenda.

## R6f es-toolkit = L5 (StrictTS 4bef3c4; labelled; checks/r6f-20261027T1859Z; an agent; written 2026-10-27T19:31Z; SUMMARY.md d2dda924)
- Inputs prereg/ADDENDUM_R6f_inputs.md (4e3af7f3, 16:39:14Z; run 16:39:55Z, HEAD 4bef3c48). EVIDENCE 2292/2292; lists and pair
  sums = addendum; copy tracked files = 4bef3c4 (1057/1057); dist frontend be5d20e4, difftool 86fe40d6.
- PROVED 98 (94 all-worlds, 4 allocated), OLD-NO-PANIC 1 (own column), REFUTED 12 Lean + 74 Node, UNKNOWN 230; by type 28/50/20.
  vs R6e: exactly 30 changes (27 UNKNOWN -> PROVED all-worlds; compact -> allocated; fill, compareValues -> Lean-confirmed);
  28/28 new PROVED tried before the run; all 77 first-looked pairs equal their last first look; difference and intersection
  stay UNKNOWN.
- Restrictions among the 98: inst 39, allocated 4, compat wrapper 13, return wrapper 2, extern 6 (statements for every Impl
  and world; the 6 already proved under L4). 99/99 theorems std; 29 derived proof modules + 50 StrictTS closure leanchecker
  rc 0; BadCtl rc 1, GoodCtl rc 0. Refutations 86/86 (spot check 10 in node). Producer 1.923 core-h (es); check 0.457.
- Checker slip: the fork removed two of its own temporary files in its check dir with rm -f, against the brief.
- Paper: sec-fixes later-versions paragraph (L1-L5, es-toolkit), intro sentence (98 for es-toolkit), appendix versions,
  addenda (16:39, 4e3af7f3) and replay row. remeda part of R6f pending.

## Composite theorems (equiv-lean ba05f6e / 89806a8; checks/composite-20261027T190730Z; an agent; written 2026-10-27T20:05Z; SUMMARY.md d6eadcc5)
- Each commit adds only Composite.lean (24cd6e12) and CompositeRestricted.lean (de06bcf9), identical on both branches; compiled
  in a copy of the 0fd209e kit, oleans byte-identical to the producer's.
- 21/21 statements: the generated Statement's binders (defeq, in order) and conclusion Safe c and (Rust, 11) the run returns
  .ok and Equiv, or (Java, 10) MTerm, (exists execution and every execution meets post), Sim. 21/21 exactly std axioms.
- Closure 1,204 modules: 868 replayed rc 0 (incl. the 17 AeneasMeta modules, which no earlier closure followed) + 336 reused
  from repin; BadCtl rc 1, GoodCtl rc 0; 1.0 core-h. AeneasMeta oleans byte-identical in the composite, repin and
  eq-20261025T1449Z copies (pruned in the adler32 and r4 copies).
- Paper: intro, example, CBSTM03B paragraph, trust (axioms, replay, AeneasMeta), appendix versions and replay row.

## V: labelled re-run at cirlean next2 424e821 (checks/Vnext2-20261027T201054Z; an agent; written 2026-10-27T20:13Z; SUMMARY.md 76366241)
- Addendum ed2f75df (19:42:51Z; run 19:43:07Z); runner v9 7b85c170 (diff vs v8: docstring, CIRRUN, stop); cirrun 85da63b4.
- Seal 8e60b781 3444/3444; results 813c52b6, 200 rows = sample. vs e6ac99a 36 changed rows (31 kind changes as declared, 5 new
  reasons); vs runV 39; native identical; no CRASH/oom rows.
- 177 natively OK: 121 same (68.4%, 61.2-74.8), 1 different (widechar-3), 26 UB, 17 outside, 0 exit, 12 timeout; 121/148 =
  81.8% (74.8-87.1). New UB: 131 pr47925, 144 pr88739 (indeterminate or ill-typed read), 173 2003-05-07-VarArgs (va_arg of
  another type), native OK, sanitizers silent, untriaged. 0.511 + 0.071 core-h.
- Paper: sec-stack V paragraph (labelled sentence), appendix versions and addenda.

## CSUTLDTC all-input theorem (labelled; checks/csutl-20261027T201400Z; an agent; written 2026-10-27T20:20Z; SUMMARY.md 8859d5e4)
- Pin coblean-pinM3-csutldtc-20261027T2010Z SUMS 3e7d6fbc 992/992; vs snapshot 2008Z only Examples/Csutl, the IR, lakefile
  (3915e28c), progress, SUMS; 43 Cobol oleans = 2008Z (be3132eb root).
- IR from the unmodified CSUTLDTC.cbl (58c165dc) = b38f9a39 (stored). csutldtc_every: env arbitrary (every CEEDAYS behaviour),
  m.size = 714, fuel 10; no CEEDAYS hypothesis; branches: no answer -> fault; valid 258/258/4/12 results -> EXIT PROGRAM, one call
  event, LS-RESULT and RETURN-CODE exact, all 714 bytes given; else invalidData, range or bad-result faults. Corollary
  csutldtc_result premises (a) vstrings unchanged, (b) fillers, (c) valid halfwords; fillers_init, fillers_kept.
- 4/4 std; scan clean; 47/47 modules leanchecker rc 0 (nothing reused); controls ok; run_mono (larger fuel, same result).
- Paper: sec-migration CBSTM03 subsection (11 of 14 batch programs, labelled), appendix versions and replay row. Snapshot 2008Z
  re-check (an agent) still running.

## coblean snapshot 20261027T2008Z, merge 3 (labelled; checks/cob2008-20261027T2011Z; an agent; written 2026-10-27T20:44Z; SUMMARY.md 3343289f)
- Files 14/14; manifest a59e8b4b 406/406 before/after; snapshot vs live = HANDOFF only.
- Source changes 1730Z -> 2008Z: Lean semantics only collate constructs (IR, Sem/Arith, Sem/Data, Sem/Exec); ODO front end only
  (Layout, Sem/File unchanged); cleanups and README E1-E3 as declared; no undeclared change.
- TH0 from source 115 jobs, 25 axiom lines = 1730Z/0518Z, TH*.st = 2306Z; oleans 13/14/17 changed vs 1730Z/0518Z/2306Z,
  Cobol.olean be3132eb; 9 stored IRs = 2306Z, regenerated byte-identical; identity 31 changed (20 collating, 11 ODO).
- TSV 4c670769: 218 same, 11 differ, 8 new; 54/54 re-run rows match. NIST: 12 programs to pass. CSUTLDTC IR b38f9a39.
  link.py exposure scan reproduced byte for byte (17cf69eb): no linked program declares a collating sequence.
- Paper: sec-limits later-version sentences (collating, ODO, departures, linker defect), appendix snapshot list.

## R6f remeda = L5 (labelled; checks/r6fre-20261027T2032Z; an agent; written 2026-10-27T21:03Z; SUMMARY.md 2806a495)
- EVIDENCE 1942/1942; inputs = addendum; deviation files r6_testable/r6_provable in re/ = R6e's r7 lists (fec09171, 14c45704).
- PROVED 117 (all-worlds; inst 93, compat 4, return 1, extern 0; 21 outside the frozen 160), OLD-NO-PANIC 2, REFUTED 11 + 53,
  UNKNOWN 679; vs R6e exactly 58 changes (56 UNKNOWN -> PROVED; isEmpty, chunkImplementation -> Lean-confirmed); 56/56 tried
  before the run; all 78 first-looked pairs equal their last first look.
- 119/119 theorems std; 32 derived modules leanchecker rc 0; StrictTS closure reused (byte-identical, replayed in the es
  check); controls ok; 64/64 node replays; producer remeda 1.421, R6f total 3.345 core-h; check 0.511.
- Correction to the addendum (4e3af7f3): it says no script reads a provable list; report.js does, for the provable column
  and reason text only.
- Paper: sec-fixes remeda sentences and cost, intro (117 for remeda), appendix replay row (L5, 111 modules).

## Mutant refutations (labelled; checks/mutref-20261027T205650Z; an agent; written 2026-10-27T21:17:50Z; SHA256SUMS 5c2da3ec)
- equiv-lean 47d9ce3 (r4-cbstm03b, parent ba05f6e) and b46c478 (unified, parent 89806a8) each add only
  MutantRefutations.lean (aadaeb06) and 16 mutant Jimple files, same blobs on both branches.
- J4 and M5r Jimple differ from the originals exactly as the A3 records; M2 regenerated from the A3 mutant source
  (javac 17 + Soot 4.7.1): 5/5 files byte-identical.
- Theorems ¬Statement_J4, ¬Statement_M2, ¬Statement_M5r (the 3 A3 timeouts); Statement_<mut> = the generated Statement
  with only the program (and its run reference) substituted (Lean meta check). runs_of_runMK: runMK = some o -> Runs;
  evaluations decide +kernel; no native_decide/ofReduceBool.
- Axioms: 3/3 exactly [propext, Classical.choice, Quot.sound] (fresh process + own body walk, 420 constants).
- Compile byte-identical to both producers (ddb05c25); leanchecker rc 0; BadCtl rc 1, GoodCtl rc 0; closure 104
  modules byte-identical to the composite check's (31 replayed + 73 reused there) + MutantRefutations: 105, 1 + 104.
- Witnesses: one record per input file (2, 2, 5 records); outcomes differ in a display line (J4), an output record
  (M2) and the abend flag (M5r). Cost 0.034 core-h.
- Paper: sec-trust mutation-test paragraph and axiom sentence, intro "Second" sentence, appendix version + replay row.

## Continued-literal front-end defect: exposure (checks/contlit-20261027T2205Z; by the evidence-owner session, no fork; written 2026-10-27T22:06:03Z; SHA256SUMS 1cdaaaba)
- The COBOL maintainer session's note (~22:0xZ, for the next revision): a nonnumeric literal continued over 3+ lines loses the trailing spaces of its
  middle lines, in snapshots 2306Z, 0518Z and 2008Z; NIST: no graded outcome depends on it (producer's statement).
- My scan: 106 CardDemo .cbl/.cpy files, 11 continuation lines (all CBSTM03A), 0 consecutive continuation lines: no CardDemo
  literal is continued over 3+ lines.
- Paper: sec-limits, one sentence after the fifth defect (attributed; exposure scan ours).

## All headline theorems together: equiv-lean unified 04d2599 (labelled re-check; checks/unified-20261027T2059Z; an agent; written 2026-10-27T22:13:23Z; SUMMARY.md 112fff30, SHA256SUMS 394f9bbb)
- Kit SUMS 597/597; HEAD 04d2599, 2564 tracked files, clean, no partial clone; deps cirlean e6ac99a, JimpleLean 2035Z,
  StrictTS a15926a, coblean 2306Z, Aeneas fdebf20; 2063/2063 closure oleans byte-identical to the freeze.
- 144 kit rows mapped (migration 16, restricted CBACT04C Java + total, Java totals 8 + run_term 8 + JL 3, CBSTM03B 4, TRX 9,
  jsmn 6, Adler-32 25, musl 11, T4 24 + 7 + 3, nibbles 10, esdiff 2 + 4); 2 restricted Rust rows added (145-146); 2 rows
  without a paper result (rlb_uuid, rlb_uuid_total).
- Statements: 15/15 prints byte-identical to the earlier checks'; 22/22 generated statement files = composite copy.
- Axioms: 146/146 std in 84 fresh processes (two modules define the same auxiliary name, so no single environment).
- Replay: 2,063 modules (incl. 17 AeneasMeta): 1,082 replayed rc 0 + 981 reused; controls ok; 1.289 core-h.
- History 04d2599 -> 89806a8 -> b46c478: additions only (Composite, CompositeRestricted, MutantRefutations, 16 jimple).
- Paper: sec-trust replay paragraph (AeneasMeta now replayed in this build), intro replay sentence, appendix versions item
  and replay row (2,063 = 1,082 + 981), caption.

## IBM-variant tester repeat on coblean 2008Z (labelled; checks/ibmvar2-20261027T2355Z; an agent; written 2026-10-28T00:08:57Z; SHA256SUMS 301ddcea)
- Seal 438/438 and raw runs 46,499/46,499 verify; pre-run list = DEVIATIONS 20:22:19Z (1e3625d2), before the runs (20:23Z);
  testers and wrappers byte-identical to the list; two logged crashed first attempts re-run with the same seeds.
- 66 seeded runs, 3,960 programs: 3,391 agree, 264 agree under the relaxed second verdict (pre-run list item 9), 120 agree up
  to class Z (INITIALIZE sign zone of a signed zoned zero: GnuCOBOL F, IBM manual and model C), 63 pointer-translation twins
  (raw equal), 34 declined, 88 differ (81 explicit collating sequences, 7 HIGH-VALUE ordering; GnuCOBOL departures, model =
  IBM on samples). 12 of 66 runs re-run byte-identical (0.051 core-h).
- Caveats: the relaxed verdict accepts a byte matching either view; CTL-W 60/60 reproduces, CTL-A did not exercise the planted
  sign table (wrapper refused it in 59/60); the CBSTM03A/B sample-data run was not repeated.
- Paper: sec-limits validation paragraph (repeat sentences), appendix addenda sentence (1e3625d2 at 20:22).

## coblean merge-4 snapshot 2231Z (labelled; checks/merge4-20261027T2355Z; an agent; written 2026-10-28T00:28:26Z; SHA256SUMS 28692ecb)
- Delivery 24/24, manifest 437/437; all 56 changed files declared (merge resolutions only beyond the branch diffs).
- TH0 from source rc 0 (115 jobs): 25 axiom lines and 25 statement hashes = 2008Z; 9 CardDemo IRs byte-identical and
  regenerate; CSUTLDTC b38f9a39; CBSTM03B 38fa862f; 503-program identity: 28 changed = coblean's list, none CardDemo.
- TSV: 6 new and 6 changed rows as declared; 65 rows re-run, 65 match. NIST: 68 runs = coblean's; vs 2008Z, 26 newly pass
  (IC module 7 -> 19, IX205A-IX215A, SM203A, SM204A, SQ206A), none worse.
- Dynamic READ NEXT defect fixed (probe: 46 at 2231Z, 00 at 2008Z); gates G2 (linker collating sequence) and G4 (CSUTLDTC
  placeholders) fail without their fix. 0.502 core-h.
- Paper: sec-limits (2231Z sentences after 2008Z; READ NEXT fix in the defect list; "latest we checked" = 2231Z), appendix list.

## TypeScript relational proofs ts-esnext / ts-repin (labelled; checks/tsnext-20261027T2356Z; an agent; written 2026-10-28T00:28:26Z; SHA256SUMS c4f3647a)
- ts-esnext 4f5883d (StrictTS a15926a): at 94cf7ff6 + 7 remeda changes; ts-repin ae7949d (StrictTS 6c1f00c, between L4 and L5):
  10 es-toolkit changes (at x3, range x2, rangeRight, tail, min/max x2). Archives = commits; slices = frozen pair files.
- 18/18 and 33/33 theorems std; replay 55/55 and 95/95 rc 0, controls ok; all pairs in the frozen lists, UNKNOWN for R6..L5;
  host hypothesis for isStrictlyEqualImplementation (Object.is depends only on values). 0.421 core-h.
- Paper: sec-fixes paragraph after difference/intersection; appendix versions item and two replay rows.

## Changed-source theorems in the paper: R2-64, R2-32 and yajl_lex_number (labelled; the user lifted the embargo on their paper text; written 2026-10-28T00:44:36Z by the session the user assigned to this topic)
- R2-64 (checks/fh-r264-20261026T2003Z, SUMMARY.md 39f59bd3, SHA256SUMS 05364943 419/419 re-verified) and R2-32
  (checks/r232-20261026T2007Z, SUMMARY.md bb6dd6c3, SHA256SUMS f3210d50 382/382 re-verified): checked as in the two
  sections above; their EMBARGOED marks no longer apply to the paper text. Replay: R2-64 285 = 284 rc 0 + the import-only
  CIR root; R2-32 285 = 283 rc 0 + 2 import-only. Parent of the 32-bit pin e00113f: c4ef58d (independent read
  checks/ilp32parent-20261028T0035Z, SUMMARY.md 3868ad95, SHA256SUMS 3b1d89c9: 5 files +35/-7, manifest COMMIT = HEAD).
- yajl_lex_number on the changed yajl_lex.c (veriforch scratch/yj1/r3_patched_ln, SHA256SUMS 515890ae): fresh check
  checks/yjpatch2-20261027T2352Z (an agent; SUMMARY.md f73c1d16, SHA256SUMS 0d2baa55 205/205): one line changed
  inside yajl_lex_number; YajlLN.ln_spec for 0 <= len <= |xs|, len < 2^32 (R3's contract: len < 2^31); 7/7 std; closure
  122 = 121 rc 0 + the import-only CIR root; pin ffab71e; ClangIR and Gen regenerate byte-identically; a unit theorem (no
  entry theorem uses it; R3's harness theorem and its 2^31 bound unchanged). The partial check
  yjpatch-20261027T1820Z (stopped 18:22Z) is superseded.
- In the paper: sec-ub paragraph "We proved three more theorems" (statements, bounds, axioms, replays only), appendix
  versions sentence, replay rows (284 + 1; 283 + 2; 121 + 1). Corrected with them: the parse-only row (247 = 246 rc 0 + 1
  import-only, checks/cjh-20261025T1854Z) and the c4ef58d whole-harness row (285 = 284 rc 0 + 1, checks/fh-r1-20261026T2003Z).
- paper_lint PASS on the live abstract before the freeze (v1 and v2; ~/fv_ub_20261027/lint/live_20261028T004425Z). Claims audit ub1 (6 findings, all applied; re-check clean) and de-AI rounds ubr1a/ubr1b (3 of 4 critics clean; the fourth cited
  examples outside the new paragraph only): records in ~/fv_ub_20261027 (LOG.md, deai/rounds/*/SCREEN.md).
- Correction 2026-10-28T00:46:54Z (an agent): in the IBM-variant repeat section above, the re-run covered 10 of the 66 seeded runs plus the two controls (not 12 of the 66); in the TypeScript section, the ten re-pin changes include two changes to at (eb181846, c939d973), not three.
- Correction 2026-10-28T01:07:05Z (an agent): in the TypeScript section above, six remeda pairs come from fix commits; isStrictlyEqualImplementation (33caa142) comes from a chore commit and is one of the 269 refactorings/style/chores.

## coblean merge-5 snapshot 0109Z (labelled; checks/merge5-20261028T0112Z; an agent; written 2026-10-28T01:43:12Z; SHA256SUMS 72e92999)
- Files 23/23, manifest 511/511; all changes declared. TH0 from source: 25 axiom lines and statement hashes unchanged; 9 CardDemo
  IRs byte-identical; CSUTLDTC b38f9a39; 305/503 front-end outputs differ = coblean's list, none CardDemo; 63 TSV rows match.
- NIST: 10 programs newly pass (NC207A-NC209A, NC222A, SM201A, SM202A, SM206A-SM208A, SM401M); NC401M stops at SYMBOLIC.
- Continued-literal and de-editing defects fixed (our runs of the session's probes); the edit-point defect is still present.
- CBEXPORT/CBIMPORT: RECORD KEY outside the file's record (IBM LR 6.4), so the front end and IBM reject them; COBSWAIT:
  ACCEPT FROM SYSIN unsupported. 0.449 core-h.
- Paper: sec-limits (0109Z sentences; defects 2-4 status; "latest we checked" = 0109Z), sec-migration program-selection
  sentence, appendix snapshot list.

## CBSTM03A to Rust (labelled; checks/r4a-20261028T0107Z; an agent; SUMMARY.md written by the evidence-owner session from the fork's report; written 2026-10-28T01:47:07Z; SHA256SUMS 7eb0f7bb)
- equiv-lean a50f10e (r4-cbstm03a): Cbstm03a.Rust.rust : Statement and rust_composite, std axioms, 0 sorry; 73 files added to
  b46c478, 3 changed (Composite.lean, genall.sh, genstmt.py; 24/24 statements regenerate byte for byte).
- Provenance: lib.rs = veriforch final v6 cdfec3ff; IR 2c5ba72b = pin2306Z-cbstm03ab; Aeneas output = commit except the
  maxRecDepth line (hand edit, as in other modules).
- Hand-written: Domain + three generator overrides (records map, walk display patterns -> drop 11, address-space model);
  one initial storage (178,495 bytes, PSAPTR null).
- Replay: closure 1,136 = 45 replayed + 1,091 reused (unified replay); controls ok; 0.321 core-h.
- The producer's "10/10" list was wrong (CBEXPORT/CBIMPORT have no theorems); the ten = the paper's eight + CBSTM03B +
  CBSTM03A; Rust 10/10, Java 9 (CBSTM03A Java pending).
- Paper: sec-migration paragraph after the CBSTM03A+B theorems; intro sentence; appendix item and replay row.

## coblean merge-6 snapshot 0336Z (labelled; checks/merge6-20261028T0339Z; an agent; written 2026-10-28T04:12:51Z; SHA256SUMS a972575c)
- Files 21/21, manifest 536/536, changes declared; TH0 from source: 25 axiom lines and statement hashes unchanged; 9 CardDemo
  IRs byte-identical; CSUTLDTC b38f9a39; identity 6 changed, none CardDemo; 61 TSV rows match.
- NIST: 6 newly pass (NC108M, NC134A, NC174A, NC254A, SM103A; SM104A from fail); NC107A newly runs and fails 2 tests (the
  session's JUSTIFIED RIGHT group-move finding; not in the paper until the session's exposure note). Edit-point defect still
  present. 0.460 core-h.
- Paper: tab:snapshots row, "five later snapshots", fourth defect "still present in 0336Z", appendix list.

## CBSTM03A to Java (labelled; checks/r4ajava-20261028T0213Z; an agent; SUMMARY.md written by the evidence-owner session from the fork's report; written 2026-10-28T04:35:20Z; SHA256SUMS 76e2ba27)
- equiv-lean 8ed869e = a50f10e + the JimpleLean maintainer session package cbstm03a_java_20261028T0124Z (243 files: 236 new, 6 identical,
  Java/Iface3.lean replaced; the replacement strengthens a helper precondition, outside the statement) + Composite.lean
  (java_composite) + README; Cbstm03a.Java.{java (Sim, partial correctness), java_terminates, java_total, java_composite}:
  std axioms, 0 sorry.
- Provenance: Cbstm03a.java 08402d30 = veriforch guided/java/v3 (first guide); Jimple regenerates byte for byte with javac 17
  -g + Soot 4.7.1; statement JavaStatement.lean 6ebb42b4 unchanged from a50f10e.
- Hypotheses (17): valid values x4, Domain (hand-written, as for Rust), fewer than 2^27 records (Rust 2^28), fuel n > records,
  4 file premises (Java arrays of record objects, < 2^31 elements), 6 class-init premises.
- Replay: closure 1,370 = 252 replayed + 1,118 reused from the r4a replay; leanchecker 252/252 rc 0; controls ok;
  4.952 core-h guarded. Recipe note: compiling needs --load-dynlib=libJimpleLean_Jimple.so (JimpleLean precompileModules,
  as lake does); without it one module hits its heartbeat limit; not a proof gap.
- Paper: sec-migration paragraph after the Rust theorem; intro "both to Rust and to Java"; appendix item and replay row.
- 2026-10-28T05:38:19Z: added prior-art citation cve202616554 (CERT Polska advisory CVE-2026-16554, 2026-07-27; prior_art/LEDGER_addendum_20261026_cve.md) to the changed-source paragraph in sec-ub.tex and to refs.bib.

## COBSWAIT all-input theorem (labelled; checks/cobswait-20261028T060011Z; an agent; written 2026-10-28T06:10:03Z; SUMMARY.md 239593fa, SHA256SUMS 24f07de2)
- Pin coblean-pinM7-cobswait-20261028T0554Z (SHA256SUMS 956392e2, 1146/1146) = snapshot 0551Z (merge 7, ACCEPT FROM SYSIN) +
  Examples/Cobswait (Cobswait c535a43b, Model 6b6d3e80, Prog 228fd800) + cobswait.ir.json + lakefile (lean_lib Cobswait); 677
  shared build files byte-identical (43 Cobol oleans, Cobol.olean be3132eb).
- IR regenerates byte for byte (f2ae5593) from the unmodified COBSWAIT.cbl (38a8d282); new modules rebuild byte-identical.
- cobswait_every: env and m0 arbitrary, m0.size = 12, fuel 10 (run_mono): no device -> named unsupported; invalid parm ->
  invalidData; else one CALL MVSWAIT: none -> fault; one 4-byte result -> stop run with storage = result ++ parm; other ->
  fault; every fault has out = []. Corollaries cobswait_digits, cobswait_waitstep (WAITSTEP.jcl card -> 3600), parmVal_*.
- Axioms: std for the headline theorems; 76 theorem constants within the three (parmVal_spaces: propext only); scan 0 hits
  (planted 2). Replay 44/44 rc 0, controls ok. GnuCOBOL spot check with a stub MVSWAIT: 3/3 cards agree (labelled).
- 0.011 guarded core-h. Paper: sec-migration (COBSWAIT sentences; 12 of 14), program-selection sentence, Appendix A.

## coblean merge-7 snapshot 0551Z (labelled; checks/merge7-20261028T0554Z; an agent; SUMMARY.md written by the evidence-owner session from the fork's report; written 2026-10-28T06:25:05Z; SHA256SUMS e55e3038)
- d0 files 20/20, manifest 561/561; 0336Z + w7m_vs_live.diff = 0551Z byte for byte; TH0 from source: 25 axiom lines (278e3cce)
  and statements unchanged; 9 CardDemo IRs identical and regenerating; CSUTLDTC b38f9a39.
- Identity 500/503; NC109M, NC204M and COBSWAIT differ only at their ACCEPT statements. TSV: 252 same, 8 predicted changes
  (CV.sum covered 11 -> 12 of 14 batch programs), 3 new V.sysin rows; 63/63 re-run match.
- NIST: 173 runs unchanged, 0 newly pass with the frozen runner; NC109M 11/11 only with the labelled runner copy that supplies
  SYSIN (diff 25010422). sysintest 60/60 at s1 and s2; control 0/60. 0.453 core-h.
- Paper: tab:snapshots row (six snapshots), caption note on NC109M, Appendix A list, Limitations "six later snapshots".

## T2 union units and T3 shared_ptr verdicts at cirlean next2 424e821 (labelled; checks/t23next2-20261028T061053Z; an agent; SUMMARY.md written by the evidence-owner session from the fork's report; written 2026-10-28T06:28:54Z; SHA256SUMS 2dd347ed)
- Packages t2_unionpun_next2_424e821 (59083fd5, 26/26) and t3_shared_ptr_next2_424e821 (4811f315, 189/189); next2 frozen tree clean.
- Statements = the e6ac99a expressions (T2 3/3, T3 24/24); std axioms; replay 115/115 rc 0, no reuse, controls ok; one proof-side
  line in Bridge/Cir/Tactic.lean:112.
- Condition 1: next2 makes libstdc++'s 64-bit counter read UB (Ctx.punnedMember), so each T3 verdict relates outcomes only on inputs
  on which neither version has UB and says nothing about executions that reach the read (both versions go wrong on the same inputs).
- Condition 2: the T3 verdicts use T3's program terms; next2's own front end emits them differently (std::string union layout in
  24/24; atomic cmpxchg unsupported in 2/24). The T2 terms equal next2's front-end output; the T2 NaN restriction stays.
- 0.217 guarded core-h. Paper: sec-thrift T2 and T3 sentences; Appendix A version list and two replay rows.

## NIST census N3 of coblean 0551Z (labelled; checks/nist3-20261028T072837Z; an agent; written 2026-10-28T07:41:02Z; SUMMARY.md 3dda080a, SHA256SUMS 7c1c81f7)
- Plan: prereg/ADDENDUM_NIST3_coblean.md (0a5fcca5), logged 06:50:15Z before any run; correction entry 07:40:01Z (the pre-run
  summary reached the evidence owner after the NC module had run; the plan was fixed before it).
- Producer seal 729f32ff (2602/2602); tree rebuilt from a fresh copy with the declared changes (cobolrun 195786db, run_nist.py
  6635004c = N2's); census re-run: 309/309 per-program outcomes identical: pass 235, fail 11, unsupported 61, undefined 1,
  error 1, timeout 0; per test 5513/5570 (N2: 85, 13, 193, 1, 17, 0; 2687/2767).
- Transitions recomputed: 155 outcome changes (unsupported->pass 131, error->pass 14, fail->pass 5, unsupported->fail 3,
  error->unsupported 2), no pass -> other; NC175A changes detail only. 14 merge attributions sampled, all consistent (the
  attributions remain the COBOL maintainer session's statements).
- Switch control (labelled, outside the census): without COB_SWITCH, NC108M passes and NC174A, NC211A, NC254A fail.
- NC109M: unsupported in the census; separate labelled sysin sub-run (833a680b) passes 11/11, reproduced.
- 0.019 guarded core-h (check). Paper: sec-stack NIST paragraph (census sentence), app:later paragraph "The NIST census N3",
  tab:snapshots NIST column and its caption notes dropped in favour of the census.
- Addendum to the N3 section (2026-10-28T08:00:26Z, claims audit v30): the census departs from its plan in one respect, logged only after
  the NC module had run: the plan set COB_SWITCH_1=ON, COB_SWITCH_2=OFF for NC211A only; the census sets them for every
  program (as tools/nist/gc_ref.py:117 does for the references; read-only check by an agent). By the switch control, the
  plan's setting would give 233 pass, 13 fail. NC109M counts among the 61 unsupported but fails for lack of an input device.

## Whole cJSON harness theorem R1 re-verified at cirlean next2 424e821 (labelled; checks/r1next2-20261028T0803Z; an agent; written 2026-10-28T08:43:22Z by the sec-ub session; SUMMARY.md 54552ac4, SHA256SUMS 8e4b728d 336/336)
- Package ~/veriforch/runs/postfreeze/r1_cjson_next2_424e821 (SHA256SUMS 4747bb88, 493/493 OK, 0 symlinks; hard-linked copy replay/r1next2-20261028T0803Z/pkg) on frozen pin ~/cirlean_frozen/next2_424e821_20261027; all 9 announced file hashes match; RESOLUTION.tsv (288 modules: 45 CIR.* + 243 lib/) verifies 288/288 on disk; changed-unit .oleans match cirlean's *_next2_v4 deliveries.
- Entry statement and printed definitions byte-identical to e6ac99a's (5,857 bytes, 0 diff); 32 unit theorems + FHEntry.entry_main print [propext, Classical.choice, Quot.sound].
- Unit statements e6ac99a -> 424e821: 31/32 and CIR.CJ.printable byte-identical; 1/32 (cJSON_cJSON_New_Item_spec) adds hpunm (ctx.punnedMember ... = false), discharged inside the composition so the entry statement carries no new hypothesis.
- Kernel replay: 288/288 modules rc 0 via leancheck1lp.sh (pjobs_v3 N = 2, 609.6 s); leanchecker --fresh on the entry module rc 0 (375.1 s); controls BadCtl rc 1, GoodCtl rc 0; 0.552 core-h guarded.
- Paper: sec-ub sentence ("On the member-strict C semantics (cirlean 424e821)..."), appendix versions item ("proved again at cirlean e6ac99a and 424e821") and replay row ("the same, on the member-strict C semantics & 288 & all"); "labelled results" -> "exploratory results" and "our model" -> "our semantics" in sec-ub.tex.

## CBSTM03A with CBSTM03B: sorted-abort corollaries (coblean pin2306Z-cbstm03ab-v2-20261028T0658Z; labelled; checks/stmcor2-20261028T084846Z; an agent; written 2026-10-28T09:00:26Z; SUMMARY.md d8c5f188...)
- Pin = 1251Z + Examples/StmCore/SortedAbort.lean (8 build files) + SHA256SUMS + STMCOR_PROGRESS.md (diff -rq; sha256sum -c 839/839).
- abortPost_sorted: CardsSorted trs -> (AbortPost (grp trs) pre ... walkDisplays [] [] msg st <-> out = msg ++ (pre.flatMap evsOfS).reverse
  ++ walkDisplays and STMT/HTML open for output with pre.flatMap stmtOfS / htmlOfS). stm_run_abort_cust_sorted / _acct_sorted: hypotheses of
  stm_run_abort_cust/acct + CardsSorted; Fault.abend (-1) with out = custMsg/acctMsg ++ pre's evsOfS events ++ the 11 walk lines (newest
  first), STMT/HTML = pre's stmtOfS/htmlOfS records; pre = the cross-reference records before the one whose customer/account is missing.
- Axioms exactly [propext, Classical.choice, Quot.sound] x3 (fresh process; planted sorry/axiom flagged). Replay: SortedAbort from source
  against the stm03ab closure (28 + 43 oleans byte-identical, reused) rc 0; leanchecker --fresh rc 0; prebuilt Stm/StmCore + SortedAbort 29/29;
  BadCtl rc 1, GoodCtl rc 0; 0.080 core-h. No new abend case: restatement under sortedness through stm_run_sorted's models.
- Paper: sec-migration sentence (exploratory corollaries), Appendix A item, replay row (72, all).

## Defect E: leading-comma PICTURE strings (front end; reported by the COBOL maintainer session; checks/picscan-20261028T104013Z; by the evidence-owner session, no fork; written 2026-10-28T10:41:27Z; SUMMARY.md 2bdcb71c...)
- All 48 snapshot front ends + pins read ,ZZ9 as ZZ9 (session's probe). Our independent scan: CardDemo src/app 109 files, 9,143 PICTURE clauses, 0 hits; NIST extract3 510 files, 58,366 clauses, 0 hits; planted control 3/3 (incl. a string continued on the next line). No exposure.
- Paper: App. F paragraph (session's description, our scan); sec-limits counts (eight after our checks, four of them on the session's report, all but five unfixed/unstopped, COBSWAIT covered by this scan).

## C1 attribution run of N3 (coblean variant: size error traps with either SIZE ERROR phrase; labelled; plan prereg/ADDENDUM_C1ATTR_coblean.md b677baab + tree addendum 60553303; checks/c1var-20261028T110556Z; an agent; written 2026-10-28T11:14:44Z; SUMMARY.md 623765f6...)
- Producer sealed c1var/sealed_20261028T110243Z (SHA256SUMS 4b8c115d, 2,424/2,424). Our rebuild from the N3 replay tree + patch b740d599: Resolve.lean dd5de241, cobolrun 8b0a88db (= producer's); full 309-program re-run identical to the producer's per program.
- Own per-test parser N3 vs C1: 91 entry changes = 55 FAIL->PASS (expected_flips_55.tsv exactly; NC106A, NC170A-173A, NC175A-177A, NC202A, NC253A) + 36 new NC251A PASS (F5-11..F5-20, agree with GnuCOBOL; N3 stopped at line 768, DIVIDE by zero under NOT ON SIZE ERROR alone; variant stops at DIV-TEST-F5-21, unsupported). NC107A unchanged (JUST-TEST-04). Census 245/1/62/0/1; per test 5,568 of 5,570. Run-time lines (NC214M ACCEPT TIME, WHEN-COMPILED) not compared.
- Paper: App. F paragraph after the N3 census; sec-stack sentence after the census.
- Note (audit v38): the NC251A change was not predicted by the recorded plan ('any other difference counts against the attribution'); its stop is the semantics' division-by-zero abend without ON SIZE ERROR (Arith.lean, unchanged from N3), not the truncation rule. Own per-test comparison covers 5,191 entries; the rest of the census's 5,570 rest on the producer's comparison and the census totals.

## coblean snapshot 20261028T1223Z = merge 8 (fixes A-D; labelled; checks/merge8-20261028T122832Z; an agent; written 2026-10-28T12:42:16Z; SUMMARY.md 72465cbf...)
- Manifest 19454817 577/577; sources changed Edit, Sem/Data, Sem/Exec, parser.py (+ testers/docs), nothing under Examples/; Cobol.olean be3132eb; our rebuilt changed oleans = snapshot's. The 9 CardDemo IRs = 0551Z = 2306Z; all regenerate byte for byte (CBSTM03B 38fa862f, CSUTLDTC b38f9a39, COBSWAIT f2ae5593). TH0 not rebuilt by us (producer: same 25 axiom lines).
- tests/EditPoint.lean: 13 theorems, exactly std axioms, leanchecker --fresh rc 0, planted controls; old == new editing on every picture outside the changed cases, the four theorem pictures (CBTRN03C -ZZZ,ZZZ,ZZZ.ZZ, +ZZZ,ZZZ,ZZZ.ZZ; CBSTM03A Z(9).99-, 9(9).99-) satisfy that; #eval 880,040 comparisons each, 0 differences. Fixes A-D: probes ok on 1223Z, mismatch on 0551Z; testers byte-identical to editfix runs; G-editins, G-editptb remain.
- NIST, all 309 on 1223Z (own tree, cobolrun 6f8a8f56): census 236/10/61/1/1, per test 5,515 of 5,570; own parser vs our N3: only NC107A fail -> pass (JUST-TEST-04 x2 = GnuCOBOL). Paper: tab:snapshots row, App. F sentences, sec-stack and sec-limits updates.

## Arithmetic departures F1-F6 and G (coblean; reported by the COBOL maintainer session before any fix; checks/arith-20261028T140509Z; an agent; written 2026-10-28T14:13:15Z; SUMMARY.md a2863d43...)
- Own scan of 18 IRs (12 theorem programs + pins + acctint example): 3 divisions; only CBACT04C 1300-COMPUTE-INTEREST changes places under F1 (model 2, IBM 4), a lone quotient truncated into S9(9)V99 without ROUNDED -> same stored value; F2/F3/F5/F6/G 0 hits (plant hits all). Lean trunc_comp (trunc2 . trunc4 = trunc2 over Int.tdiv), std axioms. Model truncation cited (Resolve/Arith/Round 2306Z). Probes on 2306Z vs GnuCOBOL -std=ibm reproduce D1-D3 and G.
- Assumption stated in the paper: IBM truncates the extra intermediate places (manuals imply, do not state). NIST exposure and F4/R1 rest on the session's scans. Paper: App. F paragraph; sec-limits sentences.

## coblean snapshot 20261028T1421Z = merge 9 (defect E fix; labelled; checks/merge9-20261028T142433Z; an agent; written 2026-10-28T14:32:56Z; SUMMARY.md f37481f5...)
- Manifest 0ab8f11a 583/583; only tools/cobolfe/lexer.py (one condition) + testers/docs; 68 oleans identical, Cobol.olean be3132eb; theorem IRs (9 CardDemo, CBSTM03B 38fa862f, CSUTLDTC b38f9a39, COBSWAIT f2ae5593) regenerate byte for byte; probe ,ZZ9 [z,z,nine] on 1223Z, [comma,z,z,nine] on 1421Z, B,ZZ9 unchanged; lctest 60/60 both seeds (G-editlc classified); NIST 309 re-run = merge 8 (236/10/61/1/1, 5,515 of 5,570; 0 changes). TH0 not rebuilt (no olean changed).

## coblean snapshot 20261028T1636Z = merge 10 (close-fix + ifn2; labelled; checks/merge10-20261028T164108Z; an agent; written 2026-10-28T16:58:23Z; SUMMARY.md dd09c702...)
- Manifest 349d588b 619/619; 8 Cobol Lean files + cobolfe changed, nothing under Examples/; theorem IRs regenerate byte for byte (CBSTM03B 38fa862f, CSUTLDTC b38f9a39, COBSWAIT f2ae5593); 32 oleans differ (9 library, 23 Examples recompiled, sources unchanged). FuelMono +2 arms; fresh-process axioms: FuelMono x5 std, ioFinishU_mono [propext]; TH0 24/25 std + bincnt_equiv bv_decide native axiom (= producer's list). closetest/powtest + hand rows = producer's. NIST 309: 246/11/50/1/0/1, 5,780 of 5,836; vs merge 9 only 11 outcome changes (SQ109M, SQ110M, SQ123A, SQ124A, SQ211A, SQ215A, IX204A, IX216A, SQ303M, NC252A -> pass; NC250A unsupported -> fail 114/115, IF--TEST-28 = defect G).

## equiv-lean unified-next2 fac6c38 (cirlean 424e821 + coblean 0109Z): NOT CONFIRMED (checks/next2-20261028T161321Z; an agent; written 2026-10-28T17:10:59Z; SUMMARY.md d7a62165...)
- Replay of the 2,362-module closure: 620 reused, 1,742 replayed: 1,720 rc 0, 22 rc 1 (JavaProof/RustProof of 11 COBOL programs, stale oleans = 8ed869e build, Env.mk arity without coblean 0109Z's absent field); 56/176 claimed theorems reach them; the other 120 closures replay rc 0; pins pass; axioms 175/176 std (+ thrift_classes_length none). Statement text unchanged for all 176; meaning follows the new pins (T4 contracts gain ProtoRecords; memcpy_diff_overlap RHS). Not in the paper; producer asked to clean-rebuild and recommit.
- 2026-10-28T17:47:49Z RE-CHECK after the producer's rebuild: CONFIRMED (section 7, SUMMARY.md 82a4de0b): tracked 2,892/2,892 = fac6c38; 64 oleans changed; closure 2,362: 154 replayed rc 0 (incl. the 22), 2,208 reused; axioms std for the 56 previously blocked (29 fresh processes); recompiles of 4 modules byte-identical and declaration-equal. Paper: sec-trust paragraph, sec-limits clauses.

## sec-ub exposure check for the pointer-stride defect and core-memory gaps (checks/ub-stride-coresnd-20261028T1846Z; written 2026-10-28T18:51:20Z by the sec-ub session; SUMMARY.md 6d4c7c84, SHA256SUMS bd34c1c3 23/23)
- Pointer-stride and pointer-difference scan (cirpun --stride): STRIDE 0 across both UB findings (tiny-regex-c matchstar and cJSON cJSON_SetValuestring, UNKNOWN 0) and all six harness/unit closures: cjh (15 functions, UNKNOWN 0), r1/r264/r232 (32 functions, UNKNOWN 1 on localeconv()->decimal_point, a 1-byte-element char[2] block in cirlean's model), yjr3/yjpatch2 (45 functions, UNKNOWN 96 = u8 strides on the unresolved indirect-call allocator pointers already disclosed in sec-ub.tex).
- Core-memory gaps (G5, G4, G2, G3, U1/U2 of checks/coresnd-20261028T183958Z): 0 union declarations, 0 get_bitfield/set_bitfield ops, 0 atomic ops, and 0 va_arg in all six Gen trees; cJSON's single sscanf ("%lg" in cJSON_print_number) matches double* and its single strtod (cJSON_parse_number) stores endptr into an unsigned char* slot; yajl-ruby's strtol/strtod are in the untaken yajl_integer/yajl_double branches; all .copy ops copy between matching declared types.
- Paper: sec-ub sentences on the two UB findings and on the harness closures.

## C-semantics audits, exposure, T3 vacuity, V triage, merge 11, tier-0 (d0; appended 2026-10-28T22:48:08Z by date -u)
- Reproductions of the C maintainer session's reports (own tests, frozen builds + 3 replay-copy interpreters): stride-20261028T182920Z (SUMMARY e44b8fe8: stride/difference defect at all 13 versions; vbase/: cir.vtt.address_point unsupported), coresnd-20261028T183958Z (SUMMARY 40499ff0: G5, G4 at all 13; G2 at f107f53/424e821; U1/U2 from 90b9c2f), libsnd-20261028T184506Z (SUMMARY 2cfb0c8a: mem* null/0, const-local store, sprintf/va gaps).
- Exposure outside sec-ub: coreexpA-20261028T184243Z (8412eb48: 0 G5/G4/G2/G3 on claimed paths), coreexpB-20261028T184254Z (3f58347a + followup 029c1a4b: stride sites strlen word loop, T2 409 offset 0, T3 D2 and breakLoop callee (unreachable); kept union pointers in std::string/TSocket; T4 string bit-fields behind models), coreexpC-20261028T184554Z (208499ca: no library-gap condition can hold); the C maintainer session stride scan v2 ~/cirlean_work/scratch/stridescan_v2 (0bce58a8; agrees).
- T3 vacuity: vacuity-20261028T185625Z (fc2b3fb5; deep/DEEP.md 290e7f3f: 19) + t3arity-20261028T200633Z (559d752a: 16 statements drop a bool -> bindArgs .ub): 22/54 relate no execution; none of the 9 partly certified commits has a verdict relating an execution. Tier-0 re-proof (veriforch t3_tier0_tsocket_424e821, faf97918): tier0-20261028T214410Z (87ae92c5: confirmed; witnesses early return only).
- Non-vacuity of partial C theorems: nonvac-20261028T191944Z (b3e653f5: jsmn, musl memcpy/strlen complete on sample inputs).
- V triage at next2: vtriage-20261028T190635Z (ed8a5a7e: 26/26 agree; 13 real/13 false; UBSan 7/7).
- Merge 11 = coblean-20261028T2106Z: merge11-20261028T211008Z (006b0196: confirmed; F1 exception only at CBACT04C 1300-COMPUTE-INTEREST and NC252A COMP-TEST-32; census 247 = producer); TSV rows re-run pending (tsv/ follow-up).
- Freezes: 1941Z (audit v47), 2018Z (v48), 2138Z (v49).
- 2026-10-28T22:55:11Z merge-11 TSV follow-up (checks/merge11-.../tsv/TSV.md 362af16e; SUMMARY 08b1b81b): 284 same, 4 changed (T5/E4 +55, T7 +10, S2), 12 new V.dmax rows, 0 CV changed; changed/new rows re-run match (T7 on the snapshot). Cron item (4) for 2106Z done.
- 2026-10-28T23:03:07Z FREEZE freeze/paper_v2_20261028T2302Z (src/main.pdf 37edddf3, SHA256SUMS 4ed23deb, 51 files; 59 pages, 0 overfull, lint PASS): + tier-0 TSocket re-proof (exploratory) + merge-11 TSV follow-up note + audit v50. Supersedes 2138Z.
- 2026-10-29T00:40:24Z FREEZE /home/user/fv_paper/freeze/paper_v2_20261029T0040Z (src/main.pdf 2898a26f, SHA256SUMS 9169b90b; lint PASS): + v2r57 de-AI fixes + audit v51. Supersedes 2302Z.
- 2026-10-29T04:53:48Z FREEZE /home/user/fv_paper/freeze/paper_v2_20261029T0453Z (src/main.pdf 9b4ac85a, SHA256SUMS c5731fef): + App F readings wording (R1, F7) + audit v52. Supersedes 0040Z.
- 2026-10-29T07:24:20Z FREEZE /home/user/fv_paper/freeze/paper_v2_20261029T0724Z (src/main.pdf 46e9b797, SHA256SUMS 89da34ee): + three later C/C++ defects (by-value, return by value, declared-only globals) with exposure + audit v53. Supersedes 0453Z.
- 2026-10-29T09:53:24Z FREEZE /home/user/fv_paper/freeze/paper_v2_20261029T0953Z (src/main.pdf bfdabf60, SHA256SUMS d928432c): + merge 12 (coblean 0854Z: remaining departures fixed, Z0/C30, stops, R3 assumption) + audit v54. Supersedes 0724Z.
- 2026-10-29T15:17:48Z FREEZE /home/user/fv_paper/freeze/paper_v2_20261029T1517Z (src/main.pdf 03118f87, SHA256SUMS 9fda0902): + de-AI v2r58 fixes + audit v55. Supersedes 0953Z.
- 2026-10-29T17:22:23Z tier-1 (exploratory): checks/tier1-20261029T164912Z (SUMMARY 7ba1301f: 12/12 nonvacuous, 10/12 proved again, 072/105 refuted on memory set by no function in the closures; std axioms; --fresh 12/12) + checks/t1closure-20261029T171309Z (SUMMARY c16484b9: closure 53 + 46 modules). Paper text added; exposure check by an agent pending, then audit v56 and a freeze.
- 2026-10-29T18:21:12Z FREEZE /home/user/fv_paper/freeze/paper_v2_20261029T1820Z (src/main.pdf dfa3ad18, SHA256SUMS 6361a35b): + tier-1 re-proof (checks/tier1-20261029T164912Z 7ba1301f, t1closure-20261029T171309Z c16484b9, t1expo-20261029T172130Z 9136a55a) + audit v56. Supersedes 1517Z.

## cirlean next3 (7c73739) FH bundles check (labelled; checks/fhnext3-20261030T0432Z; an agent; written 2026-10-30T05:07:39Z by the sec-ub session; SUMMARY.md b5fe9173, SHA256SUMS 0efa553c 561/561)
- Freeze notice ~/cirlean_work/scratch/next3_chain/FREEZE_NOTICE_next3_7c73739.md (14694e8f): all 19 announced sha256 values verify; MANIFEST_build.sha256 (8d2cc1ff) verifies 1017/1017 files in ~/cirlean_frozen/next3_7c73739_20261030/.lake/build; all 10 ~/cirlean_work/deliver/*_next3/SHA256SUMS pass sha256sum -c.
- Five conditions for the GhostNat12.lean:77 (3M -> 6M) step-budget change hold: (1) primary fix tried first (pin_chain_vs_c4ef58d_v2.diff 90de2bf8 touches only GhostNat7.lean, GhostNat8.lean, and GhostNat12.lean:77); (2) all 20 .lean source files across the 10 *_next3 bundles are byte-identical (cmp -s rc 0) to their *_next2_v4 / *_next2 counterparts (0 statement changes, no maxHeartbeats fallback and no parse_array closer used); (3) old/new values recorded in RESTATEMENTS_next3.md (7ceb78a5) and pin_chain_vs_c4ef58d_v2.diff; (4) all 34 theorem names across the 10 bundles check in fresh Lean processes and print only subsets of [propext, Classical.choice, Quot.sound]; (5) per-module leanchecker 259/259 distinct modules rc 0 (pjobs_v3 N = 2, ulimit -v 32 GiB) and leanchecker --fresh 10/10 root bundle modules rc 0 (98.5-155.8 s each); 0.429 core-h guarded.
- 2026-10-30T06:07:23Z FREEZE /home/user/fv_paper/freeze/paper_v2_20261030T0607Z (src/main.pdf a96e64ce, SHA256SUMS 72a46df2): + third revision 7c73739 (checks next3pin-20261030T023649Z, Vnext3-20261030T034258Z 2a185f3f, vtriage3-20261030T043105Z 26ec1e3d, n3kinds-20261030T050155Z a60932c1) + row-184 correction (vtriage errata 2-3, 0ad1f451) + audits v57/v57b. Supersedes 1820Z.
- 2026-10-30T06:38:25Z FREEZE /home/user/fv_paper/freeze/paper_v2_20261030T0638Z (src/main.pdf 1a3eb6bc, SHA256SUMS 3273549a): + companion 072/105 re-proof under a memory hypothesis (checks/ctor-20261030T054550Z 2cb97f67) + audit v58. Supersedes 0607Z.

## CycleSpecsP2N v5 FH bundles at cirlean next3 7c73739 (labelled; checks/fhnext3v5-20261030T1146Z; written 2026-10-30T11:57:14Z by the sec-ub session; SUMMARY.md 041ce9c5dd6b9b04, SHA256SUMS 2c08c8af83b55418 27/27)
- Packages ~/cirlean_work/deliver/{parse_array_strong_next3_v5 (790e46ef, 11/11), parse_object_strong_next3_v5 (7946ff56, 19/19), cJSON_Delete_next3_v5 (1db06365, 9/9)}, SPEC_v5.sha256 (CycleSpecsP2N.lean 0c5e9e53, CycleSpecsP2N.olean 371b7033, 4/4), and 238/238 distinct rows in the union of RESOLUTION_v5.tsv verify on disk.
- Fresh Lean process (statement/check_v5.out, rc = 0): CJReal.delete_forest : DeleteSpecTheirsP, parse_array_step : ParseArrayStepSpecP, and parse_object_step : ParseObjectStepSpecP typecheck against CycleSpecsP2N v5 and all print [propext, Classical.choice, Quot.sound].
- Kernel replay (replay/, ulimit -v 32 GiB): 12/12 rebuilt v5 modules pass per-module leancheck1lp.sh rc = 0 (237 shared modules reused from checks/fhnext3-20261030T0432Z); 3/3 root modules pass leanchecker --fresh rc = 0 (cJSON_Delete_fuzz_harness 98.8 s, ParseArrayStepStrong 122.6 s, POSFinal4 152.5 s).

## Whole cJSON harness theorem R1 re-verified at cirlean next3 7c73739 (labelled; checks/r1next3-20261030T1407Z; an agent; written 2026-10-30T14:38:54Z by the sec-ub session; SUMMARY.md d336e0b6, SHA256SUMS de921b52 639/639)
- Package ~/veriforch/runs/postfreeze/r1_cjson_next3_7c73739 (SHA256SUMS 13ef1e65, 499/499 OK, 0 symlinks; hard-linked copy replay/r1next3-20261030T1407Z/pkg) on frozen pin ~/cirlean_frozen/next3_7c73739_20261030; all 8 announced file hashes match; RESOLUTION.tsv (300 modules: 54 CIR.* + 246 lib/) verifies 300/300 on disk; all 12 rebuilt CycleSpecsP2N v5 bundle .olean hashes match checks/fhnext3v5-20261030T1146Z/v5_oleans.sha256.
- Entry statement and printed definitions byte-identical to 424e821's (0 diff); 32 unit theorems + FHEntry.entry_main print [propext, Classical.choice, Quot.sound].
- Unit statements 424e821 -> 7c73739: 30/32 and CIR.CJ.printable byte-identical; 2/32 change (cJSON_cJSON_New_Item_spec adds hrel = ctx.memberRelated ... (.record "internal_hooks") = true; cJSON_skip_utf8_bom_spec types the input buffer block bc as .array (.int false 8) xs.length), both discharged inside the composition so the entry statement carries no new hypothesis.
- Kernel replay: 300/300 modules rc 0 via leancheck1lp.sh (pjobs_v3 N = 2, 618.5 s); leanchecker --fresh on the entry module rc 0 (388.3 s); controls BadCtl rc 1, GoodCtl rc 0; 0.225 core-h guarded.
- Paper: sec-ub sentence ("On the third revision of the C semantics (cirlean 7c73739)..."), appendix versions item ("proved again at cirlean e6ac99a, 424e821 and 7c73739") and replay row ("the same, on the third revision of the C semantics & 300 & all").
- Final manifest hashes of checks/r1next3-20261030T1407Z (2026-10-30T14:41:58Z): SUMMARY.md 1047f089, SHA256SUMS a3fed15e (642/642).
- 2026-10-30T14:53:37Z FREEZE /home/user/fv_paper/freeze/paper_v2_20261030T1453Z (src/main.pdf 9fb1afe6, SHA256SUMS 6b6ff49b): the harness-study session's 1442Z content (cJSON re-proof on 7c73739) + audit v59 fixes to the third-revision uses and the App. B record list. Supersedes 1442Z.

## cirlean next3.1 (e0b4d64) FH bundles check (labelled; checks/fhnext31-20261030T1834Z; an agent; written 2026-10-30T19:04:04Z by the sec-ub session; SUMMARY.md a66c7186, SHA256SUMS e694fbda 558/558)
- Freeze notice ~/cirlean_work/scratch/next3_chain/FREEZE_NOTICE_next31_e0b4d64.md (c27b8af3): all 18 announced sha256 values verify; MANIFEST_build.sha256 (01ad8503) verifies 1032/1032 files in ~/cirlean_frozen/next31_e0b4d64_20261030/.lake/build; all 10 ~/cirlean_work/deliver/*_next31/SHA256SUMS pass sha256sum -c.
- Source byte-identity: all 21 .lean source files across the 10 *_next31 bundles are byte-identical (cmp -s rc 0) to their *_next3 (7 bundles) and *_next3_v5 (3 bundles) counterparts (0 source or statement changes).
- Fresh Lean processes (statement/check_statement_and_axioms.out, rc = 0): CJReal.delete_forest : DeleteSpecTheirsP, parse_array_step : ParseArrayStepSpecP, and parse_object_step : ParseObjectStepSpecP typecheck against CycleSpecsP2N v5 and all 34 theorem names across the 10 bundles print subsets of [propext, Classical.choice, Quot.sound].
- Kernel replay (replay/, ulimit -v 32 GiB): 260/260 distinct modules in the union of RESOLUTION_next31.tsv (244 rows, 242 distinct module names) and the 19 compiled bundle modules pass per-module leancheck1lp.sh rc = 0 (pjobs_v3 N = 2); 10/10 root bundle modules pass leanchecker --fresh rc = 0 (95.5-151.1 s each); 0.422 core-h guarded.
- Final manifest hashes of checks/fhnext31-20261030T1834Z (2026-10-30T19:06:12Z): SUMMARY.md 125e368e, SHA256SUMS b9fe6829 (558/558).
- 2026-10-30T20:14:01Z FREEZE /home/user/fv_paper/freeze/paper_v2_20261030T2013Z (src/main.pdf f3aa397d, SHA256SUMS ea380948): + third-revision re-checks: T2 (checks/n3t2-20261030T171447Z d2b095d0; n3pkg25 4d0518f8), D2 (n3pkg25), equiv-lean (next3el 05b02e16, next3el2 409ec6c9), closures n3closure bfcf8509 + audit v60. Supersedes 1453Z.
- 2026-10-31T06:43:44Z FINAL FREEZE /home/user/fv_paper/freeze/paper_v2_20261031T0643Z (src/main.pdf 9acc5409, SHA256SUMS d9a5f7c5): + T3 at 7c73739 (checks/n3t3-20261031T053254Z ae35a49c; closure addendum 59e0fba1) + equiv-lean final recompile (next3el3 ce50862a) + audit v61. Supersedes 2013Z. Hard stop: no further work.
