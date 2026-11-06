RESULT: R7 agrees with the delivery. 613c77c = 2343/2343 tracked files; 85c9806 = the 53 Term files of T4Term-20261026T0955Z
(ad16b0c9...); 68/68 totals have the stated form and premises (61 with the conclusion of their partial theorem, 7 checked
for form); axioms std for the 82 named rows and all 185 public Term theorems, no sorryAx; kernel replay of the 1898-module
union closure: 868 replayed rc 0 + 1030 reused, 0 uncovered. No discrepancy; two documentation notes (9 totals missing from
README's table; rv64_total is stated for rv64SpecI). Questions for producers: none.

## R7: T4 Java column, total correctness (equiv-lean t4-java-total 613c77ccf4eb; checks/eqt4jt-20261026T2003Z; copy replay/eqt4jt-20261026T2003Z; fork of the evidence owner, 2026-10-26)
- Copy: cp -al of the equiv-lean maintainer session's clean-build worktree ~/equivlean_freeze_613c77c-t4jt (all build files dated 10:12-12:15Z, inside the
  build window; none later) plus full copies of equivlean_work/vendor/{cirlean-28e2380, strictts-a15926a,
  coblean-20261024T2306Z, JimpleLean-20261025T2312Z} and dl/aeneas. 30 symlinks, all relative and inside the copy.
  LEAN_PATH: leanpath2.txt (14 dirs; Cli is not built in this tree and is not needed).
- Tracked files: 2343/2343 blob ids = 613c77c (tracked_vs_head.txt empty). Commits on 2786c8f: 85c9806 adds exactly 53
  files, all EquivLean/Demo/Thrift/Java/Term/*.lean, and they equal T4Term-20261026T0955Z's package SHA256SUMS (ad16b0c9...,
  53/53 OK; the snapshot's SNAPSHOT_SUMS 9acf5fc8... verifies, 179 files); 613c77c changes only ROWS.md and README.md.
  ac65118 -> 613c77c: inside Thrift only Java/ZzB.lean (proofs of uzz32_body/uzz64_body: closer uzz32_goal -> uzz32_val
  and maxRecDepth 100000; statements unchanged), ROWS.md and the 53 Term files; the other 181 added + 35 modified files are
  java-total's (9f0e5fb -> 613c77c: 1021 added = 968 T4 + 53 Term, 1 modified = README.md).
- Packages: lake-manifest = the eqt4 copy's except JimpleLean 0149Z -> 2312Z; Mathlib.olean identical; olean counts of the 8
  unfollowed packages equal. Vendor cirlean/strictts/coblean copies = the eqt4 copy (diff -rq empty), JimpleLean 2312Z =
  the eqjt copy; aeneas = the eqt4 copy apart from two dangling symlinks present in both (doc.html, src/charon).
- JimpleLean 2312Z: snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z SHA256SUMS c1808513... 144/144 OK in
  the vendor copy (all 86 vendor .lean files covered); tools/modernize/import_jl.py --check (JL_DST = the copy): 36/36 same.
- 1764 EquivLean sources + the root = 1765 modules, each with its .olean (= the equiv-lean maintainer session's 1765/1765).
- README/ROWS: ROWS.md now lists NoRedeclL for rlb_uuid / rlb_exNegSize and thrift_coll_hyps as Contains, NoRedeclL,
  NoRedeclS, NoRedeclW (the gap found in the ac65118 check is fixed) and the 8 row totals with their premises. README's new
  table names 59 totals, all declared in the package; 9 package totals are not in that table (gtt_total, rb_total,
  rfiA_total, uzz32_total, uzz64_total, wbd_total, wi16A_total, zz32_total, zz64_total: contracts of callees).
- Statements (stmt/stmt_all.lean + stmt/stmt_special.lean, a Lean meta check in a fresh process, reducible-transparency
  unification): 68/68 *_total declared = STATEMENTS.tsv (90 rows = 68 _total + 22 _term). Every total has the form
  forall xs, (exists o, MExec P m args s o) /\ forall o, MExec P m args s o -> C, with the existential's body = the run
  hypothesis. 61 of 68: C unifies with the conclusion of the partial theorem (42 E/D/M theorems by name; 19 method
  contracts <m>_sat / <m>A_sat / rfb_sat' / wi16_sat after unfolding Sat), every hypothesis of the partial theorem is a
  binder of the total (its run hypothesis = the inner MExec), and the binders the partial theorem does not use are exactly
  the termination premises. 7 checked for form only: zz32/zz64/uzz32/uzz64_total (no named partial theorem; second
  conjunct by BodyVCP.sat of the frozen VC; premises Contains + the spec's pre only); rv64_total (stated for rv64SpecI =
  rv64Spec's pre plus CPAtH and ClassOK, same post; a derived statement for the contract rv64Spec, stmtcheck_rv64_contract_total,
  elaborates with propext, Classical.choice, Quot.sound); rfiA_total and wi16A_total (partial rfiA_sat / wi16A_sat need
  Valid P (Gamma2 P R), obtained in the proof by valid_Gamma2 from Valid, NoRedecl x2).
  Termination premises per total = STATEMENTS.tsv for all 68: none 12 (zigzag, getTType, checkContainerReadLength),
  TransportTerm + BConc 15, TransportTerm + TConc 22, TransportTerm + TRepConc 19. The 8 row totals: conclusion = the frozen
  row theorem's, extra premises TransportTerm + TRepConc (W1, W2, R1, R2, R3, L1, agreement) and TransportTerm + TConc (V1/V2),
  as ROWS.md states.
- Source scan of the 53 files: no sorry, admit, axiom, native_decide, implemented_by, extern, unsafe, opaque; 44 hits are
  set_option maxRecDepth / maxHeartbeats.
- Axioms (tools/axcheck.py --leanpath, fresh process per module): the 82 named rows of the equiv-lean maintainer session's audit 81 exactly [propext,
  Classical.choice, Quot.sound] + thrift_classes_length with none; the 68 totals and 22 termination lemmas 90/90 exactly the
  three; all 185 public theorems of the 53 Term modules std (181 exactly the three, 2 propext only, 1 propext +
  Quot.sound, 1 none).
- Kernel replay: union import closure of the 53 Term modules and the modules of the 82 named rows (105 roots), 1898 modules
  (EquivLean 1537, Aeneas 249, Cobol 43, CIR 42, Jimple 27; union_closure.tsv). tools/delta_reuse.py against three earlier
  passing copies (eqt4-20261026T0559Z, eqjt-20261026T0209Z, eq-20261025T1449Z): 868 modules replayed with leanchecker
  (leancheck1lp.sh, LEAN_NUM_THREADS=1, ulimit -v 64 GiB, 2 lanes of 1 job), all rc 0 (slowest ThriftProgC 144.4 s,
  ThriftProg 75.4 s); 1030 reused (olean and whole closure byte-identical to a module that passed there: 888 eqt4, 104 eqjt,
  38 1449Z, first match in that order); closure_verdicts.tsv: 0 not covered. The 27 Jimple modules (JimpleLean 2312Z) reuse
  the eqjt replay (same 2312Z oleans); a module was reused only when its olean and whole closure were byte-identical.
- Size of the termination package: 53 files, 3,486 lines (2,921 lines that are neither blank nor -- comments; raw count, not
  proof_lines.py).
- The equiv-lean maintainer session's RESULT.md (copied, producer_run/): built 1765/1765, failed 0; audit headline 82/82 standard; sweep Demo+Test 5882
  (5874 + 8 Popcount bv_decide), Modernize 6618/6618, sorryAx 0. Not redone: the full sweep; checked here: the 82 named rows
  and every public theorem of the 53 Term modules.
- Cost (reported, not recomputed): the Java maintainer session ~$43 (session $31.82 + helper $10.70); the equiv-lean maintainer session's build 7.63 core-h. This check: about 1.05 core-h (guard logs: replays and axioms 1.04, the rest < 0.01).
- Disclosure: one `git status --porcelain` ran on the producer's worktree before I switched to `git --no-optional-locks`
  (it may refresh the worktree index's stat cache; no content change). All other git reads used --no-optional-locks.
- Disclosure 2: at 21:02Z one rm -f removed my own scratch file SUMMARY.tmp1 (an intermediate of this SUMMARY.md) in
  this check dir; the draft with open fields is kept as superseded_SUMMARY_draft_with_open_fields.txt.
