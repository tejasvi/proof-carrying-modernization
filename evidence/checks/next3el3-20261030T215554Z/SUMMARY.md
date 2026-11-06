RESULT: CONFIRMED. After the producer's final recompile (90 modules, 21:17:23Z to 21:48:05Z), equiv-lean unified-next3 is still commit 5b7bf49 and exactly the 53 .olean files the producer lists changed. leanchecker accepts the 53 changed modules and their 20 importers (73 of 73), --fresh accepts the 6 roots, the 26 claimed theorems in changed modules print exactly as before the recompile and use exactly propext, Classical.choice and Quot.sound, and all 15 sampled modules (Bridge.Cir.Tactic, Congr and PtrLemmas among them) recompile from the commit to byte-identical .olean and .ilean files. Reservation 2 closes for Congr and Tactic, and all 10 Bridge.Cir modules now reproduce byte for byte; it remains for the carried-over TinyRegex oleans the step did not rebuild. One correction to the producer's report: the recompile was not in strict import order for Bridge.Cir.Congr and Bridge.Cir.PtrArgs (outside the claimed closure, so outside the producer's X = 594), which were compiled before their imports Tactic and AutoCouple were rewritten; both still reproduce byte for byte, so the final oleans are unaffected. The paper paragraph needs no change.

# Final re-check of equiv-lean unified-next3 at 5b7bf49 after the producer's import-order recompile
An agent of the evidence-owner session. Check dir /home/user/fv_paper/evidence/checks/next3el3-20261030T215554Z (stamp from
date -u at creation). Predecessors: T1 = checks/next3el-20261030T153456Z (SUMMARY.md 05b02e16) and P2 = checks/next3el2-20261030T174813Z
(SUMMARY.md 409ec6c9); both hashes were recomputed, and every T1 and P2 file used here was checked against its SHA256SUMS first (P2: 20
files, T1: 45 files plus s2/C2_now_olean_sha256.txt; all OK). Inputs were read only: the worktree ~/equivlean_wt_next3, ~/equivlean/.git
(git reads with GIT_ALLOW_PROTOCOL=file, no lazy fetch, no optional locks, after a promisor and remote check), ~/equivlean_work/{logs,
vendor,dl}, T1's control oleans in the T1 replay copy, and the T1 and P2 directories. No copy of any tree was made. Lean and leanchecker
read the worktree in place with P2's LEAN_PATH (leanpath_prod.txt: the producer's roots). Recompiled .olean and .ilean files were written
only under this check's recompile/lib. Every script, Lean and leanchecker run, multi-file scan and interpreter run was one job under
coreh_guard_v2, launched through pjobs_v3 (450 150 2); at most 8 Lean jobs ran at once, with LEAN_NUM_THREADS=1 and ulimit -v 32 GiB.

## 1. Commit, files and the producer's artifacts: PASS
- HEAD = 5b7bf492e0c08028ad7062dbf04e5d4e9dcc340c (refs/heads/unified-next3), parent e1c9a855571c925b7c561670a516fd68b34d6e9d. ~/equivlean/.git:
  0 remote or partial-clone config lines, 0 .promisor packs, no alternates, 0 remotes.
- Tracked files: commit 2893, worktree 2893 (git hash-object), diff 0 bytes; the commit blob list is identical to P2's. Untracked and not
  ignored: 0. Index vs commit: 0 paths. Ignored: .lake/.
- Producer artifacts (sha256): rebuilt_old_vs_new_sha256.tsv 7c7a33cb3cbd012ac30e3543bf099f16cd5cdb3cbdcdeff14144382475a4b042;
  build_final_all.log d52621ef86757c3c98855be875a061fef5be5f588cbf434b7d487f2e3ff447e4 (both copies); birth_order_check_final.tsv
  e7813c91732cf90876fd216ba5732963768826362a8688140b6b2b113c2ca116; birth_order_summary_final.txt
  d6271ae94b2376542ce8853bc65e8db25bea1c241ee2d836122606a7f0f094ee; REPORT_next3.md 51e591b85d49773c106fa459b8c1979a0d6ba64e3ba58c0119f8da657a5ae1f7 (both
  copies). All match the brief, and the four sha256 values in the REPORT's Section 5 match their files.
- Olean hashes now (22:03:24Z to 22:03:42Z, P2's file selection, 30907 files) against P2's list of 17:57Z: same 30854, changed 53, new 0,
  gone 0. All 53 are .olean files in the EquivLean build dir; no .olean.server or .olean.private part changed.
- The producer's old/new table (90 rows: 53 bytes_differ, 37 bytes_identical): old = P2's recorded hash for 90 of 90, new = the current
  hash for 90 of 90, flags consistent for 90 of 90, and the bytes_differ set equals the 53 changed files. The 53: Bridge.Cir Behaves, Corr,
  Loops, Obs, ValSwap, PtrLemmas, Congr, PtrArgs, Tactic, AutoCouple (10); Demo.Cir StraightLine, EarlyExit, LoopRefactor, TwoLoops,
  BugFix, VectorLoop, AutoCouple, AutoEarlyExit, AutoBound, AutoCountBits, AutoVector, PtrArgs (12); Musl Strlen, StrlenRefines, MemcpyCex,
  Memcpy, MemcpyFindings (5); Adler32 CZ, CZSpec (2); TinyRegex CCharClassP, COneP, CMatchQ, CMatchS, CMatchP, CMatchPat, CReMatchp,
  CReMatch (8); XLang Point, VecSum (2); Jsmn CTok, CScan, CSearch, CPrim, CPStepA, CPStepDead, CPStepOpen, CStepClose, CStepComma,
  CStepPrim, CString, CPStepQuote, CPMain, CRun (14). The 37 byte-identical: the 14 Thrift.Cpp modules; Jsmn RustGlue, Equiv, Final,
  CBase, CModelFacts, CStrSpec, CPDefs, CPLemmas; Musl Partial, MemcpyRefines; Adler32 Equiv, CBase, CCombine, CCombineSpec, RustSpec,
  Final (Adler32 CZ and CZSpec changed); TinyRegex CPartial, CBridge, Equiv, Final; ReverseBits; Bridge.Registry; EquivLean.
- build_final_all.log: 90 rows, rc=0 for all, window 21:17:23Z to 21:48:05Z, the same module set as the table. It has no leanchecker
  lines, so the "inline leanchecker 90/90" has no record in the listed files; section 3 replaces it.
- End of check (s7): no file under the worktree, ~/equivlean_work/logs or the vendor pins has an mtime or ctime after 21:55:54Z, and the
  90 .olean files still have the hashes of 22:03Z.

## 2. Birth order (stat %W and %w): no stale module among those compiled in this tree; two out-of-order compiles outside the closure
Method: P2's s3d logic (s3d_birth_v2.py) in s2_graph_v1.py. The closure of the 176 claimed theorems, recomputed now from the 89 claimed
modules over import lists read from the current .olean headers, has 2371 modules and equals T1's closure_N; every closure module's import
list equals P2's of 18:00Z. stat read at 22:06:19Z; %W equals the whole seconds of %w for all 2634 entries (closure plus build dir).
STALE_BIRTH_ANY(M): some transitive import of M within the closure has a later .olean birth than M (by %w; the %W test uses whole seconds).
- P2's X (596): STALE_BIRTH_ANY 0 (by %w and by %W), META_LATER 0, BACKDATED 0, FUTURE_MTIME 0. The producer's X (594): 0, 0, 0, 0, as
  its summary says; its rows' birth, mtime and ctime equal stat now (594 of 594). The 68 closure modules of the 90: 0. The producer's X is
  P2's X without Bridge.Cir.Behaves and Bridge.Cir.PtrLemmas, whose new oleans are byte-identical to the next2 copy C2's; both are in order.
- Whole closure (2371): STALE_BIRTH_ANY 1207 by %w, 1012 by %W. All 1207 are .olean files carried over by copy: 236 Aeneas files born
  2026-10-23T18:41 and 971 files born 2026-10-28 (953 of them hard links). Each is byte-identical to C2's .olean, and none imports, within
  the closure, a module whose .olean differs from C2's (s6_c2_v2.py: 630 closure modules differ from C2, 1741 are identical; the 19
  identical modules that have a changed import are 9 CIR files of the frozen cirlean 7c73739 build and 10 EquivLean modules written in the
  final step, all in birth order). So these births record the copy order, not a compile order, and these oleans and their import closures
  are the next2 build's. Among the 630 closure modules whose .olean differs from C2's (589 written in this tree on 2026-10-30 and 41 CIR
  files of the frozen cirlean build, hard-linked the same day), STALE_BIRTH_ANY = 0.
- Metadata flags over the closure: META_LATER 1674, BACKDATED 266, FUTURE_MTIME 0. Every flagged file has ctime minute 2026-10-23T18:41
  (266), 2026-10-30T02:19 (1355) or 2026-10-30T02:40 (53): copies and hard links made before the next3 rebuild. No file with ctime after
  21:00Z is flagged; the 90 files have link count 1, and the files born at or after 21:00Z are exactly the 90.
- Build order of the 90 (log start and end, .olean births; graph over the closure and the build dir, 2634 modules): 669 pairs (M, I) with
  I a transitive import of M among the 90. In 666, I's .olean was born before M's logged start. Every .olean of the 90 was born inside its
  logged compile window. Three pairs fail:
  - Bridge.Cir.Congr (compiled 21:17:43 to 21:18:45, .olean born 21:18:41) imports Bridge.Cir.Tactic directly (compiled 21:19:27 to
    21:19:43, born 21:19:41).
  - Bridge.Cir.PtrArgs (compiled 21:19:19 to 21:19:24) imports AutoCouple (born 21:19:47) and Congr, and through them Tactic.
  So Congr and PtrArgs were compiled against the old Tactic (and, for PtrArgs, the old AutoCouple) .olean, and the REPORT's "strict
  topological import order" does not hold for them. With the closure and the build dir together, they are the 2 STALE_BIRTH_ANY modules
  among the 90. Both lie outside the claimed closure, which is why the producer's X misses them. Effect on the final oleans: none; both
  recompile from the commit against the final imports to byte-identical .olean and .ilean files (section 5), and leanchecker accepts both
  (section 3).

## 3. Kernel replay: PASS
- Replay set: the 53 changed modules plus every module that imports one of them, transitively, over the closure and the build dir: 73.
  The 20 importers (importers20.txt): TinyRegex CPartial, Equiv, Final; Musl Partial, MemcpyRefines; Adler32 Equiv, CBase, CCombine,
  CCombineSpec, RustSpec, Final; ReverseBits; Bridge.Registry; Jsmn CBase, CStrSpec, CPDefs, CPLemmas, Equiv, RustGlue, Final. All 73 are
  among the producer's 90. The other 17 of the 90 (EquivLean, the 14 Thrift.Cpp modules, Jsmn.CModelFacts, TinyRegex.CBridge) import no
  changed module and have .olean files byte-identical to P2's.
- leanchecker, one process per module (P2's leancheck1lp.sh): 73 of 73 rc 0, 408.9 s in total, longest Adler32.CCombine 52.0 s. Among
  them Congr rc 0 (36.9 s), PtrArgs, Tactic and AutoCouple rc 0.
- leanchecker --fresh on the producer's 6 roots: 6 of 6 rc 0 (Musl.MemcpyCex 98.5 s, MemcpyFindings 100.9 s, MemcpyRefines 111.7 s,
  StrlenRefines 98.1 s, Adler32.CZSpec 254.6 s, EquivLean 81.3 s).
- Controls (T1's control oleans, 6 of 6 equal to P2's recorded hashes): BadCtl rc 1, GoodCtl rc 0, StaleA rc 0, StaleB rc 1; with
  --fresh, BadCtl rc 1 and GoodCtl rc 0.
- Every other closure module has a byte-identical .olean and olean-import closure since P2, so T1's and P2's replays carry over.

## 4. Statements and axioms: PASS
- 26 claimed theorems lie in changed modules: Musl Memcpy 1, MemcpyCex 2, MemcpyFindings 3, Strlen 1, StrlenRefines 3; Adler32 CZ 3,
  CZSpec 7; Jsmn CPrim 1, CRun 1, CString 1; TinyRegex CMatchPat 1, CReMatch 1, CReMatchp 1. None lies in a changed Bridge.Cir,
  Demo.Cir (outside Musl), Point or VecSum module.
- T1's dump sources N__CM, N__XA, N__XJ and N__XT (whole groups) re-run against the final oleans: each output file is byte-identical to
  P2's dump of the same source at 5b7bf49 before the final recompile (65, 129, 263 and 429 theorems; rc 0, 0 errors). Per theorem
  (T1's stmt_compare_v3.awk): text, type hash and statement-dependency hashes are identical for all 886, so for the 26 claimed theorems in
  changed modules and for all 51 claimed theorems of the four groups.
- #print axioms in 32 fresh processes (T1's sources, one per claimed module of the Musl, Thrift.Cpp, Adler32, Jsmn and TinyRegex groups):
  all rc 0 with 0 error lines; 60 of 60 claimed theorems use exactly [propext, Classical.choice, Quot.sound], with the same verdicts and
  lists as P2; the 26 in changed modules are among them.
- Planted control Ctl4, in the environment of Adler32.CZSpec (rewritten with new bytes): the sorry plant reports sorryAx, the axiom plant
  plantedAxiom4, the native_decide plant plantedNative4._native.native_decide.ax_1, and cspec_z exactly the three standard axioms.

## 5. Reproducibility sample: 15 of 15 byte-identical
- Method (recompile_v1.sh = P2's recompile_v2.sh with this check's dir): the worktree source (= the 5b7bf49 blob), cwd = the worktree
  root, lean -R <root> -DautoImplicit=false -DrelaxedAutoImplicit=false -DElab.async=false, LEAN_PATH = the producer's final oleans,
  -o and -i into recompile/lib. Criterion fixed before the runs: .olean and .ilean bytes equal to the producer's current files; T1's
  OleanCmp3 (declaration compare) as the second reading.
- Modules: all 10 Bridge.Cir modules (Tactic, Congr and PtrLemmas as asked; PtrArgs added after the order finding of section 2, post hoc),
  Musl.MemcpyCex, Adler32.CZSpec, Jsmn.CPrim, TinyRegex.CReMatch and Demo.Cir.PtrArgs. Not CString or CCompile.
- Result: 15 of 15 rc 0; .olean bytes identical 15, .ilean bytes identical 15; OleanCmp3 consts_equal 15; controls: the producer's olean
  against itself consts_equal, against another module's differ. sha256 prefixes (mine = the producer's): Congr 9e9c5f2f91654055, Tactic
  85f196e9c08b4206, PtrLemmas 3f9dbd3ce1eecaa2, PtrArgs d34cf295b944243f.
- Reservation 2: closed for Bridge.Cir.Congr and Bridge.Cir.Tactic. All 10 Bridge.Cir modules now reproduce byte for byte, among them
  Behaves, Loops, PtrArgs and PtrLemmas, whose earlier oleans P2 found to differ in bytes from a recompile (Behaves, Loops and PtrArgs
  equal only up to auxiliary names). The reservation remains for the carried-over TinyRegex oleans that the final step did not rebuild and
  whose bytes are unchanged since P2: the 16 TinyRegex modules of P2's wave R and TinyRegex.CCompile (equal up to auxiliary names) and
  TinyRegex.Model (non-auxiliary constants that name auxiliaries differ).

## 6. Conclusion
- Confirmed. The final recompile changed exactly the 53 .olean files the producer lists, the commit and its tracked files are unchanged,
  and the claimed theorems' statements and axioms are as before. The kernel accepts every changed module, each of its importers and the 6
  roots. The 15 sampled modules reproduce from the commit byte for byte.
- Corrections to the REPORT's Section 5: (i) the "strict topological import order" does not hold for Bridge.Cir.Congr and
  Bridge.Cir.PtrArgs, compiled before the new Tactic and AutoCouple oleans; the final oleans are unaffected (section 5). (ii) The birth
  check over X = 594 leaves out modules outside the claimed closure (Congr and PtrArgs among them) and Bridge.Cir.Behaves and PtrLemmas;
  over the whole closure, 1207 modules have later-born imports, all of them copies of next2 oleans whose import closures are
  byte-identical to next2's. (iii) build_final_all.log records an rc per compile but no leanchecker result.
- Paper wording: no change. The paragraph in sec-trust.tex that starts "A further branch pins the third revision" claims that the 176
  theorems check with only the standard axioms, that all 2,371 modules of their closure pass a replay, and that 171 statements print as
  before; all three hold at the final oleans. It claims no byte-for-byte reproducibility. If the paper later claims it, it should add one
  sentence: "Recompiling the changed modules from the commit reproduces their object files byte for byte; object files carried over from
  earlier rounds for the tiny-regex example match only up to the names of auxiliary definitions."

## Limits
(i) Recompiles use the producer's final oleans of their imports; no from-scratch build was run. 15 of the 53 changed modules were
    recompiled here. The new bytes of the other 38 were not reproduced independently; they rest on the kernel replay (section 3) and the
    producer's compile log.
(ii) Birth times date an .olean's content only when Lean wrote it as a new inode. For copies and hard links they give the copy time; the
    comparison with C2 is what places the 1207 copied files.
(iii) Statement comparisons use pretty-printed text and Lean Expr hashes.
(iv) The log-order test, the C2 cross-tab and the choice of Bridge.Cir.PtrArgs for the recompile were made after seeing the birth data
    (post hoc).
(v) Bare-shell use: single-file reads (awk, grep, stat), mkdir, heredoc writes of scripts, command files and progress notes, with these
    exceptions: one bash -n syntax check of s1_v2.sh outside a guarded job (no execution; every later syntax check ran inside the guarded
    job); sha256sum of the two predecessor SUMMARYs together and of the five producer artifacts together; ls listings of the T1 and P2
    directories; status and version commands (hostname, date, nproc, load, free memory, tool versions); a few chained reads of this
    check's own logs and outputs while jobs ran; and two command-file writes chained with a pjobs launch or a log check (cmds_s5.txt,
    cmds_s6s7.txt).
(vi) Never run: scripts/s1_v1.sh (superseded by s1_v2.sh), scripts/summary_body_v1.md (superseded by v2, from which this file is made),
    cmds_s2.txt (superseded by cmds_s2_v2.txt), cmds_post.txt (its two lines ran as cmds_s5.txt and cmds_s6s7.txt). scripts/s6_c2_v1.py ran
    and stopped on a module name present in two C2 roots before writing anything; s6_c2_v2.py replaced it.

## Cost
Guarded jobs before the summary: 146, 0.511 core-h in total (guard_core_s.tsv and cost.out cover the first 145; the importer listing
after them took 0.000), against a budget of about 2 core-h: --fresh 6 jobs 0.207, per-module leanchecker 73 jobs 0.120, recompiles 15
jobs 0.110, statement dumps 4 jobs 0.020, fresh controls 2 jobs 0.030, s1 0.010, axioms 33 jobs 0.009, all others together about 0.004.
The cost job read its own guard log while it ran; the summary and SHA256SUMS job is not counted.

## Files
s1/ and s1.out (commit, files, artifacts, olean hashes, producer table), s2/ and s2.out (imports, closure, replay set, birth tables,
log order), s5/ and s5.out (recompile compare), s6/ and s6.out (replay, statements, axioms), c2.out and s6/c2_* (C2 cross-tab), s7/ and
s7.out (end-of-check scan), importers20.txt, recompile/ (lib, out, status.txt), replay/, replay_controls/, replay_fresh/,
replay_fresh_controls/, stmt/, axioms/, scripts/, cmds_*.txt, pjobs_*.log, guard/, guard_core_s.tsv, cost.out, genwave.out,
recompile_modules.txt, t1_control_oleans_check.txt, tools.sha256. SHA256SUMS lists every file except itself and the files of the job that
writes it.

Written 2026-10-30T22:24:33Z (date -u).
