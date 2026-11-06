RESULT: CONFIRMED as a build of 5b7bf49 in the first check's sense (every module compiles from the committed source against the producer's final oleans, and the kernel accepts the result), with two reservations. Jsmn.CTok and Jsmn.CPrim now compile. All 74 modules the producer rebuilt for the fix, Jsmn.CString included (under 128 GiB, maxRSS 79.4 GiB), recompile to byte-identical .olean and .ilean files. TinyRegex.CCompile, which the fix did not rebuild, compiles under 128 GiB (4240 s) and matches the producer's olean up to auxiliary names. leanchecker passes on the 71 changed or downstream modules, and --fresh passes on the 6 roots. The 176 claimed statements are unchanged, and the 60 claimed theorems of the rebuilt groups use exactly propext, Classical.choice and Quot.sound. Reservation 1: the producer's build-order evidence was altered (16 .olean mtimes rewritten after the rebuild; by birth time, 12 modules were written before an import's final .olean), and its replay tables predate the final oleans; the final oleans are nevertheless what the commit compiles to. Reservation 2: oleans carried over from rounds before e1c9a85 reproduce only up to auxiliary names (23 of the 36 such modules rechecked: 20 equal up to auxiliaries, and Bridge.Cir.Congr, Bridge.Cir.Tactic and TinyRegex.Model also differ in non-auxiliary constants that name auxiliaries), so a from-scratch build of the commit with the lakefile options would not reproduce the producer's tree byte for byte.

# Delta re-check of equiv-lean unified-next3 at 5b7bf49 (parent e1c9a85; cirlean 7c73739, coblean 20261028T0109Z unchanged)
An agent of the evidence-owner session. Check dir /home/user/fv_paper/evidence/checks/next3el2-20261030T174813Z (stamp from date -u at
creation). This re-check builds on the first check T1 = checks/next3el-20261030T153456Z (SUMMARY.md 05b02e16). Every T1 file used here was
checked against T1's SHA256SUMS first (s2.out, genpost.out, s7.out, s9.out). Inputs were read only: the producer worktree ~/equivlean_wt_next3
(frozen for this check) and ~/equivlean/.git (git reads with GIT_ALLOW_PROTOCOL=file and no optional locks; no promisor, no remote),
~/equivlean_work/{vendor,dl,logs}, ~/cirlean_frozen/next3_7c73739_20261030, the next2 re-check copy C2, T1's directory, and T1's replay copy
(T1's control oleans and recompiled oleans). No copy was made. LEAN_PATH points at the producer's build (leanpath_prod.txt, which is T1's list
with T1's copy prefix mapped to /home/user/). Recompiled .olean and .ilean files were written only under this check's
recompile/lib and recompile_dl/lib.
Every script, Lean and leanchecker run, multi-file scan and interpreter run was one job under coreh_guard_v2, launched through pjobs_v3
(450 150 2). At most 8 Lean jobs ran at once, with LEAN_NUM_THREADS=1 and ulimit -v 32 GiB. Jsmn.CString and TinyRegex.CCompile ran under
ulimit -v 128 GiB, each alone; free -g showed 408 GB and 405 GB available just before them.

## 1. Commit and files: PASS
- HEAD = 5b7bf492e0c08028ad7062dbf04e5d4e9dcc340c (refs/heads/unified-next3), a single parent e1c9a855571c925b7c561670a516fd68b34d6e9d (e1c9a85), whose own parent is fac6c38f7a5d5b8d199f808a8a2fbb27e1cfdb95
  (fac6c38). Committed 2026-10-30T16:58:59Z. Subject: "Jsmn/CTok, CPrim: guard simp only [Mem.endScope] with try after cir_hrun_c".
- ~/equivlean/.git: 0 remote or partial-clone config lines, 0 .promisor packs, no alternates, 0 remotes.
- Tracked files: commit 2893, worktree 2893, diff 0 bytes. Untracked and not ignored: 0. Index vs commit: 0
  paths. Ignored: .lake/.
- Delta e1c9a85..5b7bf49: two files changed (Jsmn/CPrim.lean 3 lines, Jsmn/CTok.lean 2 lines), as 5 one-line hunks at CTok.lean 81 and 99
  and CPrim.lean 231, 253 and 265. Each hunk keeps its line number. Each new line is the old line with "by simp only [Mem.endScope]; omega"
  replaced once by "by (try simp only [Mem.endScope]); omega". No other line changes. The commit blob lists differ only in these two files.
  Delta patch sha256 b1127909bc33b0e8fd0ccac1f709d485a84afb981a25d3b0d93cad2652914e65.
- The producer's patch next3_adaptation.patch (both copies) is identical to a recomputed git diff fac6c38 5b7bf49, sha256 86beb0b79d247198e85fd85f6e4052c44dc663368f20dc221574327a3fb0a1c9 (the
  value the REPORT announces). It touches 34 files (1 added, 33 modified, 32 .lean), the same file list as the e1c9a85 patch.
- Forbidden tokens (T1's list: sorry, admit, native_decide, axiom, extern, implemented_by, unsafe, ofReduceBool, skipKernelTC, decide +kernel,
  kernel := true; word match): 0 hits in the 32 changed .lean files at 5b7bf49, 0 in the delta's added lines, and 0 in the added lines of
  fac6c38..5b7bf49. The only substring hit is 'extern' inside 'external', 16 times.
- Pins are unchanged: lakefile.toml and lake-manifest.json differ by 0 bytes over the delta. vendor/cirlean-7c73739 equals the frozen tree
  (diff -rq: 0 lines), and its .lake/build matches the cirlean freeze manifest (1017 entries, 0 failures). The coblean, strictts, JimpleLean and
  aeneas trees equal the C2 copies (diff -rq: 0 lines each).
- Producer artifacts: REPORT_next3.md sha256 51a4c8149b103098280dd4e2e74611cde4675544544de1384d5950d09c74807b (both copies identical); build_next3_clean_all.log fbc58fdd5d1c0aa34c1fea0caa198c094d3a55894c7e6dd56057a9c14a9777c1 (both copies);
  leanchecker_per_module_next3.tsv 32e104c269ce8606fc6c0b73d6a4d25e10778a83cfcd4f98794d2efda15360d0. All 9 sha256 values written in the REPORT match their files (s1.out).

## 2. Statements: all 176 claimed statements unchanged from e1c9a85
- Olean delta since T1 (s2): 30907 olean files hashed now with T1's file selection. 66 .olean files changed (all in EquivLean: Musl 7,
  Thrift.Cpp 14, Adler32 5, Jsmn 28, TinyRegex 12). 0 files are new, 0 gone, and no .server or .private part changed. The toolchain olean
  list and binaries are as in T1.
- 116 claimed theorems lie in modules whose .olean is byte-identical to e1c9a85's. None of those modules imports a changed module (s3: the only
  closure modules with an unchanged .olean that import a changed module are Adler32.Final, Jsmn.Equiv, Jsmn.Final, Jsmn.RustGlue and
  TinyRegex.Final). So their statements and definition closures are unchanged.
- The other 60 claimed theorems lie in the five groups that hold every changed module (Musl, Thrift.Cpp, Adler32, Jsmn, TinyRegex). T1's dump
  sources N__CM, N__CT, N__XA, N__XJ and N__XT were re-run against the final oleans (s7):
  - Text and type hash are identical for all 60.
  - Statement-dependency hashes are identical for 57. For 3 (Jsmn.Rust.rust_spec, Jsmn.rust_rspec, Jsmn.C.jsmn_parse_pspec) they differ only
    through Jsmn.step, parse and mainLoop and their matcher, step.match_3 at e1c9a85 and step.match_2 now. The fix rebuilt Jsmn.Model, whose
    constants now equal next2's (OleanCmp3 against C2: consts_equal) and differ from the e1c9a85 olean in exactly those constants.
  - jsmn_parse_primitive_pspec: identical text, type hash and dependencies.
- All 1054 theorems of the five groups have identical text. 4 non-claimed lemmas get another type hash, from renumbered auxiliaries in their
  types: Musl.holds_evalBlock_zero_nil_elim, Jsmn.C.holds_evalBlock_at_elim, TinyRegex.C.mp_step and mp_nomatch. T1 saw the same kind of
  change (holds_* elimination lemmas, mp_step, mp_nomatch) between fac6c38 and e1c9a85.
- Definition closures (T1's closure dump N__C over the 60 claimed C-side statements, s9): 57 are identical to e1c9a85's. The 3 above differ by
  the 4 Jsmn.Model constants only. Against fac6c38 (s9b), the closures of rust_spec and rust_rspec are now identical to next2's. TinyRegex
  re_compile_eq and re_match_spec still differ from next2's by compStep's renumbered matcher, because TinyRegex.Model was not rebuilt.

## 3. Recompile from the committed sources against the producer's final oleans
Method (recompile_v2.sh, one module per job; recompile_v3.sh, the same plus GNU time, for Jsmn.CString and TinyRegex.CCompile): the source is the worktree file (= the 5b7bf49 blob, item 1), cwd is the worktree root, and the
command is lean -R <root> -DautoImplicit=false -DrelaxedAutoImplicit=false -DElab.async=false (T1's command and the one the REPORT gives), with
-o and -i writing into this check's recompile/lib and LEAN_PATH = the producer's final oleans. Each result was compared with the producer's
.olean and .ilean by bytes (cmp), then by declarations (T1's OleanCmp3). Controls passed: the producer's olean against itself gives
consts_equal, and an olean of another module gives differ.
- Wave A, 73 modules: CTok (rc 0, 21 s); CPrim (rc 0, 114 s); the other 25 changed Jsmn modules; the 3 Jsmn modules the producer rebuilt to
  identical bytes (RustGlue, Equiv, Final); the 38 other changed modules (Musl 7, Thrift.Cpp 14, Adler32 5, TinyRegex 12); and 5 more rebuilt
  to identical bytes (Adler32 Equiv, Final, RustSpec; TinyRegex RustFinal, Final). All 73 rc 0. .olean bytes identical: 73. .ilean bytes
  identical: 73. OleanCmp3 consts_equal: 73 (s5_waveA.out). Wave A covers every module of T1's 44 rebuilt STALE_ORDER modules except
  Jsmn.CString (below) and Bridge.Cir.PtrLemmas (wave R).
- Jsmn.CString (128 GiB, alone): rc=0 in 810s; maxRSS 79.40 GiB, user 778.94 s, wall 810.30 s; .olean and .ilean: bytes_same, ilean_same; OleanCmp3: consts_equal.
- TinyRegex.CCompile (128 GiB, alone; its .olean was not rebuilt by the fix and is unchanged since T1, last written 13:07:30Z): rc=0 in 4240s; maxRSS 89.97 GiB, user 4162.80 s, wall 4240.08 s; .olean and .ilean: bytes_differ, ilean_same; OleanCmp3: equal_up_to_auxiliaries (common_differ=23 (non-aux 0, type 6; []); only_mine=1320 (non-aux 0: []); only_other=1320 (non-aux 0: [])).
- Wave R, 32 modules: the rest of T1's recompile set (all of it except wave A, Jsmn.CString, TinyRegex.CCompile and the 3 probe modules below). Their oleans and imports are unchanged since T1. Recompile: 32 of 32 rc=0; .olean bytes identical: 8, .ilean identical: 32; OleanCmp3: equal_up_to_auxiliaries 19, consts_equal 13. Not consts_equal: Bridge.Cir.Behaves (equal_up_to_auxiliaries), Bridge.Cir.Loops (equal_up_to_auxiliaries), Bridge.Cir.PtrArgs (equal_up_to_auxiliaries), Demo.XLang.TinyRegex.CBase (equal_up_to_auxiliaries), Demo.XLang.TinyRegex.CCharClass (equal_up_to_auxiliaries), Demo.XLang.TinyRegex.CCharClassModel (equal_up_to_auxiliaries), Demo.XLang.TinyRegex.CClass (equal_up_to_auxiliaries), Demo.XLang.TinyRegex.CCompileLemmas (equal_up_to_auxiliaries), Demo.XLang.TinyRegex.CHelpers (equal_up_to_auxiliaries), Demo.XLang.TinyRegex.CMeta (equal_up_to_auxiliaries), Demo.XLang.TinyRegex.COneCh (equal_up_to_auxiliaries), Demo.XLang.TinyRegex.CText (equal_up_to_auxiliaries), Demo.XLang.TinyRegex.ModelLemmas (equal_up_to_auxiliaries), Demo.XLang.TinyRegex.ModelRange (equal_up_to_auxiliaries), Demo.XLang.TinyRegex.RustBase (equal_up_to_auxiliaries), Demo.XLang.TinyRegex.RustCompile (equal_up_to_auxiliaries), Demo.XLang.TinyRegex.RustLeaves (equal_up_to_auxiliaries), Demo.XLang.TinyRegex.RustMatch (equal_up_to_auxiliaries), Demo.XLang.TinyRegex.RustTop (equal_up_to_auxiliaries); bytes identical among them: 0. Bridge.Cir.PtrLemmas: rc=0 1s, bytes_differ.
- Post-hoc probe, chosen after T1's declaration differences: Bridge.Cir.Congr, Bridge.Cir.Tactic and TinyRegex.Model, not rebuilt by the
  fix. Two compiles of each, both rc 0: the method above, and the producer's own scripts/lean1.sh command (cwd = root, relative file,
  no -R, --load-dynlib of the JimpleLean library, recompile_dl_v1.sh). The two compiles are consts_equal to each other (Tactic and Model also
  byte-identical). Both differ from the producer's oleans in the constants T1 listed (Congr: 7 non-auxiliary constants differ, plus one-sided
  auxiliaries 226/238; Tactic: 11, plus 49/51; Model: compStep, plus 1/1). This check's TinyRegex.Model olean is byte-identical to T1's
  recompile (fb1693c85c7063d5…), so the build path played no part. Neither command reproduces these 3 producer oleans.

## 4. Build order: the producer's evidence was altered after the rebuild
- The REPORT's "Clean Topological Rebuild" with "transitive_stale_rebuilt=0" rests on .olean mtimes. 16 .olean mtimes were rewritten after the
  rebuild (s3e scanned every file of the build dir, s3d the claimed closure; stat %w %y %z):
  - At ctime 2026-10-30T17:41:45Z the 14 Thrift.Cpp oleans (StringWrite, outside the claimed closure, among them) got whole-second mtimes 17:56:41 .. 17:56:54, in import order and in the future at
    that moment. At the same ctime, Bridge.Cir.ValSwap (written 14:39:06.92) got 14:38:50, which is earlier than its importer PtrLemmas
    (written 14:39:06.02).
  - At ctime 2026-10-30T17:42:45Z, Musl.MemcpyCex (written 17:28:16.47) got 17:20:30, earlier than its importers Memcpy (written 17:27:40) and
    MemcpyRefines (written 17:28:04).
- By .olean birth time, which is when each current .olean was written, 12 modules were written before a transitive import's final .olean:
  - Bridge.Cir.PtrLemmas, before ValSwap.
  - Musl.Memcpy and MemcpyRefines, before MemcpyCex.
  - Thrift.Cpp Varint, before Transport (17:09:28); VarintRead and VarintRead32, before Transport and ReadLemmas (17:39:46); FieldHeader,
    FieldRead, ListHeader, ListRead and NegSize, before Transport, ReadLemmas and Zigzag (17:40:07).
  - Jsmn.RustGlue, before Jsmn.Equiv (whose bytes did not change).
  The producer's clean logs show the same order: Memcpy before MemcpyCex; Bits, Varint and the others before Transport, ReadLemmas and Zigzag.
  So the rebuild was not in import order, and the zero comes from the rewritten mtimes.
- Effect on the final oleans: none found. The 11 of them in wave A recompile from the commit against the final imports to byte-identical .olean files, and leanchecker accepts them in the final environment (section 5). Bridge.Cir.PtrLemmas (olean and imports unchanged since T1; wave R) recompiles to an olean with equal declarations (consts_equal) but other bytes, like other oleans carried over from earlier rounds; T1's replay accepted it.
- The fix's oleans were written from 16:50:03Z to 17:41:35Z (birth times). The commit time is 16:58:59Z.

## 5. Kernel replay: PASS
- leanchecker, one process per module, on 71 modules: the 66 whose .olean changed since T1, plus the 5 closure modules with an unchanged
  .olean that import a changed module. Result: 71 of 71 rc 0 in 390.3 s; the longest was Adler32.CCombine at 50.9 s. Every other closure
  module has a byte-identical .olean and olean-import closure since T1, so T1's replay of the 2371-module closure carries over.
- leanchecker --fresh on the producer's 6 roots: 6 of 6 rc 0 (Musl.MemcpyCex 98.0 s, MemcpyFindings 101.4 s, MemcpyRefines 109.9 s,
  StrlenRefines 100.5 s, Adler32.CZSpec 261.2 s, EquivLean 82.0 s).
- Controls, using T1's control oleans: BadCtl rc 1, GoodCtl rc 0, StaleA rc 0, StaleB rc 1; with --fresh, BadCtl rc 1 and GoodCtl rc 0.
- The producer's tables do not cover the final oleans. leanchecker_per_module_next3.tsv was written at 17:02:43Z, before the final .olean of
  55 of these 71 modules. leanchecker_fresh_next3.tsv was written at 15:25:20Z, before the commit.

## 6. Axioms: PASS
- 32 fresh processes, one per claimed module of the five groups (T1's sources), covering 60 claimed theorems. Result: 60 of 60 use exactly
  [propext, Classical.choice, Quot.sound], as in T1. All 32 processes exited rc 0, with 0 error lines.
- Planted control Ctl3, in the environment of the rebuilt Jsmn.CPrim: the sorry plant reports sorryAx, the axiom plant reports plantedAxiom3,
  the native_decide plant reports plantedNative3._native.native_decide.ax_1, and jsmn_parse_primitive_pspec reports exactly the three.
- The other 116 claimed theorems' oleans are unchanged since T1, where 115 of them use exactly the three axioms and thrift_classes_length uses
  none.

## 7. Conclusion
- Answer: yes. In the first check's sense (each module compiles from the committed source against the producer's final oleans, and the kernel accepts the result), unified-next3 at 5b7bf49 is CONFIRMED as a build of the commit. The two modules that failed there (Jsmn.CTok, Jsmn.CPrim) now compile. The two it could not decide compile under 128 GiB: Jsmn.CString is byte-identical, and TinyRegex.CCompile is equal up to auxiliary names. Every module the fix rebuilt reproduces byte for byte, and the kernel accepts every changed .olean and the 6 roots.
- Reservation 1 (process): the REPORT's build-order claim does not hold as stated (section 4), and the replay tables it cites predate the final oleans (section 5). Neither changes the oleans, which this check recompiled and replayed itself.
- Reservation 2 (reproducibility): 23 oleans carried over from rounds before e1c9a85 are not what the committed sources compile to with the lakefile options. For the 3 probed modules, the producer's own lean1.sh command does not reproduce them either. They differ in auxiliary names, and in Bridge.Cir.Congr, Bridge.Cir.Tactic and TinyRegex.Model also in non-auxiliary constants that name those auxiliaries. They compile from the commit and the kernel accepts them, so the theorems stand, but the producer's tree is not a byte-reproducible build of 5b7bf49. Rebuilding those modules and their importers with the documented command would close this gap.
- Correction to this check's interim message to the lead: it gave 15 files with rewritten mtimes. The full scan (s3e) finds 16, because the 14 Thrift.Cpp files include StringWrite, which lies outside the claimed closure.

Wording for the paper (T1's two sentences, updated):
At the next3 pins (equiv-lean 5b7bf49: cirlean 7c73739, coblean 20261028T0109Z unchanged) the build proves all 176 claimed theorems with at
most the standard axioms, the kernel replay of their whole import closure and of the six --fresh roots passes, 171 statements print as at
next2, and the COBOL, TypeScript, Thrift Java/Rust and Rust-side statements keep their meaning (identical definition closures, 2 of them up to
a renumbered match auxiliary). The 50 C-side statements (musl, Thrift C++, Adler-32, jsmn, tiny-regex) are now statements about cirlean
7c73739's semantics (flat pointer addresses, typed byte access, pointer arithmetic in the pointee's units), and 5 of them change form:
musl_strlen_nonchar_ub, musl_memcpy_cex_ub, musl_memcpy_ne_model and jsmn_parse_primitive_pspec gain a hypothesis (char-array block, the
bound m.next < 2^29, concrete block types) and musl_strlen_aligned_ub restates its alignment hypothesis on flat addresses.
Changes from T1's wording: e1c9a85 becomes 5b7bf49; "the producer's build" becomes "the build", because every module the fix rebuilt now
reproduces from the commit (section 3); "4 of them" becomes "2 of them", because the rebuilt Jsmn.Model made the two jsmn Rust-side closures
identical to next2's again; and T1's caveat sentence about Jsmn.CPrim and Jsmn.CTok is dropped, because both now compile from the commit. If the
paper says the build is reproducible, it should add that oleans carried over from earlier rounds reproduce only up to auxiliary names
(section 3: TinyRegex.CCompile, wave R and the probe).

## Notes on the producer's report (REPORT_next3.md, sha256 51a4c8149b103098…)
- Confirmed: the commit, the patch hash, the 5-line delta, the statement changes (including the corrected old hypothesis of
  musl_strlen_aligned_ub, (i + 1) % 8 = 0, and the three Bridge.Cir lemmas), and the count of EquivLean oleans byte-identical to C2 (1587
  identical, 632 different, 1 new).
- "Clean Topological Rebuild ... transitive_stale_rebuilt=0": not supported. The rebuild was not in import order, and the zero rests on 16
  mtimes rewritten after the rebuild (section 4). The final oleans of the rebuilt modules are still reproduced byte for byte (section 3).
- "207/207 per-module replay, covering all 633 rebuilt .olean files" and "6/6 --fresh": these tables predate the final oleans and the commit
  (section 5). This check's replays of the final oleans pass.
- Memory: the REPORT gives Jsmn.CString maxRSS 79.37 GiB in 930 s, and TinyRegex.CCompile 4263 s under 128 GiB. Measured here: Jsmn.CString maxRSS 79.40 GiB, user 778.94 s; TinyRegex.CCompile maxRSS 89.97 GiB, user 4162.80 s (GNU time).
- The REPORT does not say that TinyRegex.CCompile was not rebuilt. Its .olean is unchanged since T1.

## Limits
(i) Each recompile uses the producer's final oleans of its imports; no from-scratch rebuild of the commit was run. Of the oleans carried over
    from rounds before e1c9a85, only the 36 modules of T1's recompile set outside the fix were recompiled again (wave R, the probe and TinyRegex.CCompile). The 515 rebuilt generated
    Demo.Gen modules were not recompiled, as in T1.
(ii) Kernel replay here covers the 71 changed or downstream modules and the 6 --fresh roots. The rest of the closure carries T1's replay, since
    those oleans and import closures are byte-identical.
(iii) Statement comparisons use pretty-printed text and Lean Expr hashes; renumbered auxiliaries count as changes.
(iv) Birth times are the file-system creation times of the current .olean inodes (stat %w). They date each .olean's current content if
    Lean writes every .olean as a new file; every changed .olean has its birth inside the rebuild window.
(v) The probe (section 3) and the birth-time analysis (section 4) were chosen after seeing the data; they are labelled post hoc.
(vi) Bare-shell use was single-file reads, mkdir, heredoc writes of scripts and command files, progress appends, one awk that split
    cmds_wave2.txt, one read-only progress tally that read two of this check's own files at once, and a few read-only stat and ls calls that read the metadata of several producer or check files at once.

## Cost
Guarded jobs: 265, 2.892 core-h in total (guard_core_s.tsv, cost.out), against a budget of about 3.5 core-h.
- Recompiles: 110 jobs, 2.459 core-h, including Jsmn.CString at 0.225 and TinyRegex.CCompile at 1.178.
- Per-module leanchecker: 71 jobs, 0.113. --fresh: 6 jobs, 0.209, plus 2 controls at 0.029.
- Statement and closure dumps: 6 jobs, 0.028. Axioms: 33 jobs, 0.009. Probe compiles with the lean1.sh command: 3 jobs, 0.024.
- All other jobs together: about 0.02.
The cost job read its own guard log while it ran. The summary, template and SHA256SUMS jobs that ran after it are not counted.

## Files
s1/ (commit, delta, patch, tokens, pins, producer artifacts), s2/ (olean hashes now, delta against T1 and C2, toolchain, symlinks),
s3/ (LEAN_PATH, closure module list, import lists from the olean headers, a whole-closure mtime test superseded by s3b), s3b/ (mtime
order in the rebuilt set), s3c/ (birth order on rebuilt imports, superseded by s3d), s3d/ (birth order over all imports, metadata flags), s3e/ (metadata scan of every file of the build dir),
recompile/ (lib, out, status.txt), recompile_dl/ (probe), s5/ (waveA, waveR, big, probe), s5_models_vs_c2.out, replay/,
replay_controls/, replay_fresh/, replay_fresh_controls/, s6/, stmt/, s7/, clos/, s9/, s9b.out, axioms/, s8/, scripts/, cmds_*.txt,
pjobs_*.log, guard/, guard_core_s.tsv, *.out, summary_manual_v*.txt and .tsv and summary_values*.tsv (summary inputs), SUMMARY_v1_superseded.md (first generation, superseded by this file). Never run: scripts/s9_clos_v1.sh (superseded by v2), scripts/mk_summary_v1.sh and
scripts/summary_template_v1.md (superseded by v2; v3 to v7 are v2 with the literal corrections made by mk_template_v3.sh to mk_template_v7.sh, and SUMMARY.md comes from v7), cmds_cstring.txt and cmds_ccompile.txt (superseded by the _v3 command files).
SHA256SUMS lists every file except itself and the files of the job that writes it.

Written 2026-10-30T19:55:26Z (date -u).
