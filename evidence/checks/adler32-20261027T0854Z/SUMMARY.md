RESULT: the zlib adler32 C -> safe Rust delivery (equiv-lean ff07aac) checks out: manifest 4269/4269 before and after; 2444 tracked files = ff07aac; the six main theorems compile from my copy, state what the report says, and with the 25 existing adler32 rows print exactly propext, Classical.choice, Quot.sound; the 323-module import closure passes the kernel replay (28 replayed rc 0, 295 reused); the C sources equal the pre-registration's zlib 1.3.1 copy; ClangIR, its Lean module and the Aeneas extraction regenerate identically; cirpun finds no access of another width; the native differential test reproduces (27,383 and 207,383 identical; the mutant fails on 73). The frozen scope is covered as stated, with C and Rust totality proved.

# Check of "zlib adler32, C -> safe Rust" (equiv-lean r7-final ff07aac)

Checked by a fork of the evidence owner, 2026-10-27 08:54Z-09:35Z (date -u). Check dir ~/fv_paper/evidence/checks/adler32-20261027T0854Z;
copies in ~/fv_paper/replay/adler32-20261027T0854Z (equivlean/ = rsync -rtL of the kit tree ~/equivlean_freeze_ff07aac-r7b without
.git/.tmp; equivlean_work/ = rsync -rtL of the four vendor packages and the Aeneas backend the lakefile names; 0 symlinks; hard
links became separate files). Every job ran under coreh_guard_v2 with logs in guard/ (62 jobs, 0.252 core-h in all).

## 1. Hashes and commits
- Manifest SHA256SUMS_ff07aac-r7b.txt (sha256 1b21658d0345f4c1..., 4269 lines, copy kit_SHA256SUMS_ff07aac-r7b.txt): sha256sum -c
  4269/4269 OK in the kit tree before (manifest_check_before.txt) and after (manifest_check_after.txt), and in my copy
  (manifest_check_copy.txt). No file in the kit tree is newer than my first check.
- Tracked files: git ls-tree -r ff07aac = 2444 files; git hash-object of each file in the tree = the blob of ff07aac, 2444/2444
  (tracked_vs_ff07aac.txt). The main repo ~/equivlean has no partial clone or promisor; git was run read-only with
  GIT_ALLOW_PROTOCOL=file.
- ff07aac vs master 9b15933: 34 added files + README.md modified, all adler32 (diff_9b15933_ff07aac.txt): 17 Lean modules
  (EquivLean/Demo/XLang/Adler32/*, Demo/Gen/Aeneas/Adler32Rs/{Types,Funs}, Demo/Gen/Cir/Adler32/Adler32), the C example dir and
  the Rust crate with its difftest.
- Against 751764f (the C-to-Rust study): the 15 EquivLean modules of the closure that are not new have the same source blobs
  (closure_src_vs_751764f.txt: 17 NEW, 15 SAME, 0 CHANGED), so no previously checked statement in the closure changed.

## 2. Statements (fresh process; stmt/stmt.out, stmt/defs.out, stmt/defs2.out)
- EquivOn Bad R f g := for all x, not Bad x -> Equiv R (f x) (g x); Equiv = simulation both ways in wp form (Core/Sim.lean:46, 176).
  Same (rust result, C exit): Rust returns Ok y and the C run exits with ret y; anything else is False.
- Inputs. ZInput = (adler : u64, buf : Option byte slice, len : usize); zLen = the slice length, or len when buf = none (Z_NULL).
  zRun = the Rust adler32_z(adler, buf, zLen); C.cRunZ = the C adler32_z on the program's initial memory with the slice as a
  read-only array of exactly its bytes (or Z_NULL) and length zLen. run32 / C.cRun32: adler32 with the length cast to u32 /
  taken mod 2^32. CbInput = (adler1 : u64, adler2 : u64, len2 : i64); cbRun, cb64Run vs C adler32_combine, adler32_combine64.
- adler32_z_equiv_explicit : EquivOn (zLong x or (buf = none and len = 1)) Same zRun C.cRunZ, zLong x := 2^28 <= zLen x.
  adler32_equiv_explicit: the same for adler32 (run32, C.cRun32).
- adler32_z_equiv / adler32_equiv : EquivOn (zLong x or CUB cRun x) Same ..., CUB := not Safe (the C run has undefined behaviour):
  the frozen form.
- adler32_combine_equiv / adler32_combine64_equiv : EquivOn cbLong Same ..., cbLong := False (every input).
- Totality, from the components: z_rspec, run32_rspec, cb_rspec, cb64_rspec : RSpec Long model run (on every input that is not
  Long, the Rust returns Ok y with y = the model's value: it never panics); C.cspec_z, C.cspec_32 : CSpec (when the C run returns,
  it returns the model's value); C.cub_z_iff, C.cub_32_iff : off zLong, CUB holds exactly on buf = none and len = 1;
  C.adler32_z_buf (Returns from any memory with the buffer as a read-only array of fewer than 2^28 bytes, the model's value, the
  caller's blocks unchanged), C.adler32_z_null (Returns 1 on Z_NULL with len != 1), C.adler32_z_null_one (no ok outcome on
  Z_NULL with len 1); C.ctotal_cb, C.ctotal_cb64 : CTotal (on every input the C run returns the model's combine).
- In words: for every adler and every buffer of fewer than 2^28 bytes, or Z_NULL with any length below 2^28 except 1, zlib's
  C adler32_z (and adler32) returns without undefined behaviour, the safe Rust translation never panics, and both return the
  same value; Z_NULL with length 1 is the one input below 2^28 where the C has undefined behaviour (it reads buf[0]). The
  combine functions agree on every input, both sides total.
- Against the frozen scope (DEVIATIONS 2026-10-27T01:14Z: functions adler32_z, adler32, adler32_combine64/adler32_combine;
  statement EquivOn Bad (Same ret) rustRun cRun, Bad = len >= 2^28 or C UB in cirlean; totality only if proved): covered as
  frozen (adler32_z_equiv, adler32_equiv, combine for all inputs), and C and Rust totality are proved (components above).

## 3. Compile, axioms, kernel replay
- The 17 new modules compiled from source in my copy (lean with the lakefile options, LEAN_PATH of the copy; scripts/compile_one.sh),
  in 6 dependency levels, all rc 0, no error or sorry line (compile/status.txt, compile/scan.tsv; CZ 483 s, CCombine 105 s, the
  rest under 11 s). My 17 oleans differ in bytes from the producer's (new_oleans_mine_vs_producer.txt; producer copies kept in
  replay/producer_oleans); the replay below is of mine.
- Axioms (axioms/ax.out, fresh process): all 25 existing adler32 rows of rows_r7_v3.txt print exactly [propext,
  Classical.choice, Quot.sound], adler32_combine__spec included (the kit's audit mis-marked it because of a file-name
  collision; equiv-lean's separate re-run audit_fix/ agrees). rows_r7_v3.txt lists 27 adler32 names; two, C.ctotal_z and
  C.ctotal_32, do not exist in the sources (unknown constant), which is why the report counts 25.
- Import closure of EquivLean.Demo.XLang.Adler32.Final (tools/closure_multi.py; closure_final.tsv): 323 modules (EquivLean 32,
  Aeneas 249, CIR 42; no Jimple, Cobol or StrictTS module). tools/delta_reuse.py against the R5 check's copy
  (replay/eqr5-20261026T2004Z, pass list = its 92 replayed + 248 validly reused modules): 295 reused (olean and closure
  byte-identical, passed there), 28 to replay (17 new; Core.Sim, whose olean bytes differ although its source is unchanged, and
  10 modules that import it) (delta_eqr5.*). Package pins equal R5's except JimpleLean, which is not in the closure
  (manifest_vs_eqr5.txt).
- leancheck1lp.sh on the 28: 28/28 rc 0 (replay/). Controls: BadCtl (a false theorem added with the kernel check skipped)
  rc 1, declaration type mismatch; GoodCtl rc 0 (replay_controls/).

## 4. Provenance
- adler32.c sha256 9cd1443a24ff2a30... = the frozen scope; adler32.c, zconf.h, zlib.h, zutil.h and LICENSE are byte-identical
  to the pre-registration's independent zlib 1.3.1 copy (~/fv_paper/prereg/D/src_zlib/zlib-1.3.1) and to equiv-lean's
  dl/zlib-v1.3.1. No upstream git copy is available locally (nothing external was fetched).
- ClangIR (scripts/regen_cir.sh, the commands of gen.sh: clang upstream-4955d32b -fclangir -O0 -D_LARGEFILE64_SOURCE=1
  -DHAVE_HIDDEN, cir2lean of my copy's cirlean 28e2380): adler32.cir and EquivLean/Demo/Gen/Cir/Adler32/Adler32.lean are
  identical to the delivered files once the embedded absolute source paths are normalized (regen/*.pathnorm); the only
  differences are those path strings.
- Aeneas (scripts/rustregen.sh, ~/equivlean_work/dl/rel/aeneas_bin = Aeneas fdebf20, nightly-2026-09-17, offline, on a copy of
  the crate): charon rc 0, aeneas rc 0; adler32_rs.llbc identical (sha256 bd91226133d97a23..., as in the crate README);
  Types.lean and Funs.lean identical (rustregen/result.txt).
- cirpun f365f63 (copy of checks/cirpun-20261025/tool, SHA256SUMS 10/10 OK; controls pos and neg PASS) on the regenerated
  adler32.cir with roots adler32_z, adler32, adler32_combine, adler32_combine64: closure 5 functions (with adler32_combine_),
  FLAG 0, CHAR 0, SIGN 0, AGG 0, NOOBJ 0, ASSUME 0, OK 412 (cirpun/). No memcpy or memmove in the IR.

## 5. Tests
- difftest/run.sh from my copy with ZLIB_DIR = the pre-registration's zlib copy (gcc 15.2.0 -O2 on the unmodified adler32.c,
  rustc/cargo 1.99.0 --release, overflow checks on): seed 20261027 N 20000: 27,383 cases, all identical (adler32_z 11,456,
  adler32 7,917, combine 4,057, combine64 3,953); seed 2 N 200000: 207,383 cases, all identical (difftest/).
- Mutant (mutant/: a copy of the crate with the len == 1 path's subtraction of BASE from the second sum replaced by % BASE,
  mutant.diff): FAIL, 73 of 27,383 cases differ (adler32_z 37, adler32 36), as reported.
- The model-vs-gcc validation (11,936 cases, ASan+UBSan clean) is described in the kit's README but its script is not in the
  frozen tree; not re-run. The model is in any case proved equal to both sides' code, so this test is supporting evidence only.

## 6. Size and cost
- Code lines (non-blank, outside comments; scripts/loc.awk; loc.tsv): model 157 (Model 45 + ModelLemmas 112), C 837 (CBase 63,
  CZ 454, CZSpec 153, CCombine 104, CCombineSpec 63), Rust 825 (RustBase 319, RustZ 279, RustCombine 86, RustSpec 141), glue 117
  (Equiv 57, Final 40, RustDefs 20): all four equal the report.
- Cost about $165 all-in: not checked (no transcripts named). The producer's 10.52 core-h is the whole 1826-module kit rebuild.

## Discrepancies and disclosures
- None in the delivery's claims. Minor: rows_r7_v3.txt names two rows that do not exist (C.ctotal_z, C.ctotal_32); the kit's
  RESULT.md says NOT GREEN only because of the audit-file collision for adler32_combine__spec, whose axioms are standard.
- The equivalence theorems speak about the C run from the program's initial memory with the buffer as a read-only array of
  exactly len bytes (cRunZ); the C contracts behind them (adler32_z_buf) hold from any memory.
- I ran one read-only command with the kit tree as working directory (git hash-object over its files; no writes; the manifest
  after the check is unchanged). In my copy only, I made the build directories of the new modules writable before compiling.
- Compute: 0.252 core-h over 62 guarded jobs (guard/). Nothing written outside my two directories.

Files: SUMMARY.md, SHA256SUMS, kit_SHA256SUMS_ff07aac-r7b.txt, manifest_check_{before,copy,after}.txt, tree_ff07aac.txt,
tracked_vs_ff07aac.txt, diff_9b15933_ff07aac.txt, tree_751764f.txt, closure_src_vs_751764f.txt, diff_751764f_ff07aac_CoreSim.txt,
closure_final.tsv, new_modules.txt, new_module_levels.tsv, compile/, new_oleans_mine_vs_producer.txt, stmt/, axioms/, pass_eqr5.txt,
delta_eqr5.*, manifest_vs_eqr5.txt, replay/, replay_controls/, regen/, rustregen/, cirpun/, difftest/, mutant/, loc.tsv,
scripts/, guard/, leanpath.txt.
