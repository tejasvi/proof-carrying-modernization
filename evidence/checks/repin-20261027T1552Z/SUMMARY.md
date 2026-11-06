RESULT: equiv-lean int-trial 7e7f28d (cirlean e6ac99a, JimpleLean 2035Z) agrees with the delivery. Manifest 4236/4236 before, after and in our copy; tracked files 2419/2419 = 7e7f28d. The vendored cirlean equals the frozen e6ac99a pin (sources; 40/43 oleans, 3 rebuilt with other bytes and replayed); JimpleLean equals the 2035Z snapshot (146/146). The printed statements of re_match_equiv, jsmn_equiv and its C rows, the 9 Thrift C++ rows, the T4 Java totals and the nibble totals are byte-identical to the earlier checks'. The musl and tiny-regex-c C statements differ from a9c8e23 exactly as RESTATEMENTS.md lists. 108 of the 109 audit rows print exactly propext, Classical.choice, Quot.sound, and thrift_classes_length prints no axioms (= the producer's audit). Kernel replay of the 1751-module closure of the 88 rows that depend on the re-pins: 1399 replayed rc 0 + 352 reused; controls as expected. No discrepancy.

# equiv-lean int-trial 7e7f28d (re-pin to cirlean next e6ac99a + JimpleLean 20261026T2035Z): evidence check

Checked by an agent, a fork of the evidence owner (the evidence-owner session), 2026-10-27 15:52Z-17:35Z (date -u). Check dir: this directory.
Replay dir: ~/fv_paper/replay/repin-20261027T1552Z.
- {equivlean, equivlean_work} are `cp -rL` copies (symlinks followed, new inodes; 0 symlinks; 13 GB):
  - the kit tree ~/equivlean_freeze_7e7f28d-replay2, without its .git pointer, .tmp and .lake/tmp;
  - its path dependencies ~/equivlean_work/vendor/{cirlean-e6ac99a, JimpleLean-20261026T2035Z, coblean-20261024T2306Z,
    strictts-a15926a} and ~/equivlean_work/dl/aeneas/backends/lean;
  - the layout mirrors the lake manifest's ../equivlean_work.
- ctl/ holds the controls.

Inputs:
- commit 7e7f28d27477047e842d618b2524d6ef50715aba;
- kit run 7e7f28d-replay2-20261027T124828Z (GREEN; its RESULT.md and audit.json are copied here as producer_RESULT.md and
  producer_audit.json);
- SHA256SUMS_7e7f28d-replay2.txt (sha256 761b2bcb..., 4236 lines);
- RESTATEMENTS.md (sha256 0af3d22a8610f2ea..., the version of 15:53Z with the FINAL paragraph).

## 1. Hashes and pins
- Manifest: sha256sum -c 4236/4236 OK each time:
  - in the tree at 15:53Z (manifest_check_before.txt) and at 17:31Z (manifest_check_after.txt);
  - in our copy (manifest_check_copy.txt).
  The tree has no file with a write bit (the only match is a symlink).
- Tracked files: git hash-object of the 2419 tracked files equals the blob ids of 7e7f28d (tracked_hash_tree.txt, 0 differ).
  git was read-only: GIT_ALLOW_PROTOCOL=file, GIT_OPTIONAL_LOCKS=0; equivlean has no promisor or partial-clone setting.
- a9c8e23 (last checked: t4nib) -> 7e7f28d (git_log_*, namestatus_*, diffstat_*):
  - merges jl2035 8e47011, t4-java-nibbles a9c8e23 and cirnext-frozen-fix a9f829b, then e5e90be (memcpy proof only).
  - Lean files changed:
    - the 5 musl files and 12 TinyRegex files;
    - Thrift/Java/Term/Base.lean, which now imports Jimple.TermSplitX; Term/TermX.lean is deleted;
    - Jsmn/Final.lean and TinyRegex/Final.lean (docstrings only; diff_base_jsmnfinal_trxfinal.txt).
  - Also changed: lakefile.toml and lake-manifest.json (the two pins only; lake_manifest_vs_t4nib.diff), scripts/lean1.sh,
    examples/rust/regen.sh and docs.
- cirlean pin: sources = the frozen pin ~/cirlean_frozen/next_e6ac99a_20261027, which we checked in
  checks/cirnext-20261027T0143Z.
  - `diff -rq` without .lake and .git shows only the vendored copy's extra VENDORED.txt (pins_diff.txt).
  - Of its 43 oleans, 40 match the frozen build's MANIFEST_build.sha256 (825e6dc0...). CIR.Logic.CJTree, CIR.Logic.Loops
    and CIR.Tactic.Simprocs have other bytes from the same sources (cir_vendor_vs_frozen.tsv); all three are replayed
    rc 0 (section 4).
- JimpleLean pin: the vendored copy equals ~/jimplelean_work/snapshots/JimpleLean-20261026T2035Z (diff -rq empty), and
  that snapshot's SHA256SUMS gives 146/146 OK on our copy. None of our earlier checks covered 2035Z.
  - Against 2312Z, the pin of our R7 and t4nib checks (jl2312_vs_jl2035_*), 2035Z adds:
    - Jimple/TermSplitX.lean: equiv-lean's former Term/TermX.lean apart from the header comment and one docstring
      paragraph (TermX_vs_JL2035_TermSplitX.diff);
    - the lemma vterm_of_none, and a rewritten jcontract_term tactic, in Jimple/Termination.lean;
    - Examples/Caching/TermLink.lean.
  - No semantic definition changes.
- Other packages (mathlib, batteries, aesop, Qq, ...): byte-identical to the t4nib check's copy (pkgdiff_*.txt: only
  .git/index differs). Toolchain v4.35.0 everywhere.
- The 109 audit rows are t4nib's 108 with musl_memcpy_cex_run replaced by musl_memcpy_cex_ub, plus musl_strlen_aligned_ub
  (headline_108_vs_109.diff).

## 2. Statements (stmt/; one fresh lean process per file, -DElab.async=false, LEAN_NUM_THREADS=1)
Method. The earlier checks' own statement files were re-run unchanged on our copy and the outputs diffed with their
recorded outputs. Rows they did not print were printed by one file on our copy and on the earlier checks' copies, each
copy with its own LEAN_PATH: replay/t4nib (a9c8e23), replay/eqr5 (373874f) and replay/eq-20261025T1449Z (eqT, f8fc84c).

| result | file run on our copy | compared with | outcome |
|---|---|---|---|
| re_match_equiv | trx.lean: the statement, the 12 definitions it names, its axioms | the same file on the eqT, eqr5 and t4nib copies | byte-identical on all three |
| jsmn_equiv | eqr5's check_statement.lean: jsmn_equiv, 16 definitions, rust_spec, jsmn_parse_pspec, rust_rspec, axioms | eqr5's recorded output | identical; the recorded file has one more line, `rc=0`, from that check's runner (diff_rerun_eqr5.txt) |
| jsmn C rows | jsmn_c.lean: jsmn_equiv, jsmn_parse_pspec, parse_string_pspec, jsmn_parse_primitive_pspec | the same file on the eqr5 and t4nib copies | byte-identical |
| 9 Thrift C++ rows | eqt4's print_rows.lean: the named inputs, the C++/Java/Rust rows W1, W2, R1-R3, V1, V2, L1 and exNegSize, the NoRedecl corollaries | eqt4's recorded output | byte-identical, 67,344 bytes |
| T4 Java totals | eqt4jt's stmt_all.lean and stmt_special.lean | eqt4jt's recorded outputs | byte-identical, 9,712 and 1,992 bytes |
| nibble totals | t4nib's check10.lean: the 10 totals and their specs | t4nib's recorded output | byte-identical, 24,855 bytes |

These statements still name cirlean's evaluation. So re_match_equiv and jsmn_equiv cover the inputs on which the C run
has an outcome in cirlean e6ac99a. `CUB x` is `¬ Safe (cRun x)`, and for cirlean results `Safe r` is `∃ a, r = .ok a`
(the instBehavesRes print is identical on both copies). A run with a type-punned access has no outcome there.

tiny-regex-c C rows (trx_c.lean on our copy and on the t4nib copy; trx_c_norm_compare.txt):
- re_compile_spec, re_matchp_pspec and the contract MPC are identical once the one inserted premise is removed:
  `(∃ es tlen, typ = (CIR.Ty.int es 8).array tlen)` for re_compile_spec, `tyt = ...` for the other two.
- matchpattern_pspec (stated as MPC) and re_match_pspec are identical.
This is what RESTATEMENTS.md lists.

musl. We ran musl_new.lean on our copy and musl_old.lean on the t4nib copy, at cirlean 28e2380, and compared them
declaration by declaration with whitespace collapsed (musl_norm_compare.txt). The changes are exactly those that
RESTATEMENTS.md lists:
- musl_strlen_pspec and musl_strlen_refines gain `(∃ es tlen, ty = .array (.int es 8) tlen)`, and musl_memcpy_pspec
  gains the same premise for tys and for tyd. Apart from these premises, the three statements are identical.
- musl_memcpy_cex_run (conclusion: the destination ends as 1 2 3 4 0 0 0) is replaced by musl_memcpy_cex_ub. The
  hypotheses are the same; the conclusion is now `∀ r, evalCall ... ≠ .ok r`.
- musl_strlen_aligned_ub is new.
- Identical: musl_strlen_nonchar_ub, musl_memcpy_refines, musl_memcpy_ne_model, memcpy_model_cex, the helper definitions
  (hcount, WordFree, copyList, cpy, wysf, cexSrc, cexDst, mval) and the 6 MemcpyFindings theorems (findings.lean).
  musl_memcpy_refines also equals the eqmusl check's print once namespace and binder display are normalized.
- pholds is EquivLean.Cir.pholds: `pholds x K := ∀ a, x = .ok a → K a`, partial correctness; runs with UB or that diverge
  satisfy it.

What each musl theorem says at e6ac99a:
- musl_strlen_refines
  - Premises: block b is a char array (an 8-bit integer element type of either signedness) with fewer than 2^62
    elements; the memory is well-formed; cirlean's strlen model returns r on &b[i]; every character that the model reads
    is in -128..255.
  - Conclusion: if musl's strlen on &b[i] has an outcome, it has the model's return value; the blocks below m.next are as
    the model leaves them; m.next does not decrease.
  - It is partial: runs without an outcome satisfy it trivially. At e6ac99a such runs include every run from an 8-aligned
    start, by musl_strlen_aligned_ub. RESTATEMENTS.md and the docstrings say this holds for every run that reaches the
    word loop; no theorem states that for unaligned starts.
  - So the refinement has content only on byte-path runs: the NUL is found in the alignment loop, before the first
    8-aligned position. musl_strlen_pspec has the same form, with the result e - i for a string whose NUL is at e.
- musl_strlen_aligned_ub
  - Premises: a char array block of any length and contents; an index i with (i+1) % 8 = 0, which is an 8-aligned
    position in cirlean's pointer encoding.
  - Conclusion: `pholds (evalCall ctx "musl_strlen" [&b[i]] m) (fun _ => False)`. No run has an outcome (it is UB or
    diverges).
  - The proof steps through the empty alignment loop to the word loop's `*w`.
  - There is no premise about a NUL, so it covers every string start at an aligned position.
- musl_memcpy_pspec
  - Premises: both blocks are char arrays (new premises); the destination is writable; the blocks are distinct; the
    ranges are in bounds; lengths are below 2^62; each copied source element is a char value ysf j in -128..255; and
    `WordFree is id n`. WordFree means: after the head loop that aligns s to 4 (hcount), fewer than 4 bytes remain if d
    is then 4-aligned, and fewer than 32 otherwise. So the run skips both word loops.
  - Conclusion (partial): if musl's memcpy has an outcome, it returns dest; the destination holds
    copyList zs id (cpy (wysf ysf) is n), the n source characters modulo 256 from index id on; other blocks are
    unchanged.
- musl_memcpy_refines (statement unchanged)
  - Premises: char arrays of signedness ss and sd; the destination is writable; distinct blocks; in bounds; lengths below
    2^62; the model returns r; every source character is in -128..255, and in 0..127 when the destination is signed;
    WordFree.
  - Conclusion: every outcome of musl's memcpy equals the model's (return value and blocks). It is partial and covers
    byte-path runs only.
- musl_memcpy_cex_ub
  - Premises: source signed char[7] = 1..7; destination signed char[7] = zeros; the destination is writable; distinct
    blocks.
  - Conclusion: `memcpy(d, s, 7)` has no outcome (`≠ .ok r` for every r). The docstring gives the reason: after the
    3-byte head loop, the 4-byte word copy is a type-punned access.
- musl_memcpy_ne_model (statement unchanged)
  - On the same inputs, musl's result differs from cirlean's memcpy model, which copies 1..7 (memcpy_model_cex).
  - The proof now uses cex_ub: musl has no outcome. It used to use cex_run: different destination contents.

## 3. Axioms of the 109 audit rows (axioms/; one fresh process per group)
- Groups: Demo_Cir 11, Demo_XLang 15, Demo_Thrift 46, and one group per Modernize program: Cbact01c, 02c, 03c, 04c
  (restricted), 04c Every, Cbcus01c, Cbtrn01c, 02c, 03c, JL.
- Every file has rc 0 and no error. axparse.py writes axioms/axioms_rows.tsv:
  - 108 rows depend on exactly [propext, Classical.choice, Quot.sound];
  - EquivLean.Demo.Thrift.Java.thrift_classes_length depends on no axioms (decide).
  This is the producer's audit, 109/109 the same lists.
- The sweep's 8 known Popcount theorems are in EquivLean.Demo.Aeneas.Popcount:
  - popcount_swar_spec, popcount_spec, swar_step_toNat, popcount_equiv_swar, swar_step, and_sub_lt, swar_toNat_le and
    swar_le.
  - Besides the standard axioms, they use bv_decide's `<thm>._native.bv_decide.ax_N` axioms (axioms/popcount.out).
  - No audit row imports that module: it is not in the 1919-module closure of the 109 rows.

## 4. Kernel replay
- Closure:
  - tools/closure_multi.py over the prefixes EquivLean, Jimple, Aeneas, Cobol, CIR and StrictTS, starting from the 72
    modules of the 109 rows, gives 1919 modules (closure109.tsv).
  - scripts/affected.py (rows_affected.tsv) selects 88 rows: those whose closure holds a CIR or Jimple module, or a file
    that changed since a9c8e23. The other 21 are Rust-only: 8 CardDemo Rust, 4 tiny-regex-c Rust, 8 Thrift Rust and jsmn
    Rust.rust_spec.
  - The union of the 88 closures has 1751 modules: 1388 EquivLean, 249 Aeneas, 43 Cobol, 43 CIR and 28 Jimple
    (closure_affected.tsv).
- Reuse: tools/delta_reuse.py against the four earlier copies that still hold oleans, each with its check's passing
  modules (replayed rc 0 or validly reused):
  - t4nib (111 passing) gave 25 reused, eqr5 (340) gave 260, eqT (962) gave 67, eqmusl (9) gave 0;
  - the union is 352 reused, 1399 to replay (delta/).
  A module is reused only when its olean and its whole closure are byte-identical to one that passed. The packages
  outside these prefixes are identical to the t4nib copy (section 1).
- Replay: tools/leancheck1lp.sh with our copy's LEAN_PATH (leanpath.txt); one core per job, two lanes (pjobs_v3); each job
  under its own guard (0.5 core-h, ulimit -v 128 GiB).
  - Result: 1399/1399 rc 0 (replay/*.tsv, replay_results.tsv); sum 5,938 s; largest
    EquivLean.Demo.Gen.Cir.Thrift.ProtoTT, 336 s.
  - Replayed by module: 1353 EquivLean, 41 CIR, 4 Jimple (Jimple, TermSplit, TermSplitX, Termination), 1 Cobol.
  - These include: the 6 musl proof modules (Memcpy 25.9 s); TinyRegex.Final; Jsmn.Final; Thrift.Java.Term.Base; and the
    3 CIR modules whose oleans differ from the frozen build.
  - Coverage: 1751/1751 modules of the affected closure are replayed rc 0 or reused (uncovered_mods.txt is empty).
- Controls (replay_controls/, compiled here):
  - BadCtl, a false theorem added with the kernel check skipped: rc 1, "(kernel) declaration type mismatch";
  - GoodCtl: rc 0.

## 5. Cost
- This check: 1.816 core-h metered.
  - 1.798 in guard/ALL_pjobs.log: the overall guard (cap 3.2) over all 1429 queued jobs, each also under its own guard;
  - 0.018 in 17 standalone guarded steps: copy 0.005, hash checks 0.005, delta 0.002, follow-up statements 0.003,
    manifest after 0.003, the rest under 0.001.
  - Not metered (about 0.005 core-h): the first hash steps and three one-line JSON reads (section 6).
- Producer: kit run 7e7f28d-replay2, 1818/1818 modules, 11.73 core-h (producer_RESULT.md).

## 6. Discrepancies and disclosures
Discrepancies: none.

Notes:
1. Three vendored cirlean oleans (CJTree, Loops, Simprocs) are not byte-identical to the frozen build; their sources are
   identical. All three replay rc 0.
2. No earlier check covered JimpleLean 2035Z. Its changes from 2312Z are listed in section 1; equiv-lean's Term/TermX.lean
   moved there unchanged as Jimple.TermSplitX.
3. RESTATEMENTS.md was edited at 15:53Z, after the delivery (FINAL paragraph). We used that version (sha256 above).
4. The two musl statement files exit rc 1 because of one line of ours: `#print EquivLean.pholds`. The name is
   EquivLean.Cir.pholds; trx_c.out prints it. Every other line printed.
5. The unchanged texts of re_match_equiv and jsmn_equiv now speak about cirlean e6ac99a's semantics (section 2).

Disclosures:
- The Write tool refuses report files from a subagent, so this SUMMARY.md was written with a shell heredoc, as the task
  asks.
- Run without the core-hour guard (each under 20 s): the manifest check before, the git hash-object of the tracked files,
  the pins diff, and three python one-liners reading JSON (audit.json, lake-manifest.json).
- Nothing was written outside our two directories. git was used read-only, no lake was run anywhere, and the producer
  tree was only read.
