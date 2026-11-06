RESULT: cirlean next e6ac99a passes the check: the records, the build manifest, the merge history and every regression re-run from a copy of the frozen build match the records. 20 Examples statements gain element-type premises exactly as CHANGES_punning2.md lists, and the census matches the record. No discrepancy found.

Pin: cirlean `next` e6ac99a09c75d3cc38bd7da4a3a5eabbdaa551cb. Frozen build: ~/cirlean_frozen/next_e6ac99a_20261027. Records:
~/cirlean_work/deliver/next_e6ac99a (copied to records/). Checked by worker an agent on 2026-10-27, 01:43Z-02:10Z.
Check dir: ~/fv_paper/evidence/checks/cirnext-20261027T0143Z. Replay dir: ~/fv_paper/replay/cirnext-20261027T0143Z.

## 1. Records and build
- records/SHA256SUMS (26090a47...): 15/15 OK.
- MANIFEST_build.sha256 (825e6dc0...): 126/126 OK against the frozen build (123 oleans + cirrun, cirscan, cir2lean).
  Of the 1134 files in .lake/build, none is writable. HEAD is e6ac99a and the worktree is clean.
- Copy for the re-runs: replay/.../next (608M, no symlinks). `diff -rq` against the frozen tree is empty
  (copy_identity_diff.txt). The copy's cirrun 232b7a0d..., cirscan 7357b267... and cir2lean 768ed51d... match the manifest.

## 2. Merges
- First-parent history (git_first_parent.txt), 8 steps above 2f90781:
  - merges: fuzzer266 c4ef58d (341c706), punning2 cbbf0b7 (8d6fcec), hexfp af0c0d4 (7a07bf0), ilp32 e00113f (58d01b8);
  - direct commits: d8afb97 (difftest punning regressions) and c674a7b (VCG simproc reducePtrBytes);
  - unionpun merged twice: 6653cbe (c688d91), then ad01e8e (e6ac99a).
- Per-step shortstats (git_shortstat_steps.txt) and totals match MERGES_AND_DIFFSTATS.txt (6f22f88a...).
- Files changed vs c4ef58d (the FH pin): 36, listed in files_vs_c4ef58d.txt.
  - 16 CIR semantics, front-end and tactic files;
  - 12 Examples files;
  - 6 tests/difftest files;
  - CHANGES_punning2.md and HANDOFF_20261023.md.
- Files changed vs 28e2380 (equiv-lean's pin): 41, listed in files_vs_28e2380.txt. These are the same 36 plus CIR.lean,
  CIR/Tactic/Call.lean, CIR/Tactic/Options.lean, tests/difftest/cases.txt and tests/difftest/clib.cpp (the fuzzer266 changes).

## 3. Regressions, re-run from the copy
The runner copies differ from the originals only in their scratch paths (ilp32/run_mine_vs_run_v1.diff; run_mine.sh
changes only W=).
| set | re-run at e6ac99a | vs record | vs c4ef58d |
|---|---|---|---|
| C++ cases | 177 MATCH + 1 UB (t_gap_emplace) | equal | all 178 per-case lines identical to cases_c4ef58d.txt (ilp32_branch_e00113f, its SHA256SUMS OK) |
| floats | 1120/1120 MATCH | equal | first 1118 lines identical to floats_c4ef58d.txt; plus the 2 new t_fp_consts cases |
| punning (4) | 4 UB "type-punned access", as punning_cases.txt labels them | equal | not re-run (record: 3 MATCH + 1 MISMATCH) |
| unions (49) | 39 MATCH + 10 UB | equal; 49/49 outcomes = union_labels.tsv | not re-run (record at d8afb97: 49 UB) |
| ILP32 i686 (13) | 13/13 MATCH (native: gcc -m32 -static under qemu-i386) | output byte-identical to C_ilp32.txt | c4ef58d re-run: 4 MATCH + 9 UB (= the e00113f record) |
| x86-64 (13) | 13/13 MATCH | byte-identical | 13/13 |
The 26 ILP32 outputs at e6ac99a are equal to e00113f's recorded ones.

## 4. Statements (CHANGES_punning2.md, 5a088092...)
Method: I took the 28 declarations of the 12 changed Examples files at c4ef58d and at e6ac99a, cut each statement at its
first `:=` and collapsed whitespace (punning2/stmts_*.tsv, stmt_changes.tsv).
- Counts: 20 statements changed, 6 are unchanged, 2 are new and none was removed.
- Each change only inserts hypotheses; no part of the old statement changes, so every conclusion is as before.
- For 19 of the 20, the inserted text is verbatim the record's table. For delete_spec it is the premise `AllCJSON ts →`,
  which the record describes in words.
Old vs new, in words. Every theorem below held for a block of any type `ty` and now holds only for the element type given:
- an array of 32-bit integers, of either signedness and any length:
  - TwoLoops.fill_after_count_spec;
  - Carray.sum_arr_spec and Carray.find_first_spec.
- an array of records with any record name: Tokens.fill_token_spec.
- an array of 8-bit integers (char, of either signedness):
  - PtrLoop.str_len_spec, count_char_spec and has_char_spec;
  - PtrArgs.fill_buf_spec;
  - PtrArgs.skip_spaces_spec, which in addition needs the caller's variable `p` to have a pointer type;
  - PtrArgs.copy_nonspace_spec, for both the source and the destination;
  - the parse buffer's content in CJScan.string_scan_spec, CJStrings.skip_whitespace_spec and skip_whitespace_ub, and in
    CJParseString.parse_string_not_quote, parse_string_unterminated and parse_string_noub;
  - the four hex digits in CJHex4.parse_hex4_ub and CJHex4Tight.parse_hex4_spec.
- CJDelete.delete_spec and delete_forest have a new premise, AllCJSON ts: every item of the forest, children included,
  has record type "cJSON". AllCJSON is a new def, with the new lemma AllCJSON.get.
Unchanged statements:
- CJAppend.build_array_spec: its statement lines are identical, and only its proof's loop invariant adds the items' record type.
- CJParseString.Utf16Spec.
- CJStrings.skip_bom_off, skip_bom_short, skip_bom_main and skip_utf8_bom_spec.
Lean check: all 28 declarations load from the copy's oleans (punning2/AxCheck.lean, axcheck_out.txt). `#print axioms` gives
[propext, Classical.choice, Quot.sound] for 26 of them and [propext, Quot.sound] for AllCJSON and AllCJSON.get; no sorryAx.
The 12 modules' oleans are in the verified manifest, and the producer's build log A_cj.txt ends "Build completed successfully".
For users of the pin: a result that applies one of these 20 theorems now needs the block's element type as stated.

## 5. Census, c4ef58d vs e6ac99a (measurement only)
- Static: cirscan --json on the 405 files (48 from cirlean_work/corpus, 357 from TheAlgorithms fdcc29b).
  - The two pins' outputs are identical (census/static_diff_mine.txt is empty).
  - 2977 functions: 2374 in scope and 603 external.
  - My scans for both pins are byte-identical to the producer's scan directories.
- Dynamic: `main` of the 193 in-scope programs, 10 s per run.
  - All 193 rows are byte-identical to E_census_dynamic.tsv; 192 outcomes are the same at both pins.
  - One UB reason changed: math_inv_sqrt, from "read of an indeterminate or ill-typed value" to "type-punned access
    (byte-level access not modelled)".
  - Outcome classes at e6ac99a: 118 values, 68 UB and 7 with no output.

## Also re-run: generation (record section D)
- cJSON 1.7.18 LP64: the Gen regenerated with the copy's cir2lean differs from c4ef58d's (vgen_full/src_c4ef58d) only in
  fn_cJSON_GetNumberValue and that function's manifest hash.
  - The constant 0x7FC00000 : float is now Float.ofBits 9221120237041090560 (0x7FF8000000000000, a NaN).
  - Before, it was Float.ofBits 2143289344 (a subnormal).
- i686 Gen: ptrBytes := 4. Compiled on the copy, sizeAlign gives cJSON (36, 1), printbuffer (36, 4) and pointers (4, 4).
- gen/D_gen_mine.txt equals D_gen.txt after normalizing the paths.

## Notes
- Two baselines were not re-run: punning at c4ef58d and unions at d8afb97.
- The c4ef58d cirrun and cirscan were only executed, from ~/cirlean_frozen/c4ef58d_20261025.
  - No recorded hash was found for them: sha256 3cfd076e14761985... (cirrun) and 013c6b8c88142774... (cirscan).
  - Their outputs reproduce the producer's c4ef58d scans and census column, and the e00113f record's c4ef58d ILP32 column.
- Process:
  - No writes outside the check and replay dirs.
  - Tests, scans and Lean runs ran under coreh_guard_v2 with ulimit -v 32 GiB on one core. Light reads (sha256sum -c,
    git reads with --no-optional-locks and GIT_ALLOW_PROTOCOL=file, diffs) ran unguarded.
  - One `sha256sum -c` ran inside the read-only ilp32_branch_e00113f deliver dir (a subshell cd).
  - One `rm -f` removed a mislabelled diff file I had just created in ilp32/.
- Cost: 0.125 core-h in total over 9 guard logs (census 0.072, gen 0.027, floats 0.020, others <= 0.004 each).
