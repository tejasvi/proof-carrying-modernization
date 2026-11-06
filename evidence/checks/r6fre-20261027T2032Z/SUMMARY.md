RESULT: R6f remeda (StrictTS L5, master 4bef3c4; frozen 862 pairs) agrees with the delivery. PROVED 117 (all all-worlds;
93 only at one instance), OLD-NO-PANIC 2 (not an equivalence), REFUTED 11 Lean-confirmed + 53 Node only, UNKNOWN 679.
119/119 theorems print only the standard axioms and have no error in their blocks; 32 derived proof modules replay rc 0;
StrictTS closure: the sibling's replay (50 modules, same .olean bytes); controls ok.

# R6f remeda: evidence check (an agent of the evidence-owner session; written 2026-10-27T21:01:32Z)
Copies: ~/fv_paper/replay/r6fre-20261027T2032Z/r6f (cp -rL of ~/strictts_ws/r6f/scratch/r6f after RE DONE; 0 symlinks).
Tool tree: the sibling's ~/fv_paper/replay/r6f-20261027T1859Z/tree, used read-only after checking that it is unchanged
(tracked files = 4bef3c4 1057/1057, as the sibling's record; 0 paths with mtime or ctime newer than the sibling's SUMMARY.md,
before and after my Lean runs). Inputs: prereg/ADDENDUM_R6f_inputs.md (4e3af7f3, 16:39:14Z). Method and scripts:
checks/r6f-20261027T1859Z (copied to scripts/ and retargeted; new scripts are marked in their headers).

## Objects and inputs (inputs.out, ids_vs_lists.txt, tree_vs_4bef3c4.txt)
- R6F_RESULTS.md 2718bc2f, re/r6f_table_final.tsv f0f94ab6, re/r6f_table.tsv d7af240a, re/compare_r6e.tsv 2968abfa,
  re/np_returns.tsv a93d69f8, re/tscheck.tsv 81ac872f, re/refuted_export.tsv 1c298fa0 = announced, in the producer tree and
  in the copy; re/EVIDENCE_SHA256SUMS 42e346b2: 1942/1942 OK in both.
- Inputs = the addendum: re/r7_testable.txt fec09171 (862 pairs; table ids = the list after its "scan/" prefix, 0
  differences), re/pairs_SHA256SUMS 41e73814 (hist_remeda 7124/7124 OK). run_all.log: start 16:39:55Z, HEAD 4bef3c48; ES DONE
  18:54:04Z; RE DONE 20:30:06Z. post.log: HEAD 4bef3c48, dist 86fe40d6.
- Deviation files: re/r6_testable.txt (fec09171) and re/r6_provable.txt (14c45704) = R6e's re/r7_testable.txt and
  re/r7_provable.txt. re/report.js reads them; the first report step failed (rc 1, 20:07:20Z, file missing) and was rerun at
  20:16:48Z after the copy (post.log; disclosed in R6F_RESULTS.md). So the addendum's "no chain or post-run script reads a
  provable list" does not hold for report.js. The list feeds only the provable column and the reason text; categories come
  from the chunk records. Table provable=yes = the list's 160 (0 differences).

## Counts (re_chunk_cat.tsv, re_table_cat.tsv, table_checks.txt)
- Chunk records and table agree 862/862 (id, category).
- PROVED 117 (statement all-worlds 117); OLD-NO-PANIC 2 (last dbeea0a3, _last b08a667d; own category); REFUTED 11 + 53;
  UNKNOWN 679. The addendum expected PROVED about 117, REFUTED 64, UNKNOWN about 681.
- Among the 117: inst (one instance) 93 (table = chunk notes: 93 inst, 24 none); domain: old version's parameter types
  (compat wrapper) 4 (isArray, isBoolean, isDate, isString at 7900d2c2), new version's return type (return wrapper) 1
  (_first b08a667d); extern 0.
- By commit type: chore 44, style 13, fix 18, feat 31, docs 2, other 8, type 1.
- Provable 160: 96 PROVED, 2 old-no-panic, 9 + 2 refuted, 51 unknown. 21 proofs are of pairs outside the frozen 160 (1 from
  L4, 20 from L5).

## Changes against R6e and first looks (changes.txt, changes_re.tsv, restrictions_vs_r6e.txt)
- Against the R6e check's table (re_table_cat.tsv d46fad9b): exactly 58 changes: 56 UNKNOWN -> PROVED (all-worlds), isEmpty
  9c79944e and chunkImplementation 785b885c Node only -> Lean-confirmed; same ids, no pair lost.
- The 61 pairs that R6e proved keep the same statement, inst and domain columns (61/61; R6e's re/r6e_table.tsv e948632d =
  R6E_RESULTS.md).
- The 56 new proofs: all in first_looks_per_pair.tsv (578b56fc) with last verdict PROVED and new_proved yes; table
  tried_before_run yes 56/56. Restrictions: inst 56; compat wrapper 3 (isArray, isBoolean, isString at 7900d2c2), return
  wrapper 1 (_first b08a667d), extern 0. 20 of the 56, these 4 among them, are outside the frozen 160. By commit type: chore
  21, style 6, fix 11, feat 12, other 5, type 1.
- All 78 first-looked remeda pairs: R6f verdict = last first-look verdict (78/78). The two new confirmations are first looks
  with last verdict REFUTED.

## Theorems (recheck_*, axiom_lines*, derive_*, compile_*, replay_*, statement_forms*, closure_*)
- Re-elaborated the 32 batch files (lake env lean --tstack=262144, LEAN_NUM_THREADS=1, ulimit -v 32 GiB, guarded, at most 2
  at once, load floor 0): 19 rc 0, 13 rc 1. For each of the 119 proofs.tsv rows (117 + 2): declared once, my output prints
  exactly [propext, Classical.choice, Quot.sound], no error or sorry warning inside its block: 119/119
  (recheck_verify_re.tsv). 41 error blocks, none of a proofs.tsv theorem, none outside a block. Axiom lines 224 = the
  producer recheck's 224. One line differs: equiv_h019u001_np in 191527Z obs_00, an unproved block (mine sorryAx after a simp
  failure, the producer's none after a heartbeat timeout; both runs report "difftool: residual goal" in it).
- Derived modules R6fReProof.B00-B31 drop exactly the 41 failing blocks (870 lines deleted, 0 added); 119/119 proof blocks
  byte-identical. lean -R: 32/32 rc 0, 0 errors, 0 sorry warnings, 183 axiom lines, all standard; 119/119 print exactly the
  three.
- leanchecker (leancheck1lp.sh): 32/32 proof modules rc 0. StrictTS closure: the same 50 modules as the sibling's
  (closure_strictts_re.txt), which its replay passed 50/50. The 50 .olean files in the shared tree are byte-identical to
  the producer's build and were last changed (ctime and mtime) before that replay started at 19:21:05Z
  (closure_oleans_re.tsv), so the replay is reused. BadCtl rc 1 (kernel declaration type mismatch), GoodCtl rc 0.
- Statement forms (statement_forms_re.tsv): all 117 are (I : Impl) -> forall vs w, JS.exec (callFun I Old ..) w =
  JS.exec (callFun I New ..) w, for every host implementation and every world, with no World premise. The 2 old-no-panic
  theorems: that equation, or the old run ends in a panic.

## Refutations (refutations.out, node_spot.tsv, confirm_*)
- replay_v2/replay.tsv ed254301 = R6e's (64/64 agree yes); tscheck.tsv and refuted_export.tsv = R6e's (exported 40, internal
  24); refuted ids = table REFUTED ids (64).
- My spot check in plain node (v22.22.1), 10 pairs (every 6th dir), old and new drivers: outputs = recorded out.json 20/20,
  old != new 10/10.
- 13 confirmation blocks: the 11 shared with R6e have identical OldC_/NewC_ sections (confirm_compare_re_r6e.tsv). The new
  ones evaluate differently, as their node replays: isEmpty(undefined) false vs true; chunkImplementation([], 0) [] vs
  RangeError (confirm_new_two.txt).
- My re-run of the 7 confirmation files: error counts = recorded (7/7); all 13 OldC_/NewC_ sections = recorded; old != new
  for the 11 Lean-confirmed. The two that stay Node only, as in R6e: swapArray 035ae147 (the old run panics on an
  out-of-bounds read in our semantics, node returns [undefined, undefined]) and sampleImplementation b08a667d (equal
  sections; node differs in whether the result is the argument array) (confirm_rerun_re.tsv).

## Cost (producer_coreh_windows.txt; it supersedes producer_coreh.txt, whose es window wrongly included 2 pre-run logs)
- Producer guard logs: 188. es-toolkit [16:39:55Z, 18:54:04Z) 110 logs 1.923 core-h; remeda [18:54:04Z, 20:30:06Z] 72 logs
  1.421; after RE DONE 4 logs 0.001; before the run 2 logs 0.045. Run total 3.345 core-h: under the addendum's estimate (4.5),
  its stop-and-ask projection (6.75) and its cap (8).
- This check: 105 guarded jobs, 0.511 core-h (my_coreh.txt: recheck 0.303, compile 0.104, confirm 0.097, replay 0.007).
  Light analysis (awk, jq, diff, sha256sum, the 20 node spot runs) unguarded. No rm, no sed -i, no /tmp.

## Proposed wording (L5 on remeda)
- sec-fixes: "On remeda, L2 proves 59 pairs equivalent (35 only at one instance), L3 proves 60 (36), L4 proves 61 (37) and
  L5 proves 117 (93)." After the L4 sentences: "L5 adds 56 proofs, all at one instance. Three of them hold only on the old
  version's parameter types and one with the old result cast to the new version's return type, and 20, these four among
  them, are of pairs outside the frozen 160. Its producer had tried all 56 before the run." Last sentence: "On remeda the
  later versions leave the differences and their type checks as they were. L2 to L4 confirm the same 9 of them in our
  semantics, and L5 two more, in \code{isEmpty} and \code{chunkImplementation}, both also tried before its run."
- Cost sentence: "... and L5 1.9 on es-toolkit and 1.4 on remeda."
- Intro: "to 98 for es-toolkit and 117 for remeda" (the rest of that sentence still holds).
- Appendix replay table: "L5, 98 + 117 equivalences and 1 + 2 weaker theorems & 111 & all & StrictTS \code{4bef3c4}"
  (29 + 32 proof modules and the 50-module closure), replacing the es-toolkit-only L5 row.
