RESULT: R6b agrees with the delivery: 415/415 frozen pairs, PROVED 54 (51 all-worlds, 3 allocated-arguments), REFUTED Lean-confirmed 10, REFUTED Node only 76, UNKNOWN 275; the only changes from R6 are the 8 newly PROVED pairs and toString's Lean confirmation; 54/54 theorems re-elaborated at 43132a8 with exactly the standard axioms and no error, and all 15 proof modules plus the 48-module StrictTS import closure pass a kernel replay; 86/86 node replays and 10/10 Lean confirmations reproduce; the regressions reproduce at the exact commit. Two qualifications: all 9 changes are pairs outside the frozen 79-pair provable list, and 2 of the 8 new proofs (endsWith, startsWith) hold only on the old version's parameter types.

# R6b (the R6 es-toolkit audit re-run with StrictTS 43132a8): evidence check

Checked by a fork of the evidence owner (the evidence-owner session), 2026-10-27 01:50Z-02:38Z (date -u). Copies under
~/fv_paper/replay/r6b-20261027T0150Z/: tree = cp -a of ~/strictts_ws/loosenull at HEAD 43132a8 (all 911 tracked files
byte-identical to the commit by git hash-object; its one symlink, frontend/node_modules -> ~/strictts/frontend/node_modules,
replaced by a real copy, and the .git pointer moved to orig_links/, so no link leads outside the copy); evidence/,
node_replay/, chunks/ = copies of scratch/r6b/{evidence,replay_v2,chunks} (diff -rq empty, no links); recheck/, confirm/,
r6breplay/ = copies of the Lean files run.

## Objects and hashes (all as announced)
- From StrictTS master d3208a8 (git show, read-only, GIT_ALLOW_PROTOCOL=file): R6B_RESULTS.md 884e0b87..., r6b_table.tsv
  0b7167cb... (= scratch/r6b/r6_table.tsv), R6B_EVIDENCE_SHA256SUMS 7019a187... (1,180 entries; sha256sum -c in scratch/r6b:
  1,180/1,180 OK). R6's table for comparison: 53f98fcd tools/difftool/r6/r6_table.tsv, c2caa541...
- Inputs: scratch/r6b/r6_testable.txt and r6_provable.txt = the prereg/R6 copies (cmp); the table's ids are the 415 frozen
  testable pairs, each once, and its provable=yes rows are the 79 frozen provable pairs; pairs_SHA256SUMS bf561176... -c in
  ~/strictts/scratch/hist_es: 3,642/3,642 OK (the run writes its history outputs there; the pair files are unchanged).
- git: 2ea47b8 is the merge of 0eccf2b and 43132a8; its tree differs from 43132a8 only in HANDOFF_20261023.md; d3208a8 and
  bbe90b4 after it change no code.

## Tool changes 10ec829 -> 43132a8 (tool_changes.md, tool_code.diff, tool_diffstat_10ec829_43132a8.txt)
The four described changes, plus the corpus program tests/corpus/loose_null.ts and rebuilt dist/: (1) the translator
accepts `==`/`!=` only against null, the global undefined or `void <number>` (diagnostic no-loose-eq otherwise) and lowers
`x == null` to "x is null or undefined", with narrowing of optionals and unions with null; (2) StrictTS/Proof/DynNullish.lean:
four lemmas, Dyn.eq of any value against undefined/null = some (its runtime type is undefined/null) (statements.md);
(3) ts_destruct splits optionals and unions (StrictTS/Proof/Literals.lean, 8 lines); (4) difftool compatWrapper: for a
non-generic function whose parameters widened, the new version is called through `__difftool_compat`, which takes the OLD
version's parameter types.

## Regressions from the copy (regress.sh; each phase guarded and pinned to one core)
- lake build: up to date (50 jobs), and Examples, Modular, f64diff, strdiff (164 jobs); rc 0.
- corpus (tests/difftest/run.js): PASS 181 / FAIL 0 / SKIP 0 (180 programs at 10ec829 plus loose_null). Two outputs,
  date_now and small_levers, change on every run (Date.now, Math.random); restored from a snapshot afterwards.
- difftool selftest: PASS (8 functions).
- equivalence bench, six subsets: 43/44 equivalences PROVED, 23/23 differences REFUTED, 0 wrong. The 67 per-pair verdicts
  (with the Lean-confirmation flags) equal the producer's full regression (scratch/ln_reg/full, run on 6ac88b4 plus the
  working tree that became 43132a8) and the R6-era regression at f6a4ec0 plus working tree (rally_reg). 0.151 core-h.

## Counts and changes (from r6b_table.tsv and, independently, from the 415 chunk records)
- PROVED 54 (51 all-worlds, 3 allocated-arguments), REFUTED Lean-confirmed 10, REFUTED Node only 76, UNKNOWN 275. The chunk
  records give the same category for 415/415 pairs (confirmedBy node+lean 10, node 76), and for the 54 PROVED pairs the
  same theorem, file and statement kind as proofs.tsv, each with axioms [propext, Classical.choice, Quot.sound].
- Against R6's table, 406 verdicts are unchanged. 8 pairs go from UNKNOWN to PROVED (all-worlds): isNil 523e5592 and
  489ac76f, isNotNil 523e5592 and 72589819, isArrayLike 925ee3be and be4162dc, endsWith and startsWith e3525153; toString
  43932e61 goes from REFUTED (Node only) to REFUTED (Lean-confirmed). The 86 REFUTED rows keep identical evidence strings,
  their counterexample inputs equal the erratum check's list (checks/r6erratum-20261027T0027Z/cex_inputs.tsv), and the 86
  replay directories (drivers, modules, recorded outputs, replay.tsv) are byte-identical to R6's: the erratum's 76/10 split
  applies unchanged.
- All 9 changed pairs lie outside the frozen 79-pair provable list: the frozen scan marks each inSubset=false for the single
  rule no-loose-eq (`==` with null). On the 79 provable pairs nothing changed (46 PROVED, 9 + 4 REFUTED, 20 UNKNOWN, as in
  R6). Of the 27 pairs that the scan excluded for that rule alone, R6b proves 8, refutes 5 (1 Lean-confirmed) and leaves 14
  unknown.
- UNKNOWN reason classes against R6 (unknown_class_transitions.tsv): "outside the subset" 217 -> 199 (8 now PROVED, 10 now
  "no proof"), "translated signatures differ" 9 -> 4 (5 now "no proof", through the compat wrapper), "no proof" 8 -> 23.
  UNKNOWN pairs that ran all 1,500 random inputs: 218 (R6: 226, less the 8 now proved).
- By commit type (as reported): refactor/perf/style/chore 13 PROVED (R6: 9), fix/feat/revert 32 (29), docs/test/other 9 (8).
  Generic and compared at one instance: 25 of the 54 (R6: 23 of 46; the 2 added are isNotNil at T := number).

## The 54 theorems
- proofs.tsv lists exactly the 54 PROVED pairs with the table's statement kinds; the 15 Lean files are byte-identical to the
  run directories' batch files (30/30 .lean/.out equal).
- Re-elaborated one at a time in the copy (`lake env lean --tstack=262144 FILE`, LEAN_NUM_THREADS=1, guarded): for each of
  the 54, the theorem is declared once, my output prints exactly `'<thm>' depends on axioms: [propext, Classical.choice,
  Quot.sound]` (the same line as the producer's recheck output), and no error and no sorry warning falls inside its lines:
  54/54 (recheck_verify.tsv).
- 10 of the 15 files exit 1. Their errors fall in 22 theorem blocks: 19 belong to UNKNOWN pairs (the provable "no proof"
  pairs and the pairs newly translated but unproved) and 3 are the all-worlds variants of the pairs PROVED as
  allocated-arguments (xor e595e5e0, sum 34be6d76, without 030817ee); none is a PROVED theorem, and no error lies outside a
  theorem block (recheck_error_theorems.tsv).
- Axiom report lines: 103 in my outputs. Mine equal the producer's recheck in 14 of 15 files and the run's own outputs in 13.
  The differences are two theorems of UNKNOWN pairs that fail at the heartbeat limit (equiv_h005u001, intersection 576b136a,
  the one difference the producer's recheck.log reports, which mine reproduces; equiv_h022u001, at 94cf7ff6, where mine differs
  from both). Between runs, such a theorem prints
  either `[propext, sorryAx, Classical.choice, Quot.sound]` or "does not depend on any axioms", next to its timeout error.
  The axiom line alone therefore does not show a proof; each PROVED verdict here also has no error in its lines and passes
  the kernel replay below.
- Source scan of the 15 files (trust_scan.txt): no skipKernelTC, addDeclWithoutChecking, unsafe, implemented_by, @[extern],
  axiom, native_decide, ofReduceBool, Lean.Kernel, setEnv/modifyEnv, sorry, admit or debug options; options only
  maxHeartbeats 400000 and maxRecDepth 100000; imports only StrictTS and StrictTS.Proof.Literals. Each file's preamble defines
  elaboration helpers (meta code reading the environment), which the kernel replay does not trust.
- Kernel replay (as checks/r6replay-20261026T2241Z): the 15 files as modules R6bProof.B00-B14 (batch_map.tsv). lean writes no
  olean for a file with errors, so derive.awk removed exactly the 22 failing blocks from 10 files (deletions only, 0 added
  lines; derive_ranges.txt, derive_diffstat.txt); the 54 PROVED blocks are byte-identical before and after (54/54,
  proved_blocks_identity.tsv). Compiled with lean --tstack=262144 -R (LEAN_NUM_THREADS=1, guarded): 15/15 rc 0, no errors, and the compile outputs print exactly the standard axioms for all 54 PROVED theorems. leanchecker (leancheck1lp.sh, explicit LEAN_PATH): R6bProof.B00-B14 15/15 rc 0; the import closure of StrictTS and StrictTS.Proof.Literals at 43132a8 (closure_strictts.txt: 48 modules, R6's 47 plus StrictTS.Proof.DynNullish) 48/48 rc 0; negative control BadCtl rc 1 (declaration type mismatch), GoodCtl rc 0; replay wall sum 105 s over 63 modules.
- Statements and the new lemmas: statements.md. The isNil, isNotNil and isArrayLike theorems quantify over every host model,
  every argument vector of the declared types (unknown values included) and every world. endsWith and startsWith (e3525153)
  quantify over the OLD parameter types (string, string, optional number) and call the new version through
  `__difftool_compat`, so these 2 hold only on the old version's inputs; the table and the report do not mark this.

## The 86 refutations and the 10 Lean confirmations
- The 86 replay directories are byte-identical to R6's. Scan of the 906 .mjs files: imports relative only (172 dynamic
  imports of ./src/*.mjs); the only process use is the drivers' process.on('uncaughtException'/'unhandledRejection')
  handlers; no fs, child_process, network, environment or absolute paths (node_replay_scan.txt).
- node v22.22.1 from the copy, old and new per pair (node_replay.sh): 172/172 exit 0 with no stderr; my stdout equals the recorded out.json for 86/86 pairs on both sides, and old differs from new for 86/86 (node_replay_compare.tsv).
- Lean confirmations (verify_confirm.sh): the OldC_/NewC_ evaluation sections of my re-runs (7 from the recheck files, 3 from their own run files) equal the run records' Lean outputs for 10/10, old differs from new, and the Lean outcome line equals the node outcome on both sides for 10/10. For toString([undefined]) the old version returns the empty string and the new one returns "undefined". Two of the three run files exit 1 because they also hold failing theorems of UNKNOWN pairs; their evaluation sections are complete. The toString confirmation file (history-20261027T011528Z-1441283/lean/batch_00.lean), and those of trimEnd
  (…011406Z-924832) and trimStart (…011853Z-2395725), are not in R6B_EVIDENCE_SHA256SUMS. I re-ran them from copies of the
  run directories (sha256 in confirm/run_files_sha256.txt; trust scan in confirm/trust_scan_confirm.txt).

## For the paper, if R6b replaces R6 (no paper text edited here)
- Numbers that change: PROVED 46 -> 54, Lean-confirmed refutations 9 -> 10, UNKNOWN 283 -> 275, proved at one instance
  23 -> 25, proved in fix/feat commits 29 -> 32. Unchanged: 86 refuted, 76/10 erratum split, the four perf/style findings.
- Qualifications to state: R6b is not pre-registered (a re-run of the frozen inputs after tool changes). All its 8 new proofs
  and the new Lean confirmation are pairs outside the frozen 79-pair provable list (the subset grew), so "79 of these lie in
  the subset" describes the frozen list, not 43132a8's reach. endsWith and startsWith are proved only on the old parameter
  types. The 3 new proofs in fix commits change code, not only types (isNotNil `!== null && !== undefined` -> `!= null`;
  endsWith/startsWith add null handling), so R6's description of its 29 proved fix/feat changes as type-only does not cover
  them.
- Cost as reported: R6b run, replays and recheck 0.84 core-h; development and regressions 0.48 core-h. The producer's guard
  logs give 0.837 core-h (01:04-01:49Z, 34 logs) and 0.484 core-h (00:13-01:04Z, 36 logs; one more log stops without a
  total after 0.017 core-h) (producer_coreh.txt). The $33.58 token figure was not checked.

## Disclosures
- Copy fix: the worktree's frontend/node_modules symlink (to ~/strictts/frontend/node_modules) was replaced by a real copy in
  the copy, and the .git pointer was moved out (orig_links/); the copy's tracked files equal 43132a8 (copy_vs_43132a8.txt).
- Compute: 0.454 core-h in all: regressions 0.151, re-elaboration 0.193, compile and kernel replay 0.105, node replays 0.005 (scheduler guards include their jobs). Light comparisons (awk, jq, diff, sha256sum, git hash-object; seconds of CPU) ran unguarded in the tool shell. Every job was guarded (coreh_guard_v2, one job at a time). Nothing was written outside this directory
  and ~/fv_paper/replay/r6b-20261027T0150Z; git was used read-only; no messages were sent.
