RESULT: R6c and R6rb agree with the deliveries. R6c (R6's frozen 415 es-toolkit pairs, StrictTS const-arrow 9e54bdb): PROVED 60 (57 all-worlds, 3 allocated-arguments; 25 at one instance; 7 on the old version's parameter types), REFUTED 10 Lean-confirmed + 76 Node only, UNKNOWN 269; exactly 6 changes from R6b, all UNKNOWN -> PROVED. R6rb (R6r's frozen 862 remeda pairs, same tool): PROVED 59 (all-worlds; 35 at one instance), REFUTED 9 + 55, UNKNOWN 739; exactly 5 changes from R6r, all UNKNOWN -> PROVED. 60/60 and 59/59 theorems re-elaborate with exactly the standard axioms and no error/sorry in their blocks; all 35 proof modules and the 49-module StrictTS closure (with the new DynOpt) pass a kernel replay; refutations identical to R6b/R6r.

# R6c and R6rb: evidence check

Checked by an agent of the evidence owner (the evidence-owner session), 2026-10-27 06:01Z-06:40Z (date -u). Copies under
~/fv_paper/replay/r6c-20261027T0601Z/: tree/ = rsync -rtL of ~/strictts_ws/constarrow without scratch/, .git and logs/
(0 symlinks; the 939 tracked files of 9e54bdb byte-identical by git hash-object, copy_vs_9e54bdb.txt; frontend/node_modules
dereferenced); r6c/, r6rb/ = cp -rL of scratch/r6c and scratch/r6rb (diff -rq empty); recheck_*/, r6creplay/, r6rbreplay/ =
the Lean files run. Inputs as registered before the runs: prereg/ADDENDUM_R6c_R6rb_inputs.md (6ecf67c4).

## Objects and hashes
- Results (git show, read-only, GIT_ALLOW_PROTOCOL=file; no partial clone): R6C_RESULTS.md at 0f1e6b8 = 28244e08...,
  R6RB_RESULTS.md at 0f1e6b8 = 9f547ca5... (copies in delivered/). At 8716145, R6C_RESULTS.md (6dcb41aa) stated a wrong
  sha256 for r6c_table.tsv; 0f1e6b8 corrects that one line, and the corrected value equals my hash of the table (075508b4...).
  R6RB_RESULTS.md's table hash (19b20706...) equals mine.
- Manifests: R6C_EVIDENCE_SHA256SUMS 175ed99a... 2,123/2,123 OK; R6RB_EVIDENCE_SHA256SUMS 17874487... 1,907/1,907 OK.
- Lists = the addendum (and the R6/R6r addenda): r6_testable 408069f7 (415), r6_provable f2f81a47 (79), pairs bf561176
  (-c in ~/strictts/scratch/hist_es 3,642/3,642 OK); r7_testable fec09171 (862), r7_provable 14c45704 (160), pairs 41e73814
  (-c in hist_remeda 7,124/7,124 OK).
- Tool: git diff 9e54bdb..0f1e6b8 touches only tools/difftool/r6c/ (15 files) and tools/difftool/r6rb/ (16 files).
  Dist hashes recomputed in the copy: difftool baf07b296e82b4bf, frontend 654dcdf41dd337e5 (as registered).

## Counts (tables and, independently, the chunk records: verdict of each pair's target function)
- Table ids = the testable lists, each once; provable=yes rows = the provable lists. Table category = chunk category for
  415/415 and 862/862 (r6c_chunk_cat.tsv, r6rb_chunk_cat.tsv, table_checks.txt).
- R6c: PROVED 57 all-worlds + 3 allocated-arguments, REFUTED 10 Lean-confirmed + 76 Node only, UNKNOWN 269. inst column
  (one generic instance) on 25 PROVED (chunk notes agree); domain column ("old version's parameter types (compat
  wrapper)") on 11 rows, 7 of them PROVED (isFinite, isNaN, isObject, isObjectLike 8db96e45; endsWith, isLength,
  startsWith e3525153) and 4 UNKNOWN. Provable 79: 52 PROVED (49 + 3), 9 + 4 refuted, 14 UNKNOWN. No row says "target not
  found in the translation".
- R6rb: PROVED 59 all-worlds, REFUTED 9 + 55, UNKNOWN 739; inst on 35 PROVED; domain empty. Provable 160: 59 PROVED,
  9 + 2 refuted, 90 UNKNOWN. No row says "target not found".
- Changes against R6b's table (r6b_table.tsv 0b7167cb): exactly 6, all UNKNOWN -> PROVED (all-worlds): startsWith
  4c285773, isFinite, isNaN, isObject, isObjectLike 8db96e45, isLength e3525153 (changes_r6b_to_r6c.tsv). Against R6r's
  table (a0d92081): exactly 5, all UNKNOWN -> PROVED: sliceString eab73291, noop, randomChar, trivialDefaultCase
  b08a667d, joinImplementation a5b389b8 (changes_r6r_to_r6rb.tsv).
- R6r's 81 no-target pairs now: 5 PROVED, 75 UNKNOWN outside the subset (68 with the rule unsupported-generic alone),
  1 UNKNOWN "translated signatures differ" (noop d1bae988) (r6r_notarget_now.tsv, r6r_notarget_rules.tsv).
- Test-file helpers among the PROVED: R6c 1 (greet, spread.spec.ts), so 59 library; R6rb 7 (as in R6r), so 52 library.
  By commit type, PROVED: R6c refactor/perf/style/chore 14, fix/feat/revert 33, docs/test/other 13; R6rb 29 / 26 / 4.
- First looks: all 6 R6c changes were among StrictTS's disclosed first looks (addendum, (a)), so they are not blind.

## Theorems
- Re-elaborated every batch file (16 + 19) in the copy (lake env lean --tstack=262144, LEAN_NUM_THREADS=1, guarded, at
  most 2 at once): for each PROVED pair, the theorem is declared once, my output prints exactly [propext,
  Classical.choice, Quot.sound], and no error or sorry warning falls inside its block: 60/60 and 59/59
  (recheck_verify_*.tsv); my axiom lines for them equal the producer's recheck 60/60 and 59/59. Errors fall in 21 + 6
  theorem blocks, none of a PROVED pair, none outside a block (recheck_error_theorems_*.tsv).
- h005 (intersection 576b136a, UNKNOWN): the heartbeat limit hits at the theorem's first line (1231:0) and Lean prints
  "does not depend on any axioms" next to the error, as StrictTS says (the run's own output printed sorryAx). A second
  timeout theorem, h022 (at 94cf7ff6, UNKNOWN), flips the other way in my run (mine sorryAx; the run and the producer's
  recheck "does not depend"), so my outputs reproduce 107 of the run's 109 axiom lines (StrictTS: 108/109); R6rb 100/100.
  Neither is a PROVED theorem; the verdict rule (no error in the block) excludes both.
- Kernel replay: derived modules R6cProof.B00-B15 and R6rbProof.B00-B18 lose exactly the 27 failing blocks (derive.awk;
  deletions only, 420 and 120 lines); all 119 PROVED blocks byte-identical before and after
  (proved_blocks_identity_*.tsv). Compiled with lean -R: 35/35 rc 0, no error; their 182 axiom lines all standard.
  leanchecker (leancheck1lp.sh): 35/35 proof modules rc 0; StrictTS closure of StrictTS and StrictTS.Proof.Literals at
  9e54bdb, 49 modules (R6r's 48 + StrictTS.Proof.DynOpt; 47 oleans byte-identical to the R6r check's copy), 49/49 rc 0;
  BadCtl rc 1 (declaration type mismatch), GoodCtl rc 0. Trust scan of the 35 proof files and DynOpt.lean: no
  skipKernelTC, addDeclWithoutChecking, unsafe, implemented_by, extern, axiom, native_decide, ofReduceBool, Lean.Kernel,
  setEnv/modifyEnv, sorry, admit, trace/debug options; imports only StrictTS and StrictTS.Proof.Literals.
- Statements. startsWith 4c285773 (the const arrow now translated): for every host model, every argument vector of the
  declared types (string, string, number | undefined) and every world, old and new give the same execution. The compat-
  wrapper proofs (e.g. isNaN, isFinite 8db96e45): the old function (value: unknown) equals the new one called through
  __difftool_compat(value: unknown), which passes the argument cast to unknown | undefined (the new value?: unknown); so
  they cover one-argument calls of the old type, not calls without the argument that the new signature also admits.
  DynOpt.lean (15 proved lemmas, ts_sym rewrites): the cast of an unknown value to unknown | undefined never fails and
  keeps its runtime value, so typeof, truthiness, === and primitive casts see the original value; no new assumption.

## Refutations
- replay_v2 directories byte-identical: R6c = R6b's (87 entries), R6rb = R6r's (65 entries); both were reproduced in
  plain node in checks/r6b-20261027T0150Z and checks/r6r-20261027T0333Z.
- tscheck.tsv: R6c = R6's erratum file (1dbd9852), R6rb = R6r's (81ac872f); refuted_export.tsv R6rb = R6r's (1c298fa0),
  and r6r_refuted_export_v2.tsv (R6r re-run with the fixed export check) = 1c298fa0, so R6r is unaffected by the pipefail
  fix. R6c's new export column: of the 76 calls valid in both versions, 72 are to exported functions and 4 to internal
  ones (areObjectsEqual, flattenObjectImpl x2, assignInImpl); the 10 invalid calls are all to exported functions
  (r6c_tscheck_export_join.tsv; flattenObjectImpl and assignInImpl confirmed plain functions by git show in the clone).
- Lean confirmations: the same pair sets as R6b (14 blocks = 10 Lean-confirmed + 4 with reasons) and R6r (11 = 9 + 2);
  every OldC_/NewC_ evaluation section equals the previous run's for the same pair, 14/14 and 11/11 (confirm_compare_*.tsv).

## Cost
- Producer guard_secs.txt: R6c 37 jobs 0.861 core-h; R6rb 55 jobs 0.917 core-h (as reported). Tokens not checked.
- This check: 159 guarded jobs, 0.502 core-h (recheck, compile, replay; copies). Light analysis (jq, awk, diff,
  sha256sum, git show/diff/ls-tree/hash-object) unguarded. Nothing written into StrictTS's trees; lake ran only in my copy.

## Notes
- The first 8716145 version of R6C_RESULTS.md stated a wrong table hash (fixed in 0f1e6b8); the delivered hash is the fixed one.
- h022's axiom line differs between runs as described above (heartbeat timeout, not a PROVED theorem).
