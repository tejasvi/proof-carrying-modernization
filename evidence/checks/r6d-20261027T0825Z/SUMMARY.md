RESULT: R6d agrees with the delivery. es-toolkit (R6's frozen 415 pairs, StrictTS master 25790c3): PROVED 64 equivalences (60 all-worlds, 4 allocated-arguments; 28 at one generic instance; 9 on the old version's parameter types through the compat wrapper, 1 at the new version's return type through the return wrapper), OLD-NO-PANIC 1 (not an equivalence), REFUTED 10 Lean-confirmed + 76 Node only, UNKNOWN 264. remeda (R6r's frozen 862 pairs): PROVED 60 (all-worlds; 36 at one instance; 1 through the compat wrapper), OLD-NO-PANIC 2, REFUTED 9 + 55, UNKNOWN 736. Exactly 5 and 3 verdicts change against R6c and R6rb, all UNKNOWN -> PROVED or old-no-panic, all disclosed first looks (not blind). All 65 and 62 theorems (the 3 old-no-panic ones included) re-elaborate at 25790c3 with exactly the three standard axioms and no error or sorry inside; the 38 proof modules and the 49-module StrictTS closure pass the kernel replay; refutation files and confirmations equal R6c's and R6rb's. Labelling note: the per-pair table and the chunk records give the old-no-panic pairs the category "PROVED (old-no-panic)"; only the results file separates them.

# R6d: evidence check

Checked by an agent of the evidence owner (the evidence-owner session), 2026-10-27 08:25Z-09:05Z (date -u). Copies under
~/fv_paper/replay/r6d-20261027T0825Z/: tree/ = rsync -rtL of ~/strictts_ws/r6d without scratch/, .git and logs/ (0 symlinks;
971/971 tracked files of 25790c3 byte-identical by git hash-object, copy_vs_25790c3.txt); r6d/ = cp -rL of scratch/r6d (diff -rq
empty, 0 links; manifest 4,043/4,043 OK in the copy); recheck_es/, recheck_re/ = the 17 + 21 Lean files run; esreplay/, rereplay/ =
the derived modules. Inputs registered before the run: prereg/ADDENDUM_R6d_inputs.md (7c9230e1).

## Objects and hashes
- Results (git show 01fe3f2:tools/difftool/r6d/R6D_RESULTS.md, read-only, GIT_ALLOW_PROTOCOL=file; ~/strictts is not a partial
  clone): sha256 a88e9e31... = announced (copy in delivered/).
- Manifest R6D_EVIDENCE_SHA256SUMS f2092508... 4,043/4,043 OK (manifest_check_before.txt); no entry under scratch/r6d_attempts/.
- Lists = the addendum: es/r6_testable 408069f7 (415), r6_provable f2f81a47 (79), pairs bf561176 (-c in ~/strictts/scratch/hist_es
  3,642/3,642 OK); re/r7_testable fec09171 (862), r7_provable 14c45704 (160), pairs 41e73814 (-c in hist_remeda 7,124/7,124 OK).
- Tool: git diff 25790c3..01fe3f2 touches only HANDOFF_20261023.md, README.md and tools/difftool/r6d/ (30 files); no tool code.
  Dist hashes recomputed in the copy (recipe: cat of the sorted dist files, sha256, 16 hex; it reproduces R6c's baf07b296e82b4bf
  on the R6c copy): difftool 3f0e0ee59cd91535, frontend 654dcdf41dd337e5 (as registered). The copy's StrictTS library is up to
  date (lake build --no-build: 51 jobs up to date).

## Counts (tables and, independently, the chunk records: verdict of each pair's target function)
- Table ids = the testable lists, each once; provable=yes rows = the provable lists; table category = chunk category for 415/415
  and 862/862 (es_chunk_cat.tsv, re_chunk_cat.tsv, table_checks.txt).
- es-toolkit: PROVED (all-worlds) 60, PROVED (allocated-arguments) 4, PROVED (old-no-panic) 1, REFUTED 10 Lean-confirmed + 76
  Node only, UNKNOWN 264. inst (one generic instance) on 28 equivalences (chunk notes agree); domain "old version's parameter
  types (compat wrapper)" on 9 PROVED rows (13 rows in all), "new version's return type (return wrapper)" on stubObject and on
  the old-no-panic sample; statement column all-worlds 60, allocated-arguments 4, old-no-panic 1. Provable 79: 52 + 4
  equivalences, 1 old-no-panic, 9 + 4 refuted, 9 UNKNOWN. No row says "target not found". Equivalences by commit type:
  refactor/perf/style/chore 16, fix/feat/revert 34, docs/test/other 14 (as reported).
- remeda: PROVED (all-worlds) 60, PROVED (old-no-panic) 2, REFUTED 9 + 55, UNKNOWN 736; inst on 36 equivalences; compat wrapper
  on isDate; return wrapper on the two old-no-panic pairs. Provable 160: 60 equivalences, 2 old-no-panic, 9 + 2 refuted, 87
  UNKNOWN. Equivalences by type: 29 / 26 / 5 (as reported).
- Changes against R6c's table (075508b4) and R6rb's (19b20706), changes_es.tsv and changes_re.tsv: exactly 5 and 3, all from
  UNKNOWN: es-toolkit isArray 35fbc4ca (docs) and isArray 4bb457ad (feat) PROVED all-worlds at T := number on the old parameter
  types (the 4bb457ad new version is not generic); initial 9089b3b4 (refactor) PROVED allocated-arguments at T := number;
  stubObject b99176b2 (style) PROVED all-worlds at the new return type; sample fa2afcd6 (fix) old-no-panic at T := number.
  remeda isDate 7900d2c2 (other) PROVED all-worlds at T := number on the old parameter types; last dbeea0a3 (other) and _last
  b08a667d (feat) old-no-panic at T := number. All 8 are in the addendum's first looks (c): not blind. The producer's
  compare_r6c.tsv / compare_r6rb.tsv list the same pairs.
- Labelling: the table's cat column and the chunk records' verdict call the 3 old-no-panic pairs "PROVED (old-no-panic)"
  (verdict PROVED, proof.statement old-no-panic). R6D_RESULTS.md's summary counts them apart ("OLD-NO-PANIC (not an
  equivalence)": 1 and 2) and its PROVED row counts 64 and 60 equivalences. A count of cat starting with PROVED gives 65 and 62.

## Theorems
- Re-elaborated all 38 files (17 + 21) in the copy at 25790c3 (lake env lean --tstack=262144, LEAN_NUM_THREADS=1, guarded, at
  most 2 at once): for each of the 65 and 62 proofs.tsv rows (equivalences and old-no-panic), the theorem is declared once, my
  output prints exactly [propext, Classical.choice, Quot.sound], and no error or sorry warning falls inside its block: 65/65 and
  62/62 (recheck_verify_es.tsv, recheck_verify_re.tsv); my axiom lines equal the producer's recheck for all of them, and over all
  theorems my outputs reproduce the producer's recheck lines 122/122 and 109/109 (axiom_lines_vs_producer_recheck.txt). 17 files
  exit 1; their errors fall in 29 + 12 theorem blocks, none of a proofs.tsv theorem, none outside a block
  (recheck_error_theorems_*.tsv).
- Kernel replay: derived modules R6dEsProof.B00-B16 and R6dReProof.B00-B20 lose exactly the 41 failing blocks (derive.awk;
  deletions only, 583 + 242 lines); all 127 proofs.tsv blocks byte-identical before and after (derive_check.txt). Compiled with
  lean -R: 38/38 rc 0, no error, 190 axiom lines all standard. leanchecker (leancheck1lp.sh): 38/38 proof modules rc 0; StrictTS
  closure of StrictTS and StrictTS.Proof.Literals at 25790c3, 49 modules, 49/49 rc 0 (names, sources and oleans byte-identical
  to the R6c check's copy at 9e54bdb, closure_vs_r6c_copy.txt); BadCtl rc 1 (rejected), GoodCtl rc 0.
- Trust scan of the 38 files (trust_scan.txt): no skipKernelTC, addDeclWithoutChecking, unsafe, implemented_by, extern, axiom,
  native_decide, ofReduceBool, Lean.Kernel, setEnv/modifyEnv, sorry, admit, trace/debug options; options only maxHeartbeats
  400000 (231) and maxRecDepth 100000 (38); imports only StrictTS and StrictTS.Proof.Literals.

## Statements
- old-no-panic (equiv_h019u001_np es sample; equiv_h009u001_np remeda last; equiv_h004u001_np remeda _last), each:
  forall vs : Vals TT [(.arr .num)], forall w, JS.exec (callFun I Old.program Old.__difftool_retRef vs) w = JS.exec (callFun I
  New.program New.__difftool_instRef vs) w  \/  exists s w', JS.exec (callFun I Old.program Old.__difftool_retRef vs) w = some
  (.error (.panic s), w'). In words: for every number array and world, the old version (its result wrapped into number |
  undefined by the return wrapper) gives the same execution as the new version, or the old run ends in a panic. The old
  versions read the array with .arrGet (StrictTS/Core/Sem.lean:432-437: JS.panic "array index out of bounds" for an index not
  below the length, "array read at a non-index key" for a key that is not an index, such as -1), the new versions with
  .arrGetOpt (undefined in both cases). So the theorems say the two agree on every input on which the old in-type read is a
  valid index; on the empty array (sample: floor(random() * 0) = 0, out of bounds; last: key -1) the old run panics by the
  model's design where JavaScript and the new version return undefined. Not an equivalence.
- np_returns.tsv = the sources: es sample `sample<T>(arr: readonly T[]): T` -> `: T | undefined`; remeda last (dbeea0a3) no
  declared return -> declared `T | undefined`; _last (b08a667d) no declared return -> `T | undefined`, its parameter also
  `Array<T>` -> `ReadonlyArray<T>`. Translated [(.arr .num)] .num -> [(.arr .num)] (.opt .num) for all three.
- stubObject b99176b2: old `stubObject(): {}` (record, no fields), new `stubObject(): object`, which the translator maps to the
  dynamic type (.dyn). The theorem compares Old.__difftool_ret() = toDyn(stubObject()) with New.stubObject() for every world: the
  old result cast to the new declared return type equals the new result (the message's "becomes any" is the dynamic type).
- isArray x2 and isDate: the old version called through the compat wrapper with the new one at T := number; initial: the
  allocated-arguments statement (arrays allocated and shorter than 2^32) at T := number.

## Refutations
- replay_v2/replay.tsv, tscheck.tsv and refuted_export.tsv byte-identical to R6c's (819d266a, 1dbd9852, 28f7a030) and R6rb's
  (ed254301, 81ac872f, 1c298fa0); the replay_v2 directories are identical too (diff -rq empty), and those were reproduced in plain
  node in checks/r6b-20261027T0150Z (86/86) and checks/r6r-20261027T0333Z (64/64); not re-run here.
- Lean confirmations: 14 and 11 blocks; every OldC_/NewC_ evaluation section equals R6c's and R6rb's for the same pair, 14/14 and
  11/11 (confirm_compare_*.tsv). The es-toolkit confirmation directory holds 9 files, all stamped in the es-toolkit run window
  (07:02Z-07:27Z), and none of its 14 pairs is a remeda pair (confirm_window.txt); the mixed attempt stays outside the manifest
  (scratch/r6d_attempts/es_confirm_mixed/).

## Cost
- Producer guard_secs.txt: 99 jobs, 2.098 core-h (as reported 2.10). Tokens not checked.
- This check: 168 guarded jobs, 0.561 core-h (recheck 0.361, compile 0.178, replay 0.022, copy and lake checks 0.000). Light
  analysis (jq, awk, diff, cmp, sha256sum, git show/diff/ls-tree/hash-object) unguarded. Nothing written into StrictTS's trees;
  lake ran only in my copy (--no-build). My one g1.sh call (the rsync copy, 0.000 core-h) wrote its guard log to
  evidence/logs/g1; moved into logs/g1_rsync_copy_20261027T082706Z.log.

## Notes
- The old-no-panic pairs are labelled "PROVED (old-no-panic)" in r6d_table.tsv and in the chunk records (see Counts).
- StrictTS's message calls the remeda return types "none, inferred T -> T | undefined"; np_returns.tsv and the sources show the
  new versions declare T | undefined. Its "{} becomes any" for stubObject is the dynamic type of the translation (new declared
  type `object`).
