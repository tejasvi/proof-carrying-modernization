RESULT: R6r (StrictTS's remeda refactoring study) agrees with the delivery: 862/862 frozen pairs, PROVED 54 (all-worlds; 35 at one generic instance; 7 are helpers in test files), REFUTED 9 Lean-confirmed + 55 Node only, UNKNOWN 744; of the 160 "provable" pairs, 81 have no translated target (uncalled module-level const arrows), so the provable label is vacuous for them; 54/54 theorems re-elaborate with exactly the standard axioms and pass a kernel replay; 64/64 node replays and 9/9 Lean confirmations reproduce.

# R6r: evidence check

Checked by an agent of the evidence owner (the evidence-owner session), 2026-10-27 03:33Z-04:05Z (date -u). Copies under
~/fv_paper/replay/r6r-20261027T0333Z/: r7/ = cp -rL of ~/strictts/scratch/r7 (diff -rq empty, 0 links); tree/ = rsync -rtL of
~/strictts without scratch/ and .git (0 links; 938 tracked files byte-identical to HEAD d57b59f by git hash-object,
copy_vs_HEAD.txt); recheck/, confirm/, r6rreplay/, probe/ = the Lean and probe files run.

## Objects and hashes (all as announced)
- tools/difftool/r6r/R6R_RESULTS.md at 7907c5f (git show, read-only, GIT_ALLOW_PROTOCOL=file; no partial clone): de746d59...
  (copy R6R_RESULTS.md). R6R_EVIDENCE_SHA256SUMS a95639c9...: 1,902/1,902 OK in the original and in the copy.
- Lists = the addendum (prereg/ADDENDUM_R6r_remeda_inputs.md e19195aa): r7_testable.txt fec09171... (862), r7_provable.txt
  14c45704... (160), pairs_SHA256SUMS 41e73814... (-c in ~/strictts/scratch/hist_remeda: 7,124/7,124 OK). The committed
  copies at 7907c5f of these lists, r6r_table.tsv (a0d92081), tscheck.tsv (81ac872f), confirmations.tsv (27eb6949),
  target_kind.tsv (8429e4a7) and refuted_export.tsv (1c298fa0) equal the scratch files.
- Tool: git diff 2ea47b8 bbe90b4 touches only HANDOFF_20261023.md and tools/difftool/r6b/; bbe90b4 -> 7907c5f only
  tools/difftool/r6b/ and r6r/; so the Lean sources and tool code of the run are those of 2ea47b8 (= 43132a8 + HANDOFF).
  Dist hash recomputed in the copy (sha256 of the concatenated tools/difftool/dist/*.js, sorted): dbe5a9c27002f8aa.

## Counts (r6r_table.tsv and, independently, the 29 chunk records, verdict of each pair's target function)
- Table ids = the 862 testable pairs, each once; provable=yes rows = the 160 provable pairs.
- PROVED 54 (all all-worlds), REFUTED 9 Lean-confirmed + 55 Node only, UNKNOWN 744; the chunk records give the same
  category for 862/862 (table_cat.tsv vs chunk_cat.tsv). Provable 160 = 54 / 9 / 2 / 95. inst column non-empty for 35 of
  the 54 PROVED (one generic instance, __difftool_inst); domain column empty in every row.

## The 81 provable pairs without a translated target
- 81 provable rows have the reason "target X not found in the translation", all UNKNOWN; target_kind.tsv classes all 81
  as module-const-function. With a target: 54 PROVED, 9 + 2 REFUTED, 14 UNKNOWN.
- Rule: frontend/src/functions.ts topFunDecl (lines 59-71) lifts a module-level `const f = (...) => ...` to a function
  only when called through a reference (calls.ts 529/592, exprs.ts 337/377); the top-level loop (functions.ts 778) pre-
  translates only function declarations. Probe re-run with the copy's frontend (probe/): t4 (`export const f = ... =>`,
  unused) gives funs := []; t5 (`export function f`) gives [fDef]; t6 (t4 plus a function calling f) gives [gDef, fDef].
  t4/t5 equal the producer's probe outputs except the header comment.
- R6/R6b (es-toolkit): of the frozen 79 provable pairs, exactly 1 is of this kind: 2024-07-21_4c285773_startsWith
  (src/compat/string/startsWith.ts, `export const startsWith = (...) => ...`), UNKNOWN with "target startsWith not found
  in the translation" in r6_table.tsv and in r6b_table_v2.tsv (d19256bf). So R6's "79 in the subset" includes one pair
  whose target the translator does not produce.

## The 54 theorems
- proofs.tsv lists exactly the 54 PROVED pairs (all-worlds, standard axioms), in 18 batch files.
- Re-elaborated one file at a time in the copy (cd tree; lake env lean --tstack=262144; LEAN_NUM_THREADS=1; guarded;
  16 rc 0, 2 rc 1): for each of the 54, the theorem is declared once, my output prints exactly '[propext,
  Classical.choice, Quot.sound]' (= the producer's recheck output), and no error or sorry warning falls inside its lines:
  54/54 (recheck_verify.tsv). The errors of the 2 failing files fall in 3 theorems of non-PROVED pairs and their _wf
  variants (recheck_error_theorems.tsv).
- Kernel replay: the 18 files as modules R6rProof.B00-B17 (batch_map.tsv); B11 and B12 lose exactly the 6 failing blocks
  (derive.awk; deletions only: 40 and 80 lines; derive_ranges.txt); the 54 PROVED blocks are byte-identical before and
  after (proved_blocks_identity.tsv). Compiled with lean -R (18/18 rc 0, no error; the compile outputs print exactly the
  standard axioms for all 54). leanchecker (leancheck1lp.sh): 18/18 proof modules rc 0; the StrictTS import closure of
  StrictTS and StrictTS.Proof.Literals, 48 modules (= the R6b check's closure; all 48 oleans byte-identical to that copy's),
  48/48 rc 0; controls BadCtl rc 1 (declaration type mismatch), GoodCtl rc 0.
- Trust scan of the 18 files (trust_scan.txt): none of skipKernelTC, addDeclWithoutChecking, unsafe, implemented_by,
  @[extern], axiom, native_decide, ofReduceBool, Lean.Kernel, setEnv/modifyEnv, sorry, admit or debug/trace options;
  options only maxHeartbeats (93) and maxRecDepth (18); imports only StrictTS and StrictTS.Proof.Literals.

## Refutations
- 795 .mjs files of the 64 replay directories scanned: relative imports only, the only process use is process.on
  handlers, "http" only in source comments (node_replay_scan.txt). node v22.22.1, old and new per pair, from the copy:
  64/64 both rc 0, no stderr, my outputs equal the recorded out.json on both sides, old differs from new
  (node_replay_compare.tsv). Replay directories = the 64 REFUTED pairs.
- Lean confirmations: confirmations.tsv's 11 blocks = the 9 Lean-confirmed pairs + 2 with reasons. My re-runs (2 files
  from the recheck, 5 re-run, 3 rc 0 and 2 rc 1 with complete evaluation sections): for the 9, OldC_/NewC_ sections equal
  the run records, old differs from new, and the Lean outcome equals the node outcome on both sides (confirm_verify.tsv).
  sampleImplementation (b08a667d): Lean prints `return []` for both versions; node shows the old version returning its
  argument array (#1 identity label) and the new one a fresh []: a difference in object identity only. swapArray
  (035ae147): the old version reads index 1 of a one-element array; StrictTS panics by design (array index out of
  bounds), node returns [undefined, undefined]; the new version agrees.
- Type checks (tscheck.tsv, recomputed): 27 calls valid in both versions, 36 in neither, 1 in the new only (isEmpty,
  9c79944e). With refuted_export.tsv: the 27 = 24 calls of module-internal functions + 3 of exported ones (flat,
  randomInteger, stringToPath); the 36 = all exported; the 1 = exported. The 24 internal functions are _chunk x2,
  _dropLast x2, _pick x3, _processItem, _swapString, _take, shiftDecimalPoint, swapArray, voidReducer, the ...Implementation
  helpers (chunk, dropLast, randomString, range, sample x2, splitAt, take, takeLast) and the test helpers func1/func2.
  Spot checks in the clone (git show at the pairs' commits): sampleImplementation, _pick and func1 (a test file) carry no
  export; flat is exported with overloads.
- Test-file helpers among the PROVED: 7 (isNumber, defaultTo x3, func1, func2, sub; *.test.ts), so 47 are library source.
  R6 and R6b: 1 (greet, src/function/spread.spec.ts).
- refactor/style/chore commits (remeda has no "perf" type: chore 235, style 32, refactor 2): 27 PROVED and 3 REFUTED:
  zipWith() (valid in neither version), func1() and func2() (test helpers in isDeepEqual.test.ts that now throw).

## Cost
- Producer: guard_secs.txt from 02:24Z, 101 jobs, 1.134 core-h; the 101 guard logs in ~/strictts/logs give 1.137 core-h.
  The $26.27 token figure was not checked.

## For the paper (no paper text edited here)
- R6r is labelled, not pre-registered; inputs fixed before the run (addendum). Qualifications to state: 81 of the 160
  "provable" pairs have no translated target, so only 79 were reachable (54 PROVED, 11 refuted, 14 unknown); 35 of the 54
  proofs hold at one instance of the type parameters; 7 PROVED pairs are test-file helpers; of the 64 counterexamples,
  36 are calls that neither version's declared types admit and 1 is admitted only by the new one, and 24 of the 27
  admitted calls go to module-internal functions. In refactor/style/chore commits no behaviour change is visible to a
  typed caller of an exported function.
- R6/R6b: 1 of the frozen 79 provable pairs (startsWith 4c285773) has no translated target for the same reason.

## Discrepancies and disclosures
- The producer's description of the 24 internal calls ("the ...Implementation helpers, plus func1/func2") leaves out the
  underscore internals, shiftDecimalPoint, swapArray and voidReducer; the count 24 and the classes are right.
- 25 new objects appeared in ~/strictts/.git at 03:49:11Z (HEAD unchanged at d57b59f); none of my commands writes git
  objects (only show, diff, log, rev-parse, ls-files, config --get, one status --porcelain at 03:34Z).
- Four g1.sh calls of this check (rsync, three probe runs; 0.000 core-h each) wrote their guard logs to
  ~/fv_paper/evidence/logs/g1 (20261027T033602Z_4003698, 033639Z_4070904, 033640Z_4072175, 033641Z_4073807); all other
  jobs log under logs/ here. Nothing was written into StrictTS's trees; lake ran only in my copy, which no run changed.
- Compute: 110 guarded jobs, 0.305 core-h (recheck, confirmations, compile, replay, node replays), plus the four g1 calls.
