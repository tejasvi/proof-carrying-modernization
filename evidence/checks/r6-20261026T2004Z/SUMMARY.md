RESULT: R6 agrees with the delivery: 415/415 frozen pairs, PROVED 46 (43 all-worlds, 3 allocated-arguments), REFUTED Lean-confirmed 9, REFUTED Node only 77, UNKNOWN 283; 46/46 theorems re-elaborated with the standard axioms only; 86/86 counterexamples reproduce in plain node; 9/9 Lean confirmations reproduce. Four record points below, none changes a count.

# R6 (StrictTS refactoring audit of es-toolkit v1.0.0..v1.52.0): evidence check

Checked by a fork of the evidence owner (the evidence-owner session), 2026-10-26 20:04Z-20:17Z (date -u). Copies: ~/fv_paper/replay/r6-20261026T2004Z/
(scratch_r6 = copy of ~/strictts_ws/rally/scratch/r6, difftool_r6 = copy of tools/difftool/r6, tree = git archive of 10ec829 plus a
copy of the worktree's .lake, node_replay = copy of replay_v2, recheck/confirm = copies of the Lean files run). diff -rq of both
copies against the originals: empty; no symlinks in any copy.

## Objects and hashes (all as announced)
- R6_RESULTS.md 214521cb..., r6_table.tsv c2caa541..., R6_EVIDENCE_SHA256SUMS 328ea254... (sha256sum -c: 1,184/1,184 OK in the original
  and in the copy), pairs_SHA256SUMS bf561176..., r6_testable.txt 408069f7..., r6_provable.txt f2f81a47... (= prereg/R6 copies; addendum
  8733b38d...). Pair sources re-checked now: pairs_SHA256SUMS -c in ~/strictts/scratch/hist_es 3,642/3,642 OK.
- git (GIT_ALLOW_PROTOCOL=file, no promisor): 10ec829 = f6a4ec0 plus 10 files under tools/difftool/{src,dist} (git_10ec829_files.txt);
  53f98fcd changes only 13 files under tools/difftool/r6 (git_53f98fc_files.txt), and its blobs equal the delivered files. Worktree status:
  only untracked frontend/node_modules.
- Copy at 10ec829: `lake build --no-build` reports "All targets up-to-date (49 jobs)" (Lean v4.35.0), so the copied oleans match the
  commit's sources; the archive differs from the worktree only by untracked test outputs and tools/difftool/r6.

## Coverage and counts (recomputed from r6_table.tsv and, independently, from the run's chunk JSON records)
- Table ids = the 415 frozen testable pairs exactly (each once); provable flag = the 79 frozen provable pairs exactly.
- Counts: PROVED 46 (43 all-worlds, 3 allocated-arguments), REFUTED Lean-confirmed 9, REFUTED Node only 77 (73 outside the subset +
  4 provable: object identity 1, designed panic at a non-index read 2, external call without a recorded answer 1), UNKNOWN 283 (263
  outside the subset + 20 provable). On the 79 provable: 46 / 9 + 4 / 20. Every UNKNOWN and every Node-only row has a reason.
- Chunk records (chunks/list_*.json, 415 functions): verdict per pair = table category for all 415, Lean flag included
  (confirmedBy node+lean 9, node 77); UNKNOWN pairs with all 1,500 random inputs: 226 (as reported).
- UNKNOWN reason classes: outside the subset 217, generic without an instance 24 + 1, external modules 20, translated signatures
  differ 9, no proof 8 (proof search timed out 4, allocation differs 2, loops and Map 1, string library 1), fuzz harness cannot run 2,
  target not found 1, module-level state 1 (unknown_reason_classes.txt). The 20 provable UNKNOWN split as the report states.
- PROVED by commit type: fix 26, feat 3 (= the report's 29 fix/feat), docs 5, chore 3, style 3, perf 2, test 2, refactor 1, other 1.
  Generic instance on PROVED: T := number 22, T := string 1, none 23.

## The 46 theorems
- proofs.tsv lists exactly the 46 PROVED pairs, statement kinds as in the table. The 15 Lean files are byte-identical to the run
  directories' batch files (30/30 .lean/.out equal).
- Re-elaborated one at a time in the copy (`lake env lean --tstack=262144 FILE`, LEAN_NUM_THREADS=1, guarded): per theorem, declared
  once as `theorem`, my output prints exactly `'<thm>' depends on axioms: [propext, Classical.choice, Quot.sound]` (the producer's
  recheck output agrees), and no error and no sorry warning falls inside its lines: 46/46 (recheck_verify.tsv).
- Files with errors (7 of 15 exit 1): every error lies in a theorem of the 8 provable UNKNOWN pairs with "no proof", or in the
  all-worlds variant of the 3 pairs whose allocated-arguments variant is PROVED (xor e595e5e0, sum 34be6d76, without 030817ee);
  none in a PROVED theorem (recheck_error_theorems.tsv).
- Source scan of the 15 files: no skipKernelTC, addDeclWithoutChecking, unsafe, implemented_by, extern, axiom, native_decide,
  ofReduceBool, sorry or admit; options only maxHeartbeats 400000 and maxRecDepth 100000 (trust_scan.txt).
- Statements (3 pairs, lowest sha256 of the pair id): greet 61d4acba (equiv_h008u001), sum 715bc60b (equiv_h019u001), drop 6739c840
  (equiv_h027u001, through the wrapper at T := number). Each states: for every host model I, every argument vector of the declared
  types and every world w, `JS.exec` of the old program's function on those arguments in w equals `JS.exec` of the new one, i.e. the
  same outcome (result or exception, output) and the same final world. The allocated-arguments form (e.g. equiv_h012u001_wf) instead
  quantifies over worlds and array addresses that are allocated in w (heap lookup gives an array, address below w.next) with each
  argument array shorter than 2^32 elements.

## The 86 refutations and the 9 Lean confirmations
- 86 replay directories = the 86 REFUTED rows. Every driver and transpiled module scanned: imports relative only; no fs, process,
  network, environment or absolute-path use (906 .mjs).
- node v22.22.1 from the copy, old and new per pair: 172/172 exit 0, no stderr; my stdout equals the producer's out.json for 86/86 on
  both sides; old differs from new for 86/86; the old/new outcome strings occur in the table's recorded evidence for all 82 rows whose
  differing parts include the outcome; the 4 rows that differ only in final arguments (pullAt x2) or console output (delay, divide)
  match the recorded values (node_replay_compare.tsv, node_vs_table.tsv).
- Lean confirmations: the old/new evaluation sections of my re-runs (8 from the recheck files, trimEnd from its own run file) equal the
  run records' Lean outputs for 9/9, old differs from new, and the Lean outcome equals the node outcome on both sides
  (confirm_verify.tsv).

## Highlights traced (row + my replay)
- perf/style: uniq([-0]) [-0] -> [0] (d7c37c9f, Lean + Node); zip() [] -> RangeError (0f26a676); zipWith([], 8, undefined) [] ->
  RangeError (e37b2957); toPath("..") 4 -> 3 empty segments (0edff252); toPath("]") [] -> ["]"] (c739a739); areObjectsEqual({ buffer:
  undefined }, { hasOwnProperty: undefined }) TypeError -> false (5cb0b788). REFUTED rows by type: perf 5, style 1 (no refactor), so
  "six commits typed perf, refactor or style" holds.
- docs/test/bench: trimEnd("", "") "" -> throw (4069aa6b, Lean + Node); takeRight([8, 8], -1) [8] -> [] (25cd782b, Lean + Node);
  divide(0, 1) console ["0 1"] -> [] (25841dca, Node).

## Record points (no count changes)
1. replay_v2/replay.tsv shows "arguments after the call=undefined" for recorded and replayed values on the 7 rows whose differing
   parts include the final arguments, so its "agree" is not a comparison of that part there; the out.json files, the table's
   evidence and my replay agree on those rows.
2. The Lean source of trimEnd's confirmation is outside R6_EVIDENCE_SHA256SUMS: scratch/difftool/history-20261026T091833Z-2179242/
   lean/batch_00.lean (sha256 172d6ea6...; .out 95c7d68c...), copied to replay/r6-20261026T2004Z/confirm/. The other 8 confirmations
   sit in files of the manifest.
3. One PROVED pair is a helper in a test file: greet in src/function/spread.spec.ts (61d4acba, a feat commit), counted among the
   29 fix/feat "type-only" changes.
4. The allocated-arguments hypothesis also bounds each argument array's length below 2^32; the report's wording ("worlds whose
   argument arrays are allocated") leaves the bound out.

## Questions for producers (the StrictTS maintainer session)
- Should replay.tsv carry the final-argument values (point 1), and should trimEnd's confirmation file join the manifest (point 2)?
- Does the paper count greet (a test-file helper) among library functions, or state the pair list's file scope (point 3)?

## Cost and method notes
- 19 guarded jobs (coreh_guard_v2, ulimit -v 32 GiB, LEAN_NUM_THREADS=1, one Lean job at a time via pjobs_v3 N=1): 0.128 core-h.
- Not re-run: the scan and fuzzing phases (1,163 commits, 1,071 functions; 162 + 494 + 336 + 79 = 1,071 holds) and the tool's
  regressions; the frozen pair inputs and the run's records are what the counts rest on.
