RESULT: R6e agrees with the delivery. es-toolkit (R6's frozen 415 pairs, StrictTS master 4016a4a): 70 equivalences (67 all-worlds, 3 allocated-arguments; 28 at one generic instance; 11 on the old version's parameter types through the compat wrapper, 1 at the new version's return type through the return wrapper), 1 OLD-NO-PANIC (not an equivalence; raw verdict UNKNOWN with the proof attached), 10 Lean-confirmed + 76 Node-only refutations, 258 unknown. remeda (R6r's frozen 862 pairs): 61 equivalences (all-worlds; 37 at one instance; 1 compat wrapper), 2 OLD-NO-PANIC, 9 + 55, 735. Against R6d (r6d_table_v2.tsv) exactly 7 and 1 changes, all disclosed first looks. 71/71 and 63/63 theorems exactly standard axioms with no error inside; 40 proof modules + the 50-module StrictTS closure replay rc 0.

# R6e: evidence check

Checked by an agent of the evidence owner (the evidence-owner session), 2026-10-27 11:38Z-12:12Z (date -u). Copies under
~/fv_paper/replay/r6e-20261027T1138Z/: tree/ = rsync -rtL of ~/strictts_ws/r6e without scratch/, .git and logs/ (0 symlinks;
1,007/1,007 tracked files of 4016a4a byte-identical by git hash-object, copy_vs_4016a4a.txt); r6e/ = cp -rL of scratch/r6e
(diff -rq empty, 0 links); recheck_es/, recheck_re/ = the 18 + 22 Lean files run; esreplay/, rereplay/ = the derived modules.
Inputs registered before the run: prereg/ADDENDUM_R6e_inputs.md (5e826840).

## Objects and hashes
- Results (git show 54f8a29:tools/difftool/r6e/R6E_RESULTS.md, read-only, GIT_ALLOW_PROTOCOL=file; ~/strictts is not a partial
  clone): sha256 3ee9800e... = announced (copy in delivered/).
- Manifest R6E_EVIDENCE_SHA256SUMS 223e550f... 4,047/4,047 OK in the copy before and after, and in the producer tree after
  (manifest_check_before.txt, manifest_check_after.txt).
- Lists = the addendum (= R6d's): es/r6_testable 408069f7 (415), r6_provable f2f81a47 (79), pairs bf561176 (-c in
  ~/strictts/scratch/hist_es 3,642/3,642 OK); re/r7_testable fec09171 (862), r7_provable 14c45704 (160), pairs 41e73814 (-c in
  hist_remeda 7,124/7,124 OK) (manifest_and_lists.txt).
- Tool: git diff 4016a4a..54f8a29 touches HANDOFF_20261023.md, README.md, tools/difftool/r6e/ (30 files, the results) and
  tools/public/ (the NoPanic measurement: RESULTS.md, lean/NoPanicDiag.lean, nopanic.py, results/proofs.tsv); no difftool code
  and no StrictTS library file. The run used the worktree at 4016a4a (HEAD verified). Dist hashes recomputed in the copy (recipe as
  in the R6d check): difftool fa8ed9263a105167 (22 files), frontend 654dcdf41dd337e5 (20 files), as registered. The copy's StrictTS
  library is up to date (lake build --no-build StrictTS StrictTS.Proof.Literals: 52 jobs up to date).

## Counts (tables and, independently, the chunk records: verdict of each pair's target function)
- Table ids = the testable lists, each once; provable=yes rows = the provable lists; table category = chunk category for 415/415
  and 862/862 (es_chunk_cat.tsv, re_chunk_cat.tsv, table_checks.txt). In the raw records the three old-no-panic pairs have
  verdict UNKNOWN with proof.statement old-no-panic attached (scripts/chunk_cat.sh maps them to OLD-NO-PANIC); the table labels
  them "OLD-NO-PANIC (not an equivalence)". No count of PROVED includes them.
- es-toolkit: PROVED (all-worlds) 67, PROVED (allocated-arguments) 3, OLD-NO-PANIC 1, REFUTED 10 Lean-confirmed + 76 Node only,
  UNKNOWN 258. inst on 28 equivalences (chunk notes agree); domain among the equivalences: old version's parameter types (compat
  wrapper) 11, new version's return type (return wrapper) 1 (stubObject). Provable 79: 54 + 3 equivalences, 1 old-no-panic, 9 + 4
  refuted, 8 UNKNOWN. No "target not found" row. Equivalences by commit type: refactor/perf/style/chore 16, fix/feat/revert 36,
  docs/test/other 18 (as reported).
- remeda: PROVED (all-worlds) 61, OLD-NO-PANIC 2, REFUTED 9 + 55, UNKNOWN 735; inst on 37 equivalences; compat wrapper on 1
  (isDate). Provable 160: 60 equivalences, 2 old-no-panic, 9 + 2 refuted, 87 UNKNOWN (doesNothing is not in the frozen 160).
  Equivalences by type: 30 / 26 / 5 (as reported).
- Changes against R6d's corrected tables (r6d_table_v2.tsv; R6D_ADDENDUM_SHA256SUMS 7/7 OK), changes_es.tsv and changes_re.tsv:
  exactly 7 and 1. es-toolkit: trim, trimEnd, trimStart (ec79293f) and isObject (63e3755f) UNKNOWN -> PROVED all-worlds on the
  full declared domain; padEnd, padStart (e3525153) UNKNOWN -> PROVED all-worlds on the old version's parameter types (compat
  wrapper); xor (e595e5e0) PROVED allocated-arguments -> PROVED all-worlds, at one instance. remeda: doesNothing (a5b389b8)
  UNKNOWN -> PROVED all-worlds at one instance (the instance table's readonly number[]). The producer's compare_r6d.tsv lists the
  same 8. Not blind: trim x3, padEnd, padStart are first look (d), isObject (g), xor (e); doesNothing's in-subset classification
  came from the rescan (h), its proof was not looked at before the run (producer's statement; nothing contradicts it).

## Theorems
- Re-elaborated all 40 files (18 + 22) in the copy at 4016a4a (lake env lean --tstack=262144, LEAN_NUM_THREADS=1, guarded, at
  most 2 at once): for each of the 71 and 63 proofs.tsv rows (equivalences and old-no-panic), the theorem is declared once, my
  output prints exactly [propext, Classical.choice, Quot.sound], and no error or sorry warning falls inside its block: 71/71 and
  63/63 (recheck_verify_es.tsv, recheck_verify_re.tsv); my axiom lines equal the producer's recheck for all of them. Over all
  theorems my outputs reproduce the producer's recheck axiom lines 130/132 and 111/111 (axiom_lines_vs_producer_recheck.txt): the
  two differences are equiv_h002u001 and equiv_h005u001 in es batch 104726Z, unproved pairs whose proofs hit the heartbeat limit
  (producer [propext, sorryAx, Classical.choice, Quot.sound], mine "does not depend on any axioms"; axiom_line_diffs_es.txt), the
  run-to-run variation noted in the R6b/R6c checks. 16 files exit 1; their errors fall in 27 + 12 theorem blocks, none of a
  proofs.tsv theorem, none outside a block (recheck_error_theorems_*.tsv).
- Kernel replay: derived modules R6eEsProof.B00-B17 and R6eReProof.B00-B21 lose exactly the 39 failing blocks (derive.awk;
  deletions only, 570 + 254 lines, 0 added); all 134 proofs.tsv blocks byte-identical before and after (derive_check.txt). Compiled
  with lean -R: 40/40 rc 0, no error, 204 axiom lines all standard. leanchecker (leancheck1lp.sh): 40/40 proof modules rc 0;
  StrictTS closure of StrictTS and StrictTS.Proof.Literals at 4016a4a, 50 modules (R6d's 49 plus StrictTS.Proof.DynTypeof; the
  root StrictTS.lean differs from R6d's only by that import; the other 48 sources are identical), 50/50 rc 0; BadCtl rc 1
  (rejected), GoodCtl rc 0.
- typeof case split (typeof_lemma.txt): StrictTS/Proof/DynTypeof.lean has one theorem, typeof_cases (v : Val TT .dyn): a nine-way
  disjunction of the answers of Dyn.typeof v, each with what it says about the runtime type (Dyn.base v).1; proved by unfolding
  Dyn.typeof and case analysis on the base. No axiom, sorry, opaque or extern, no hypothesis beyond v. The tactic dt_typeof_cases
  (tools/difftool/lean/DiffPrelude.lean) is elaboration code that applies it.
- Trust scan of the 40 files (trust_scan.txt): no skipKernelTC, addDeclWithoutChecking, unsafe, implemented_by, extern, axiom,
  native_decide, ofReduceBool, Lean.Kernel, setEnv/modifyEnv, sorry, admit, trace/debug options; options only maxHeartbeats
  400000 (243) and maxRecDepth 100000 (40); imports only StrictTS and StrictTS.Proof.Literals.

## Old-no-panic
- The three statements (equiv_h019u001_np es sample fa2afcd6; equiv_h009u001_np remeda last dbeea0a3; equiv_h004u001_np remeda
  _last b08a667d) are byte-identical to R6d's (np_statements.txt): for every number array and world, the old version (through the
  return wrapper) gives the same execution as the new version, or the old run ends in a panic. np_returns.tsv byte-identical to
  R6d's (20326a59, a93d69f8). All three hold at T := number.

## Refutations
- replay_v2/replay.tsv, tscheck.tsv and refuted_export.tsv byte-identical to R6d's (es 819d266a, 1dbd9852, 28f7a030; re ed254301,
  81ac872f, 1c298fa0); replay_v2 directories identical (diff -rq empty) (refutation_identity.txt). Not re-run in node here (done in
  checks/r6b-20261027T0150Z, 86/86, and checks/r6r-20261027T0333Z, 64/64).
- Lean confirmations: 14 and 11 blocks; every OldC_/NewC_ evaluation section equals R6d's for the same pair, 14/14 and 11/11
  (confirm_compare_*_r6d.tsv). The es-toolkit confirmation files are stamped 10:27:51Z-10:47:26Z (the es-toolkit run), the remeda
  files from 11:00:13Z; none of the 14 es-toolkit pairs is a remeda pair (confirm_window.txt).

## Cost
- Producer: 98 guard logs, all with an exit line, 1.862 core-h (producer_coreh.tsv; as reported 1.86). Tokens not checked.
- This check: 175 guarded jobs, 0.480 core-h (my_coreh.txt). Light analysis (jq, awk, diff, cmp, sha256sum, git show/diff/
  ls-tree/hash-object) unguarded. Nothing written into StrictTS's trees; lake ran only in my copy (--no-build).
