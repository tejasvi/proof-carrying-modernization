RESULT: equiv-lean's relational proofs for es-toolkit difference (4ec747ea) and intersection (576b136a) at ts-esdiff 92f75e6 check out: manifest 4240/4240, tracked 2426 = 92f75e6, both theorems and the 4 Sets lemmas print exactly propext, Classical.choice, Quot.sound in fresh processes (from the producer-equivalent build and from my own from-source build), the 35-module closure (11 EquivLean + 24 StrictTS a15926a) replays rc 0 from my builds, the slices equal the frozen R6 pair files, and the 4 frontend outputs regenerate byte for byte with the a15926a frontend and with master 7be8414's (incl. 91241e8).

# es-toolkit relational proofs (difference 4ec747ea, intersection 576b136a): evidence check

Checked by an agent of the evidence owner, 2026-10-27 14:15Z-14:23Z (date -u). Check dir:
~/fv_paper/evidence/checks/esdiff-20261027T1415Z; copies in ~/fv_paper/replay/esdiff-20261027T1415Z (0 symlinks).

## 1. Hashes and commit
- Delivery note ESDIFF_DELIVERY.md 7e53fd69... and manifest SHA256SUMS_92f75e6-esdiff.txt 8496421f... (4240 lines) as
  announced; sha256sum -c in the kit tree: 4240/4240 OK (logs/sumcheck_before.out).
- Tree HEAD 92f75e6ef0cfb3b4bbde6de0b24d39f5b4f19a1a; 2426 tracked files = the commit's blobs (git hash-object, 0 differ).
- 825a15c (master) .. 92f75e6: 16 added files (Bridge/TS/Sets.lean, 4 Gen modules, Demo/TS/EsToolkit.lean, two pair dirs
  with inst.ts, slices, meta.json) + README.md modified; no other file modified or deleted (logs/diff_master_825a15c.txt).
- The StrictTS pin is outside the kit manifest: ~/equivlean_work/vendor/strictts-a15926a, HEAD a15926a3718..., 743 tracked
  files = the commit (0 differ); its origin is the local ~/strictts (no partial clone).

## 2. Statements (fresh process, logs/statements_axioms.out)
- difference_equiv / intersection_equiv: for every Impl I, every world w (TT := EsDifferenceOld.TT), all a0 a1 and number
  arrays xs ys with heap cells (.arr .num, a0) = xs and (.arr .num, a1) = ys and a0, a1 < w.next:
  Equiv (ArrObs w.next) (old call on [arr a0, arr a1] run from w) (new call likewise). No other hypothesis: a0 = a1 is
  allowed (aliasing), no length bound, element values unrestricted (NaN, -0 included).
- Equiv R t s = Sim R t s /\ Sim (flip R) s t, Sim R t s = Safe s -> Safe t /\ every outcome of t has a related outcome of s;
  for JS.exec (Option outcomes, core instance instBehavesOption) Safe = isSome (termination), Runs = (= some o): a thrown
  exception or a panic is an outcome. So old terminates iff new terminates, and the outcomes are ArrObs-related.
- ArrObs n: WorldObs n on the final worlds (console output equal; every heap cell of every kind at an address < n equal;
  oracle indices randIdx, nowIdx, extIdx equal) and either the same returned array address below n, or two returned
  addresses >= n whose array contents are equal; or equal errors. Not compared: cells >= n other than the returned arrays'
  contents (the new version's fresh Set), the returned addresses themselves, next, jobs/timers/clock/seqNo/unhandled, the
  oracle functions (only their indices).
- Instance: the theorems are about the monomorphised difference_numberRef / intersection_numberRef that the pinned
  frontend emits for the wrapper inst.ts (written by an agent, an equiv-lean agent), which calls the generic function at
  T = number; the wrappers do not occur in the statements. inst.ts identical old/new: 4729e658... (difference),
  f6312e91... (intersection), as in the note.
- Lemmas: svz_num_equiv (SameValueZero on numbers is a JSMap equivalence), svz_normKey_num, setOfArr_has_num
  (has on new Set(ys) = ys.any svz), arrFilter_pure_at (filter with a callback that is pure at the call's world).

## 3. Provenance
- The six slice/meta files equal the frozen R6 pair files (prereg/R6/pairs_SHA256SUMS bf561176..., entries
  scan2_rpsc/<id>/...): 6/6 SAME (logs/provenance_slices.txt). Old: filter with includes; new: new Set + filter with has.
- The four Gen files regenerate byte for byte from my copies with the a15926a frontend (node v22.22.1, typescript 5.9.3
  copied from ~/strictts/frontend/node_modules, the pin's lock version): 4/4 SAME, hashes = the note (logs/regen*.out,
  logs/regen_sha.txt). With master 7be8414's frontend (git archive; 91241e8 is its ancestor): 4/4 SAME (regen_master.out).
- Scans: no trust escape in the 11 closure modules (the two hits are the word "unsafe" in comments of Bridge/TS/Behaves);
  none of the note's translator-bug patterns in the 8 TS files; no strict-equality primitive .prim (.seq ...) in the Gen
  outputs (the .seq hits are statement sequencing); filter matches 4 lines (positive control) (logs/trust_and_pattern_scan.txt).

## 4. Build, axioms, kernel replay
- The 11 EquivLean modules compile from my copy against the pin's oleans (compile/compile.tsv, rc 0; one unused-variable
  warning in Core/Sim). Then, from source: the 24-module StrictTS closure of StrictTS.Frontend.Prelude and
  StrictTS.Proof.Tactics (logs/strictts_closure.txt; = the note's list) and the 11 EquivLean modules against it
  (compile2/compile2.tsv, all rc 0). These oleans differ in bytes from the vendor's and the producer's (24/24, 11/11).
- Axioms in fresh processes on both builds: difference_equiv, intersection_equiv, svz_num_equiv, svz_normKey_num,
  setOfArr_has_num, arrFilter_pure_at: exactly [propext, Classical.choice, Quot.sound] (6/6 twice); the printed statement
  text is identical between the two builds.
- Kernel replay (tools/leancheck1lp.sh, LEAN_PATH = my from-source builds): 35/35 modules rc 0 (replay/*.tsv).
  Controls: BadCtl (False := True.intro added with debug.skipKernelTC) compiles and is rejected, rc 1, "declaration type
  mismatch"; GoodCtl rc 0 (replay_controls/).

## 5. Disclosures and cost
- One read-only command (sha256sum -c) ran with the kit tree as working directory. git status --porcelain was run in the
  vendor StrictTS pin (may refresh its .git/index). The first regeneration failed because I had not copied frontend/lib;
  rerun OK (its re-copy of the inputs hit read-only files from the first copy; diff -rq shows the inputs equal my copies).
  The first control compile failed on a syntax error in my control file; fixed and rerun.
- typescript 5.9.3 for the frontend was taken from ~/strictts/frontend/node_modules (version checked, not its tarball hash).
- Producer cost (about $20) not checked. This check: 0.038 core-h over 11 guarded jobs (guard/).
