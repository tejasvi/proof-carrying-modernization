# R6 inputs: audit of es-toolkit's change history (StrictTS), frozen before the full run

Recorded by the paper's evidence owner on 2026-10-26, after StrictTS sent the inputs and before any result of the full
run. R6 is not pre-registered: it was designed after a first look at 31 pairs, disclosed below. This file is never
edited; later changes go to DEVIATIONS.md. Copies of the lists are in `R6/`.

- Tool: commit 10ec829207b1e780e917e860e65b9e23ae6a7a83 (branch rally-hist, worktree ~/strictts_ws/rally) = master
  f6a4ec0 plus difftool changes only (module-state comparison fix; generic functions compared at one instance through a
  wrapper, the instance noted in each record; confirmation drivers at that instance; instance-aware subset check).
  Regressions reported by StrictTS on that tree: corpus 180/0/0, selftest pass, bench 43/44 proved and 23/23 refuted.
- Pair lists (one pair per line, relative to ~/strictts/scratch/hist_es/):
  - r6_testable.txt: 415 pairs (94 refactor/perf/style/chore, 321 other), sha256
    408069f766d08f00464c839de64500f1d7957634b81e6e5673baae3b8a51d7a3;
  - r6_provable.txt: 79 pairs (18 and 61), all also in the testable list, sha256
    f2f81a47575d70fc795f1821a845a77837edc53dbc085cf11e98ce13d1b416ed;
  - pairs_SHA256SUMS: 3,642 files of the 415 pairs, sha256
    bf561176efed42946d89bc770503afd6dfb3dac8666b30b8b573cd456b321596 (3,642 of 3,642 OK on the evidence owner's check).
- Provable pairs: 79, not the 113 first announced; the first scan's subset check passed generic functions that were
  never translated, and the corrected scan checks them at the compared instance (34 drop out of the provable list and
  stay testable).
- First look, on the 31 pairs the first scan called in-subset: original tool 4 proved, 3 refuted (Node), 24 unknown;
  after both tool fixes 9 proved, 3 refuted, 19 unknown; one refutation (uniq of [-0]) also confirmed in Lean.
- Report categories, every listed pair accounted for: proved (with its theorem and axioms); refuted with Lean
  confirmation; refuted in Node only; unknown with the reason. Every counterexample comes with a standalone Node driver
  per version, which the evidence owner re-runs.