# Addendum: inputs of R6f, a labelled re-run of the frozen es-toolkit and remeda pairs with StrictTS master 4bef3c4,
# fixed before the run

Recorded by the evidence owner at 2026-10-27T16:39:14Z from StrictTS's registration message; nothing runs before this record is
confirmed. Not a pre-registration of an experiment. R6e's addendum called R6e the last re-run of the series for the current
revision. The user's instruction of 2026-10-27 00:13Z to include all improvements, and the producer's strong-model window
(until 2026-10-28 00:00Z), led to this run; the change is in DEVIATIONS.md. If its check passes, R6f is reported as the
fifth later version (L5); otherwise it goes to the hand-off.

- Tool: StrictTS master 4bef3c48ef13729b36c2d8fddb1632114ab44282 (detached worktree ~/strictts_ws/r6f; HEAD verified). It is
  docs-only after 94c3f97 (git diff --stat 94c3f97 4bef3c4 = HANDOFF_20261023.md only; verified). New against R6e's 4016a4a
  (producer's list): overloads translated by their implementation (26e2072); Array.from of array unions (2dd57de);
  new Array(n) filled in order (ef434f7); comparisons on any values, destructured-parameter defaults, named re-exports kept in
  slices, destructured parameters in wrappers (6c1f00c); curried functions compared applied through an uncurried sibling
  (64f3474); never inside type-level computations (8ce6e3f); global-regex match as the extern String.match:g with
  World.MatchGlobalFresh (1f9145a); the target's overload signatures left out of slices (76f7dde); conditional types by
  branch agreement and as-casts equal at the instance (94c3f97). Dist (concatenated *.js in C-locale order; recomputed,
  equal to the producer's values): frontend be5d20e43dba6571..., difftool 86fe40d63ac93dbf... . Producer regressions
  (gcompat worktree = the tree of 94c3f97; scratch/regress23): corpus 191/191 against Node, selftest PASS, benchmark
  43/44 + 23/23, 0 wrong. Lean build in the r6f worktree OK (160 jobs; producer's log scratch/r6f/lake_build_r6f.log).
- Inputs (hashes recomputed by the evidence owner, identical to R6e's): es-toolkit scratch/r6f/es/: r6_testable.txt (415
  pairs) 408069f766d08f00..., r6_provable.txt f2f81a47575d70fc..., pairs_SHA256SUMS bf561176efed4294... (hist_es, 3,642 files,
  sha256sum -c OK); clone 9c0cac2ee6c0f807... (not a partial clone). remeda scratch/r6f/re/: r7_testable.txt (862 pairs)
  fec0917117e41f05..., pairs_SHA256SUMS 41e738141715ed17... (hist_remeda, 7,124 files, OK); clone d02c3bdb5e18cfa5... .
  R6e's r7_provable.txt (14c45704...) is not copied; no chain or post-run script reads a provable list.
- Run: scratch/r6f/run_all.sh 56e6d82700cf54da... (es-toolkit chain and post-run, then remeda chain and post-run);
  es/run_chain.sh efb561db06415b83..., re/run_chain.sh 372fee89b4b92fba..., post_run.sh c56a5e373333b454... (LANES=1).
  Against R6e's scripts with r6e -> r6f applied, only comments (incl. the commit named in a comment) and one lane instead of
  two differ (diffed by the evidence owner); the other scripts are equal. Main VM, one worker, one core (taskset), nice 10,
  address space 32 GiB. Core-hour estimate 4.5; the producer stops and asks if the projection passes 6.75; hard cap 8.
- Reporting as for R6e (OLD-NO-PANIC in its own column, never PROVED; statement/domain/inst columns; np_returns.tsv;
  comparison with R6e's table; node replays; type check with export status; Lean recheck with axioms; evidence manifest;
  core-hour and token use), plus a first_look column that marks each new PROVED as tried before the run or not. Delivery:
  es-toolkit after its post-run, then remeda.
- Disclosed first looks (not blind): all runs after 10:27:51Z, in scratch/r6f/first_looks_per_pair.tsv 578b56fc28af2727...
  (155 pairs: es-toolkit 77, remeda 78) and first_looks_all.tsv 7ceadcc4dee7aa72... (199 attempts). Last verdicts
  (recounted by the evidence owner): es-toolkit 28 new PROVED, 4 PROVED as in R6e, 19 REFUTED, 26 UNKNOWN; remeda 56 new
  PROVED, 1 PROVED as in R6e, 2 REFUTED, 19 UNKNOWN. Per-change notes: ~/strictts_ws/gcompat/scratch/{holes_fl,cmp_fl,
  uncurry_fl,never_fl,ovl_fl,cond_fl}/FIRST_LOOKS.md.
- Caveat (producer's): the first looks ran on re-extracted pairs (today's slicer); R6f runs the frozen pair dirs, whose
  slices come from the R6 slicer (which dropped named re-exports), so a verdict can differ there.
- Producer's expectation (denominators = the frozen lists): es-toolkit PROVED about 98/415 (R6e 70), REFUTED 86/415,
  UNKNOWN about 231; remeda PROVED about 117/862 (R6e 61), REFUTED 64/862, UNKNOWN about 681.
