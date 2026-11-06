# Addendum: inputs of R6d, a labelled re-run of the frozen es-toolkit and remeda pairs with StrictTS master 25790c3,
# fixed before the run

Recorded by the evidence owner at 2026-10-27T07:02:26Z from StrictTS's registration message; nothing runs before this record is
confirmed. Not a pre-registration of an experiment; reported beside the earlier runs, with the latest run per library
as its result.

- Tool: StrictTS master 25790c31dbc3f219b1fe8331167240134ecc001c (detached worktree ~/strictts_ws/r6d; HEAD verified):
  const-arrow (0f1e6b8) + generic-compat (bfb237f: compat wrapper for generic functions, generic/non-generic pairs and
  differing instances when the wrappers' signatures agree, return-type wrapper __difftool_ret, heap-split reuse of a
  known cell, array-size lemmas, and the statement kind old-no-panic). Difftool dist 3f0e0ee59cd91535, frontend dist
  654dcdf41dd337e5 (producer's values, to be checked). Producer regressions at 25790c3: corpus 181/0/0, selftest PASS,
  bench 43/44 + 23/23, 0 wrong.
- old-no-panic (weaker than equivalence, attempted only when nothing else is proved): for every argument list and world,
  the old run equals the new run, or the old run ends in a designed panic. Reported in its own column, "OLD-NO-PANIC
  (not an equivalence)", never counted as PROVED; np_returns.tsv gives each such pair's declared and translated return
  types (old -> new); the exact Lean statement goes in the results file.
- Inputs (hashes recomputed by the evidence owner, equal to prereg/ADDENDUM_R6_inputs.md and ADDENDUM_R6r_remeda_inputs.md):
  es-toolkit scratch/r6d/es/: r6_testable.txt 408069f7... (415), r6_provable.txt f2f81a47... (79), pairs_SHA256SUMS
  bf561176...; clone ~/strictts_ws/constarrow/scratch/rescan/clone_es HEAD 9c0cac2ee6c0f807099723d7b226f3b65e976d5c (verified).
  remeda scratch/r6d/re/: r7_testable.txt fec09171... (862), r7_provable.txt 14c45704... (160), pairs_SHA256SUMS 41e73814...
  (also present there under the R6 file names, same hashes); clone scratch/rescan/clone_remeda HEAD d02c3bdb (verified).
- Deliverables: as R6c/R6rb, plus the statement column, the domain column marking both wrappers, and a pair-by-pair
  comparison against R6c and R6rb.
- Disclosed first looks (not blind): (a) the 8 pairs of the R6c/R6rb addendum; (b) the rescans with 09d1e8c; (c) with the
  generic-compat tools 04:15Z-06:35Z: es-toolkit isArray 35fbc4ca and 4bb457ad, initial 9089b3b4, stubObject b99176b2
  PROVED, sample fa2afcd6 old-no-panic, sample e549de2e, isTypedArray 895c10cd, isObject 63e3755f, difference 4ec747ea,
  intersection 576b136a, at 94cf7ff6 UNKNOWN; remeda isDate 7900d2c2 PROVED, last dbeea0a3 and _last b08a667d old-no-panic,
  isStrictlyEqualImplementation 33caa142, sampleImplementation 8b6f1bc7, drop/take/uniqueImplementation 4da195bb UNKNOWN.
