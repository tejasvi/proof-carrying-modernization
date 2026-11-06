# Addendum: inputs of R6e, a labelled re-run of the frozen es-toolkit and remeda pairs with StrictTS master 4016a4a,
# fixed before the run

Recorded by the evidence owner at 2026-10-27T10:26:03Z from StrictTS's registration message; nothing runs before this record is
confirmed. Not a pre-registration of an experiment. This is the last re-run of the series taken for the current revision
(results delivered after about 18:00Z on 2026-10-27 go to the next revision).

- Tool: StrictTS master 4016a4a8d8fdaa4f551979cab833d7123e7a0c2b (detached worktree ~/strictts_ws/r6e; HEAD verified).
  New against R6d's 25790c3: cheapest proof alternative first; typeof case split (StrictTS/Proof/DynTypeof.lean,
  dt_typeof_cases); more generic-constraint instances; checker types for unannotated wrapper parameters; an old-no-panic
  proof gets verdict UNKNOWN (proof attached) in the raw JSON. Difftool dist fa8ed9263a105167, frontend dist
  654dcdf41dd337e5 (producer's values, to be checked). Producer regressions at 4016a4a: corpus 181/0/0, selftest PASS,
  bench 43/44 + 23/23, 0 wrong.
- Inputs (hashes recomputed by the evidence owner, identical to R6d's): es-toolkit scratch/r6e/es/: r6_testable.txt 408069f7...,
  r6_provable.txt f2f81a47..., pairs_SHA256SUMS bf561176...; clone 9c0cac2e... . remeda scratch/r6e/re/: r7_testable.txt
  fec09171..., r7_provable.txt 14c45704..., pairs_SHA256SUMS 41e73814... (also under the R6 file names, same hashes); clone
  d02c3bdb... . Scripts: R6d's with paths changed, plus collect_v2.js (collects old-no-panic proofs) and report.js labels.
- Reporting as for R6d (OLD-NO-PANIC in its own column, never PROVED; statement/domain/inst columns; exact np statement and
  np_returns.tsv; comparison with r6d_table_v2.tsv; confirmations in the main manifest; replays, type check with export
  status, recheck).
- Disclosed first looks (not blind): (d) the 19 R6d proof-search timeouts with a reordered script: es-toolkit trim, trimEnd,
  trimStart (ec79293f), padEnd, padStart (e3525153) PROVED; isObject 63e3755f, padEnd/padStart 0061e902, isArrayLikeObject,
  lowerFirst, upperFirst, difference, intersection, at, toString de79ea8e UNKNOWN; remeda sampleImplementation 8b6f1bc7,
  drop/take/uniqueImplementation 4da195bb UNKNOWN. (e) a loss check of all 127 R6d PROVED and old-no-panic pairs with the
  d17e200 tool (all equivalences stayed; xor e595e5e0 allocated -> all-worlds; np pairs UNKNOWN with np proofs). (f) 10 other
  R6d UNKNOWN pairs (all UNKNOWN; dist rebuilt partway). (g) typeof: isObject 63e3755f PROVED, isArrayLikeObject UNKNOWN; 12
  R6d PROVED typeof pairs still PROVED. (h) classification-only rescans: remeda in-subset 85 -> 87; es-toolkit unchanged.
- Producer's expectation: es-toolkit about 70 equivalences (+6), remeda unchanged unless the 2 newly in-subset pairs prove.
