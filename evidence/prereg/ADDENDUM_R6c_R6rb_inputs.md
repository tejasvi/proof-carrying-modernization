# Addendum: inputs of two labelled re-runs with StrictTS's const-arrow tool (R6c on R6's frozen es-toolkit pairs, R6rb on
# R6r's frozen remeda pairs), fixed before the runs

Recorded by the evidence owner at 2026-10-27T04:10:31Z from StrictTS's registration message; StrictTS starts neither run before this
record is confirmed. Not pre-registrations of experiments: labelled re-runs of frozen inputs with a changed tool, reported
beside R6/R6b and R6r.

- Tool (both runs): StrictTS branch const-arrow at 9e54bdbc34af6edfd0d784d39a89944ad4307b80 (worktree
  ~/strictts_ws/constarrow; HEAD verified), = master d57b59f + 09d1e8c (uncalled module-level const arrows translated;
  the history scan requires the target in the translation) + 9e54bdb (StrictTS/Proof/DynOpt.lean: lemmas for an unknown
  value passed to `value?: unknown`). Difftool dist baf07b296e82b4bf, frontend dist 654dcdf41dd337e5 (producer's values,
  to be checked). Producer regressions at 9e54bdb: corpus 181/0/0, selftest PASS, bench 43/44 + 23/23, 0 wrong.
- R6c inputs (scratch/r6c/ in the worktree; hashes recomputed by the evidence owner, equal to prereg/ADDENDUM_R6_inputs.md):
  r6_testable.txt 408069f766d08f00464c839de64500f1d7957634b81e6e5673baae3b8a51d7a3 (415), r6_provable.txt
  f2f81a47575d70fc795f1821a845a77837edc53dbc085cf11e98ce13d1b416ed (79), pairs_SHA256SUMS
  bf561176efed42946d89bc770503afd6dfb3dac8666b30b8b573cd456b321596. Clone scratch/rescan/clone_es, HEAD
  9c0cac2ee6c0f807099723d7b226f3b65e976d5c (verified). Script scratch/r6c/run_chain.sh (R6b's with three path lines changed).
- R6rb inputs (scratch/r6rb/; equal to prereg/ADDENDUM_R6r_remeda_inputs.md): r7_testable.txt fec0917117e41f05... (862),
  r7_provable.txt 14c45704e0089ee8... (160), pairs_SHA256SUMS 41e738141715ed17... (all recomputed, equal). Clone
  scratch/rescan/clone_remeda, HEAD d02c3bdb5e18cfa53e76f33f4ae525adce515379 (verified). Script scratch/r6rb/run_chain.sh.
- Deliverables as R6b/R6r: verdict or reason per pair with domain and inst columns; node replay of every refutation and Lean
  confirmations inside the main manifest; type checks with export status; every PROVED theorem rechecked (standard axioms
  only); the table against R6b/R6r pair by pair.
- Disclosed first looks before this record: (a) 8 R6 pairs run one by one with the new tool (R6b's 7 UNKNOWN compat-wrapper
  pairs and startsWith 4c285773): 6 PROVED (isNaN, isFinite, isObject, isObjectLike, isLength, startsWith), isArrayLike and
  isArrayLikeObject UNKNOWN. (b) Rescans with 09d1e8c at 03:38-03:49Z (scratch/rescan/, not inputs): es-toolkit still 79 of
  R6's pairs in the subset, startsWith now with a target; remeda 160 -> 85 in the subset (all within the frozen 160): 75 of
  the 81 no-target pairs now rejected, 6 now translated (noop x2, sliceString, randomChar, trivialDefaultCase,
  joinImplementation). Because of (a), R6c's results on those 8 pairs are not blind.
