# Addendum M, JimpleLean, set 2 (PREREG_M_v1; DEVIATIONS 2026-10-27, "M JimpleLean set 2")

Written by the paper's evidence owner at 2026-10-27T01:30:12Z, after the extended suite was frozen and before any set 2 candidate is
built or run. This file is never edited; changes go to DEVIATIONS.md. Copies in `M/jimplelean_set2/`. A labelled second
measurement after PREREG_M's stop (Tue 03:00Z); not pre-registered.

- Extended suite, frozen in ~/fv_paper/replay/jset2-20261027T0100Z on the set-1 pin (JimpleLean 20261025T0300Z): set 1's 44
  programs (corpus_v1, unchanged) plus 19 new ones (the bit-exact float tester FloatSemCases without its 19 Double.compare-NaN
  cases; FloatCmpGrid at Semantics:108; AbsNew and AbsNewUncaught at :320; ConcatIndy and ConcatConst at :403; 13 nop variants
  of set-1 programs at :520). Manifest MANIFEST_reads.sha256 5e21e3e8b6bd752dafc145fbbb96445feb7d34dee53bf8385f0eb1b0ba98171a
  (2,364 files), re-verified by the evidence owner with sha256sum -c (rc 0). Baseline runs/baseline_set2.jsonl
  0155c455564850c66588e5ee440cafe2f87cad8373620b9316415a7d39d3895e: 63 of 63 programs agree with the JVM on the unaltered semantics.
- Secret released: S2J = `fv-paper-prereg-M-jimplelean-set2-32f4c8d21b7df23ba937e2a9a7cdf85fb30b534854e71facf49cc2d7c53f3940`; its sha256 (string without newline) equals the one committed in DEVIATIONS
  (1ea2fe5fa2e9860972e2828972cf06955c5f4bfac4865c27c529b5ced8206b0d).
- Set 2 order: `M/draw_m.py jimplelean/population_v2.tsv jimplelean order2_full.tsv --seed S2J --exclude set1_attempted.tsv`
  (population fa8a182d..., 452 candidates; set1_attempted.tsv d62c61d5449fd268cf94d773ea12fd0065450968c08da8f011c7980fbb751e49: set 1's attempted ids, order_v2 positions 1-33)
  -> 419 candidates, none from set 1; order2_full.tsv 22401a7a93cea9a371bdf15c9b5731b81fb79cec26b57df10b7e6f88705c398d; order2.tsv (columns order, id) 7039055823831561c131124d6acb67922f12b0664db4a007b85df8398268817f; an
  independent recomputation (sha256 of "S2J|jimplelean|id", sorted) gives the same order.
- Runs: in order2, the first 30 candidates that build, each on the old suite and on the extended suite from one build
  (runner run_set2.py in the manifest), stillborn rule as set 1; headline: detected on the old vs the extended suite for these
  30. Set 1's 16 of 30 stays reported as is.
