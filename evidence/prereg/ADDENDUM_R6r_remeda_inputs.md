# Addendum: inputs of the second es-toolkit-style refactoring study (remeda), fixed before the run

Recorded by the evidence owner at 2026-10-27T02:34:45Z from StrictTS's message (received about 02:33Z, before its run chain started at
02:34:25Z by run_chain.log). Not a pre-registration of an experiment: like R6, the inputs and the tool are fixed before
any run, and the study is reported as labelled. StrictTS calls it "R7"; in our records it is R6r (R7 is the T4 Java
total-correctness item).

- Library: remeda (MIT), read-only clone at d02c3bdb5e18cfa53e76f33f4ae525adce515379 (2026-10-25); every commit touching
  src/ or packages/remeda/src/: 397 commits, 1,308 changed functions (producer's counts, to be checked).
- Tool: StrictTS master 2ea47b8 (the R6b tool, 43132a8 merged).
- Lists in ~/strictts/scratch/r7/ (lines "scan/<pair id>" relative to ~/strictts/scratch/hist_remeda/), hashes recomputed
  by the evidence owner at 2026-10-27T02:34:45Z, equal to the message:
  - r7_testable.txt: 862 lines, sha256 fec0917117e41f05da5b6d7f0200c78c02d3eb2ddbc0ec005bf4f8fab360c8ba
  - r7_provable.txt: 160 lines, sha256 14c45704e0089ee8c1d43f5a8d797b21f0d2143753fa0ed32125ac27bee4c95d
  - pairs_SHA256SUMS: 7,124 lines, sha256 41e738141715ed1793fb01164ebb384864a79673c6ddb0bb200a91f70cdedefc
- Deliverables (as R6): a verdict or a recorded reason for every listed pair; a plain Node.js replay of every refutation
  and, in the subset, a Lean confirmation; every counterexample call type-checked against the public signatures of
  both versions; every PROVED theorem re-checked with lake env lean, standard axioms only.
- Producer estimate: about 1 h wall, about 2 core-hours, the StrictTS session alone (no helper agents).
