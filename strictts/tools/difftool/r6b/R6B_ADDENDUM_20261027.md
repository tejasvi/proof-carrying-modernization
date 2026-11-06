# R6b addendum (2026-10-27): Lean confirmation files, and two proofs on the old parameter types

Asked for by the evidence owner after the check checks/r6b-20261027T0150Z, which passed.

1. **Lean confirmation files.** R6B_EVIDENCE_SHA256SUMS listed only the Lean files that hold PROVED
   theorems. The run's nine Lean files with confirmation blocks are now frozen in
   `~/strictts_ws/loosenull/scratch/r6b/evidence_confirm/`, with their outputs. Three of them held only
   confirmations: toString, trimEnd, trimStart. `confirmations.tsv` (sha256 9a126576...) maps each pair to
   its confirmation namespace and file. There are 14 blocks: the 10 Lean-confirmed refutations, plus 4
   attempts without confirmation, with the reasons R6 gives (shuffle: object identity; pullAt and at:
   designed panics; deburr: an external call without a recorded answer). Manifest
   R6B_ADDENDUM_SHA256SUMS, 22 files, checked from `scratch/r6b/`, sha256
   b7fc0a989aecb3e5a8833afed95e554ad1a03397a7931e617cda34b4059c38ce.

2. **Proofs on the old version's parameter types.** `endsWith` and `startsWith` (e3525153) are PROVED
   through the compatibility wrapper. Their new versions made every parameter optional, so the theorem
   compares the two versions on the OLD version's parameter types (`(string, string, number?)`) and not on
   the new version's wider domain. `r6b_table_v2.tsv` (sha256 d19256bf...) adds a column `domain` that
   marks this for both. It also marks 9 UNKNOWN pairs where the wrapper was tried without a proof.
   Otherwise the table is identical to r6b_table.tsv. The R6b count stays 54 PROVED: 52 on the full
   domain and 2 on the old parameter types.
