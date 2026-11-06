# R6d addendum (2026-10-27): old-no-panic rows relabelled

The evidence owner asked for this after the check checks/r6d-20261027T0825Z, which passed. No verdict or
count changes.

In `r6d_table.tsv` the cat column of the three old-no-panic pairs read "PROVED (old-no-panic)", so a count
of rows starting with PROVED gave 65 for es-toolkit and 62 for remeda, not 64 and 60.
`r6d_table_v2.tsv` labels these rows "OLD-NO-PANIC (not an equivalence)" and is otherwise identical: only
the cat of those 3 rows changes. The pairs:
- es-toolkit `sample` fa2afcd6;
- remeda `last` dbeea0a3;
- remeda `_last` b08a667d.

The `statement` column still says `old-no-panic`.

- es-toolkit: `es/r6d_table_v2.tsv`, sha256 143bea1660cb52eebce73e55c857447dd099000045c2201551bb29d0584755a5.
- remeda: `re/r6d_table_v2.tsv`, sha256 5c37aae6246b20587ba3a7de747c8b0b92fca2736b78cc854c9a3e00cf6406bb.
- Generator: `report_v2.js`, which is R6d's `report.js` with that label. The draft tables `R6D_draft_v2.md`
  are regenerated with it.
- Manifest R6D_ADDENDUM_SHA256SUMS: 7 files, checked from `~/strictts_ws/r6d/scratch/r6d/`, sha256
  ea36707959aa93567607d72e6ec1028fed56846ac7e1e7d23ae47bbb4cf24b57.

The run's raw output, the chunk JSONs (strictts-diff/v1), gives these three functions verdict PROVED with
`proof.statement` `old-no-panic`. They are evidence and stay as they are. A consumer of that schema must
read `proof.statement` (INTERFACE.md: old-no-panic is WEAKER than equality), as verif-orchestrator's
adapter does. From the next tool version on, the difftool reports such a function as UNKNOWN with the
old-no-panic proof attached, so that its verdict alone never counts as PROVED.
