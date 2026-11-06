# Addendum: labelled re-run of sample V at cirlean e6ac99a, inputs fixed before the run

Recorded by the evidence owner at 2026-10-27T16:11:16Z from cirlean's two messages; the run's output directory did not exist yet when
this was recorded (checked at 16:11:06Z). Not a pre-registration; a labelled re-check reported beside V.

- Sample: prereg/V/sample_V.tsv sha256 d0f38820db2e0f0516ea8262ec6c3b71dc1b04398dd14efa21a3206191dfeb94 (unchanged; recomputed).
- Runner: ~/cirlean_work/llvmsub/tools/run_prereg_v8.py sha256 d21f1ef2254844658fde4b8bdfbd12c26d6cab5eb34da088e1123bc54b7f0f2e
  = run_prereg_v7.py (982b23d3..., the V runner with the approved crash-fix environment) with only the docstring, the CIRRUN
  path and the default --stop-utc changed (diff run_prereg_v8.diff d9deb81b..., re-checked by the evidence owner with diff).
- cirrun: ~/cirlean_frozen/next_e6ac99a_20261027/.lake/build/bin/cirrun sha256 232b7a0d02c180c8da94568c8ad1cacafa6d388dd0bd3510995b968089c4c29b
  (recomputed); clang, gcc and the cirrun environment as in v7.
- Output: ~/cirlean_work/llvmsub/runV_next_e6ac99a (new). Delivery: sealed dir, results.tsv sha, per-kind counts old -> new,
  every changed row with old and new kind/sub against runV (results.tsv ac02a5a3), crash-fix rows marked, guard-log paths.
