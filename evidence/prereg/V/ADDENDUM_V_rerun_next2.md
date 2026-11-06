# Addendum: labelled re-run of sample V at cirlean next2 (424e821), inputs fixed before the run

Recorded by the evidence owner at 2026-10-27T19:42:51Z from cirlean's message; the output directory did not exist when this was
recorded. Not a pre-registration; a labelled re-check reported beside V (next revision).

- Sample: prereg/V/sample_V.tsv sha256 d0f38820db2e0f0516ea8262ec6c3b71dc1b04398dd14efa21a3206191dfeb94 (recomputed).
- Runner: ~/cirlean_work/llvmsub/tools/run_prereg_v9.py sha256 7b85c170cddd3b79f3a8517b07571a9dc3f45cb3923366216bed4b8c6c80b62d
  = run_prereg_v8.py (d21f1ef2...) with only a docstring, the CIRRUN path and the default --stop-utc changed (diff
  run_prereg_v9.diff 3f30fb10..., re-checked by the evidence owner with diff).
- cirrun: ~/cirlean_frozen/next2_424e821_20261027/.lake/build/bin/cirrun sha256
  85da63b47499540c87b2924d7fa54569845adee63251092d60fa83954269a30f (recomputed; in the frozen manifest 2ff29f3a...).
- Output: ~/cirlean_work/llvmsub/runV_next2 (new). Delivery: sealed dir, results.tsv sha, per-kind counts against
  runV_next_e6ac99a (e8f4129c) and runV (ac02a5a3), every changed row with old and new kind/sub, guard logs.
- Declared before the run: a faster cirrun can make a non-terminating program reach the 20 GiB address-space cap before
  the 120 s limit; such a row shows CRASH with resource=oom instead of TIMEOUT, and the delivery lists each one.
