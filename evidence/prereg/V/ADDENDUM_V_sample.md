# Addendum V: the frozen sample (PREREG_V_v1)

Written by the paper's evidence owner at 2026-10-25T17:54:18Z, before any corpus program runs. This file is never edited; changes go
to DEVIATIONS.md.

- PREREG_V_v1.md sha256 a2ada24b857e7b877f35a13f09c1f2abef0752ff0b83a28417519c17ce5541e1 (manifest SHA256SUMS_V_v1,
  32748147e9cdb10a078f1caf89e07e63ed83b75214fa5b6a1a8748783701c037).
- Frame: V/build_frame_v.py on V/list.tsv -> V/frame_V.tsv, 1,368 programs (population 1,812; excluded 444: LASX 197,
  LSX 192, Altivec 23, NEON 1, HVX 1, Polybench 30), sha256 072ca051ac5a52d61a8479899cb3fb4e27656a46467b99dc61c4cbe03918551b.
- Order: M/draw_m.py V/frame_V.tsv llvm --seed fv-paper-prereg-V-2026-10-25 -> V/order_V_full.tsv; the sample is its
  first 200 rows, V/sample_V.tsv (header + 200 rows, column `order` = processing order), sha256
  d0f38820db2e0f0516ea8262ec6c3b71dc1b04398dd14efa21a3206191dfeb94; checked by an independent recomputation.
- Composition: C 185, C++ 15; main(int, char**) 35 (harness), reading stdin 1; Regression/C gcc-c-torture 131.
