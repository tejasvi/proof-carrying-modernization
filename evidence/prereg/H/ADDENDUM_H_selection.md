# Addendum H: the selection (PREREG_H_v1)

Written by the paper's evidence owner at 2026-10-25T16:35:36Z, before any H run. This file is never edited; changes go to
DEVIATIONS.md. Copies of the files named here are in `H/sel/`.

- Selection table: H_selection.tsv (60 rows in README order), sha256
  327ce976460d0ba5de87fa5287f25caad8ab2754f84ceff3b880cff4c6079349; side file H_selection.variants.tsv,
  04b96816f8e2cee8caeef9330e0613dd6dd6122fae346846f819d8ac7eb04f9d.
- Script: veriforch scripts/h_select.py, sha256 0bd4880b2e65a61d41c20bb56f36133f86abd4dd5796a066ab2110431d8b0cc2,
  run offline on the Theorem checkout at 98e995d4daced70a0a4aa2c810854b88720735f1
  (~/veriforch/targets/theorem_oss_verify_proofs) and the upstream bare repositories
  (~/veriforch/targets/theorem_upstreams). The evidence owner's re-run gives byte-identical table and side file, and
  an independent recount (own code) of the sizes of the 5 selected entry points, skcms/iccprofile_info and
  tinyobjloader/fuzz_tobj_c gives the same numbers.
- Population 60; harnesses all C: 23; C entry points: 22; of size at most 20,000 lines: 5, so all 5 are selected.
  Processing order (ascending size, ties by name): cgif/cgif_file_fuzzer 2,178; cgif/cgif_rgb_fuzzer 2,178;
  yajl-ruby/json_fuzzer 4,877; cjson/cjson_read_fuzzer 5,280; bzip2/bzip2_compress_target 8,190.
- Readings recorded with the table: skcms/iccprofile_info has a .c harness but links skcms.cc (C++), so it is not a
  C entry point (6,051 lines); tinyobjloader/fuzz_tobj_c is C but has 22,071 lines; varnish/esi_parse_fuzzer links
  libunwind.a, a toolchain runtime, and counts as C but has 149,433 lines. The selection is the same under the side
  file's other readings (case-insensitive directory names, top-level exclusion only, newline count only).
- Part two ranking by |ln(size / 5,280)| over the four selected entry points other than cJSON, before part one decides
  which of them qualify: yajl-ruby/json_fuzzer (0.079); bzip2/bzip2_compress_target (0.439); cgif/cgif_file_fuzzer (0.886); cgif/cgif_rgb_fuzzer (0.886).
- Pins: cirlean as recorded when part one starts. The paper's decision of 2026-10-25 on cirlean's type-punned access
  defect (DEVIATIONS) applies: the pinned semantics is kept, and H's claimed theorems and UB findings get the same
  per-program check.
- Before the addendum, veriforch fetched OSS-Fuzz at bd2ce219 and assembled the seed corpora as data (no build, no
  run on the semantics).
