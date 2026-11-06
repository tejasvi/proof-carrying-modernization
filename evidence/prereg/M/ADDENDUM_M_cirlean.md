# Addendum M, cirlean (PREREG_M_v1)

Written by the paper's evidence owner at 2026-10-25T17:10:22Z, before any population mutant is built. This file is never edited;
changes go to DEVIATIONS.md. Copies of the files named here are in `M/cirlean/`.

- cirlean's draft of the frozen inputs, adopted as part of this addendum: ADDENDUM_M_cirlean_draft.md, sha256 34ebd25ace12ee31492ed068b6720e2295642013a6b1833292e3b09823ec4e2f (pin, scope files, tool,
  harness, suite, kill rule, stillborn and sorry rules, controls and baseline).
- Enumeration tool: enum_m_cirlean.py, sha256 abec03846eb6465f0be4881d22e522e81c83bbe55cbac0db2dd6b6152207e107. Candidate list: candidates_cirlean_ffab71e.tsv, sha256 cc17b9ea1da241da05714d19123646aec6c039226a04e56a78077d8cf67c098e, 1,307 candidates (AOR 282, CND 164, LIT 510, LOG 98, NEG 26, ROR 201, UBG 26). The evidence
  owner's re-run of the tool on the pin gives identical bytes; every candidate lies inside a def of an in-scope file;
  every LIT candidate is n -> n + 1; the ids parse identically with and without CSV quoting.
- Order (M/draw_m.py, bridge cirlean): M/cirlean/order.tsv (columns order, id), sha256 c0eb75d11fef1d675361134fd54f9bb91edcc4f12d80a6f69c59e06f803e45d9.
- Readings recorded in DEVIATIONS.md at 2026-10-25T17:10Z apply (baseline exclusions, scope readings, at most 2 mutants at a
  time). Also: pin cirlean ffab71e (a git archive of the pin was used for the re-run); the draft's sums file SHA256SUMS_M_cirlean_draft (5c5b40a8...) and self-test selftest_enum.py (b7d56aff..., PASS 54/54 by cirlean); the draft says at most 8 jobs at once, but at most 2 mutants run at a time (DEVIATIONS).
