# Addendum M, coblean (PREREG_M_v1)

Written by the paper's evidence owner at 2026-10-25T17:10:22Z, before any population mutant is built. This file is never edited;
changes go to DEVIATIONS.md. Copies of the files named here are in `M/coblean/`.

- coblean's draft of the frozen inputs, adopted as part of this addendum: ADDENDUM_M_coblean_draft.md, sha256 128689315a02165f6283a42535d4f9908cc857db093d786e38fde2ca01f3adb7 (pin, scope files, tool,
  harness, suite, kill rule, stillborn and sorry rules, controls and baseline).
- Enumeration tool: enum_lean.py, sha256 f1956d2a1bccdfd79d535a11d6469f9556e277df0ad56a9610874889ba79df37. Candidate list: candidates_m_coblean.tsv, sha256 e13311bdd50faff8f042d1e6ce4b384d5ed65a565db74229e0836f046dad369f, 1,111 candidates (AOR 222, CND 186, LIT 322, LOG 104, NEG 27, RND 16, ROR 200, STS 34). The evidence
  owner's re-run of the tool on the pin gives identical bytes; every candidate lies inside a def of an in-scope file;
  every LIT candidate is n -> n + 1; the ids parse identically with and without CSV quoting.
- Order (M/draw_m.py, bridge coblean): M/coblean/order.tsv (columns order, id), sha256 4d42f01a7dba82f4cc22ac1d9f9d04207fbab242c54eb9b558e66ba170e85145.
- Readings recorded in DEVIATIONS.md at 2026-10-25T17:10Z apply (baseline exclusions, scope readings, at most 2 mutants at a
  time). Also: pin coblean snapshot 20261024T2306Z; RND replaces a rounding mode by truncation, STS swaps a file status with its partner code (maps in the tool's docstring).
