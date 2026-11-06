# Addendum M, coblean's front end, set 1 (PREREG_M_v1, Part FE)

Written by the paper's evidence owner at 2026-10-25T16:59:02Z, before any population mutant is built. This file is never edited;
changes go to DEVIATIONS.md. Copies of the files named here are in `M/cobolfe/`.

- coblean's draft of the frozen inputs, adopted as part of this addendum: ADDENDUM_M_cobolfe_draft.md, sha256
  75157ffb653c885f4b5744e8c20d73ebba4e87f4b1c7f12f001a8dc09b0c2119 (pin coblean snapshot 20261024T2306Z,
  tools/cobolfe/*.py; harness mutfe_run.py 272c6042..., make_suite.py 021c69fd...; suite_old.json 7e28ce7e...: the 14
  GnuCOBOL testers of the evidence package with their recorded N and seeds; baseline and controls). Its frozen files
  are listed in SHA256SUMS_frozen_v1.txt (d96ca097...), which the evidence owner checked against the files.
- Enumeration tool: enum_py.py, sha256 60b285b607bc8f04540855d50a2851f4ca73d948eb33a6622c802c7bcec6d124. Candidate
  list: cands_cobolfe_v1.tsv, sha256 5857d1dfb58512d7594d25777a541a1ae360e002a5a2909c6ad89028be91f39c, 3,790 candidates
  (ROR 353, AOR 163, LOG 335, NEG 24, CND 705, LIT 374, STMT 1,836). The evidence owner's re-run of the tool on the pin
  gives identical bytes; every LIT candidate is n -> n + 1; the ids parse identically with and without CSV quoting.
- Accepted choices: (1) the wall limit per tester is 10 times its baseline wall time, at least 120 s (cost); a mutant
  that reaches it is killed, as PREREG_M_v1 counts a time limit exceeded where the original passes. (2) The Python
  forms of the families and the exclusions E1-E5 for code that only builds error messages, as the tool's docstring
  writes them. STMT includes module-level statements, among them 25 imports.
- Set 1 order (M/draw_m.py, bridge cobolfe): order_set1.tsv (columns order, id), sha256
  9f9726d9ddb8a5917bd31c8d150db7db1d0aea6650ab75e24d97b59855d8f0e9. The first 30 tested candidates in this order form
  set 1; they run on the old suite, and later on the extended suite.
- Set 2 is drawn with the secret S2 (sha256 committed in PREREG_M_v1) after coblean sends the extended suite's
  sha256, from the candidates not attempted for set 1.
