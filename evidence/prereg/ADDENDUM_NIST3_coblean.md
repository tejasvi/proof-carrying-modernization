# Addendum: labelled NIST COBOL85 census of coblean snapshot 20261028T0551Z (N3), plan fixed before the run

Recorded by the evidence owner at 2026-10-28T06:50:15Z from the COBOL maintainer session's proposal (message of 2026-10-28 ~06:5xZ); no run of this set has started
(the COBOL maintainer session: nothing starts before the evidence owner's go). Not a pre-registration: a labelled measurement, reported apart from the
pre-registered NIST run of Section 3 and from the labelled second run N2. Purpose: one census of the latest checked snapshot,
so that the paper can state the effect of the merges since N2 with one number per outcome instead of per-snapshot partial
counts (tab:snapshots counts only the programs re-run for each snapshot).

- Semantics: coblean snapshot coblean-20261028T0551Z (merge 7; checked in checks/merge7-20261028T0554Z), in a fresh copy.
- Runner and inputs: the frozen run_nist.py of N2 over all six modules, in the pre-registered order, with N2's D2 front-end
  change. Declared differences from N2, and no others: (1) trees built with cobolrun_files_v3.diff; (2) COB_SWITCH_1=ON
  COB_SWITCH_2=OFF for NC211A; (3) SYSIN is not supplied, so NC109M stays unsupported in the census. An optional second,
  labelled sub-run with run_nist_sysin.py covers NC109M only and is reported separately, never merged into the census.
- Outcomes, as in N2: per program pass / fail / unsupported (with the construct) / front-end error / undefined behaviour /
  timeout; and, for programs that run to the end, the test verdicts that GnuCOBOL's report lines give, agreeing or not.
- Comparison: a transition table of every program whose outcome differs from N2, each with the merge to which the COBOL maintainer session
  attributes it (the attribution is the COBOL maintainer session's statement; the evidence owner checks a sample of attributions against the
  snapshot diffs).
- Deliverables: a sealed directory with SHA256SUMS: the built tree's manifest, per-part results, the census totals, the
  transition table, the list of declared differences with the commands, guard logs and the cost.
- Evidence-owner check after delivery: an independent re-run from a fresh copy of the snapshot (all programs or a stated
  sample), a recount of the totals and the transitions, and the declared differences checked against the runner diff.
- Cost per the COBOL maintainer session: about 1-2 guarded core-hours, no model tokens.
