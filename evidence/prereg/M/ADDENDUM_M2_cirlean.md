# Addendum: M2, labelled re-runs of cirlean's semantics mutants against an extended difftest suite, inputs fixed before the run

Recorded by the evidence owner at 2026-10-27T17:13:59Z from cirlean's registration messages; nothing runs before this record is
confirmed and the cirlean lead gives the GO. Not part of PREREG_M_v1: labelled measurements, reported beside M.

- Plan: ~/cirlean_work/mutation/M2_PLAN_v2.md sha256 67f301efef2bd80128e284d4601e2214a95dbedc4b237e5ed7b813863e5a0cc1
  (v1 d16d445b4fa2bce4... kept unchanged; both recomputed).
- M2a: the 30 mutants that M built (orders 1-11, 13-26, 29, 30, 32-34), at the same pin (cirlean ffab71e), with the same
  tools and kill criterion as PREREG_M_v1, on the extended suite. Reported as an area-informed follow-up: the new cases
  cover formatted output, string-to-number conversion and floating point, where 13 of M's 23 survivors lie, and the
  cirlean lead chose these areas knowing M's summary.
- M2b: the next 30 built mutants of the frozen order (prereg/M/cirlean/order.tsv c0eb75d1, fixed 2026-10-25), from order 35
  on by M's prefix rule; stillborn mutants are recorded and do not count; the driver refuses a start at or below 34.
- Suite: M's 175 cases, followed by the 238 defined t_* cases of the six files at difftestx be7773c (fmt, fpx, strconv; each
  case file's lines in file order). The 18 ub_* lines are left out (evidence owner's choice at registration, prep config
  exclude_fn_prefixes ["ub_"]): C leaves those programs undefined, so a mutant's different output on them says nothing
  about the semantics; 3 of them MATCH at the pin.
- Exclusions (DEVIATIONS 2026-10-25T17:10Z reading): a case whose status at the M2 baseline (unmutated cirrun at ffab71e on
  the extended suite) is not MATCH cannot kill and is reported as excluded.
- Stop rule: one run per mutant, stopping at the first baseline-MATCH case that fails. Old-suite kill iff that case's index
  is at most 175; extended-suite kill iff such a case exists.
- Reported: for M2a and M2b, kill rates on the original and on the extended suite with Wilson 95% intervals; mutants killed
  by new cases only; for M2a, reproduction of M's builds (outcome, sorried proofs, mutated sha256) and verdicts; exclusions.
- Inputs as in the plan's section 2: pin ffab71e frozen copy (manifest 559b1f42...), unmutated cirrun 01e5df80..., candidates
  cc17b9ea..., order c0eb75d1..., M results 29b12c0e..., M baseline c4fdc98d..., original cases 09a7dfe6..., built files
  2a16fb46...; the six new files (list fba182fc...): fmt.cpp fa9a3ea7..., fmt_cases.txt a3fd830a..., fpx.cpp d62f6535...,
  fpx_cases.txt dd9489ca..., strconv.cpp 4a85ef57..., strconv_cases.txt 4370f01f... .
- Tools: M's run_mutant_m_v3 / run_suite_m / case_m.sh / build_cirrun_v4 / suite_build_m / enum_m_cirlean unchanged; new
  drive_m2_v2.py 941b4f2df217d65f..., prep_suite_m2_v2.py f259aaa68d431a6e..., compare_m2_v2.py 90a460e51a509a8c...
  (recomputed by the evidence owner).
- Blinding record: ~/cirlean_work/scratch/m2_blinding, SHA256SUMS 0ca32c19... (5/5 verified): the brief sent to the test
  author (rog) at 2026-10-27T16:06:29Z by the cirlean lead (0f06a658...); rog's tool log (452 calls) shows no read, list or
  grep of M's files, results or plans; rog's own statement is pending and is added to that record before delivery.
- Baseline classes of the new defined cases at ffab71e and at e6ac99a (~/cirlean_work/mutation/M2/baseline_classes,
  SHA256SUMS da9fec4c..., 3/3 verified): 157 and 158 of 238 MATCH; failures by class (ffab71e / e6ac99a): missing model
  43/43, format or conversion outside the modelled subset 30/30, unsupported operation 4/1, documented limit 3/6, wrong
  value 1/0. A separate labelled measurement for the trust section, not part of M2's verdicts.
- Cost: estimate 2.9-3.6 core-h, about 2 h wall, at most 2 mutants at a time (user and the coordinating session machine rule); caps: outer 6.0
  core-h (M2a then M2b), 2.8 per drive, 0.35 per mutant.
