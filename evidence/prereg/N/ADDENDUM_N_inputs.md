# Addendum N: frozen inputs (PREREG_N_v1)

Written by the paper's evidence owner at 2026-10-25T17:22:52Z, before coblean runs any in-scope NIST program. This file is never
edited; changes go to DEVIATIONS.md. Copies of the files named here are in `N/`.

- coblean's draft, adopted as part of this addendum: ADDENDUM_N_inputs_draft_v2.md, sha256
  df5320439844efe3ab94444b31a8fab01c05a0d31b271121b02f0a31a5979d3b (suite and EXEC85 configuration, extraction and
  manifest, GnuCOBOL reference and flags, the NIST pin with both diffs, the open-error table, the file-directory rule,
  the runner and its outcomes, the report parser and its check, the runs, self-tests, sha256 list, the two diffs).
- NIST pin: coblean snapshot coblean-nist-20261025T1714Z = 20261024T2306Z plus tools/cobolfe/parser.py (WRITE ...
  ADVANCING as a plain WRITE, the D2 decision), CobolRun.lean (open errors for absent files through env.openError) and
  tools/nist. Checked by the evidence owner: `diff -rq` of the two trees without .lake and third_party lists only those
  three; the 43 compiled Cobol modules (Cobol.olean and Cobol/*.olean) are byte-identical in both trees, only
  CobolRun.olean differs (lists in N/oleans_*.txt).
- Rulings on the draft's points: (1) status 35 also for OPEN EXTEND of an absent non-OPTIONAL file (COBOL 85 defines
  35 for INPUT, I-O and EXTEND); accepted. (2) Parser check: IX, IC and IF totals equal; 282 of 293 reports equal one by
  one; the 11 others are accepted as documented exceptions, because the programs count verdicts they do not print or
  print one they do not count: SQ201M, SQ207M, SQ208M, SQ209M, SQ210M, NC114M, NC135A, SM106A, NC102A, NC218A, SQ101M.
  The outcome rule compares the summary counts as well, so those verdicts are still compared. (3) Outcome rule: pass
  also requires equal summary counts (stricter than PREREG_N_v1; accepted). "The same abend" means that both systems
  abend with equal verdict vectors and, where both report the I/O status of the abending statement, the same status;
  otherwise the program fails. "error" (cobolrun ends without an outcome: crash or memory limit) is reported apart, as
  an infrastructure outcome. (4) Run (a), the same runner with the unmodified 2306Z front end, labelled as such,
  measures the statement that every program stops at its first report line under 2306Z; run (b) with the NIST pin is
  the measured run; accepted.
- Named limits, reported with the results: an absent OPTIONAL file opens with status 00 where COBOL 85 gives 05 (the
  hook cannot express it, and the front end drops OPTIONAL; 11 program/file pairs); a file that the program creates
  later with OPEN OUTPUT is not flagged, so an earlier OPEN INPUT, I-O or EXTEND of it gives 00 where COBOL 85 gives 35.
  Those programs keep their natural outcome.
