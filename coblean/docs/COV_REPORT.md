# Coverage tests for the PREREG_M survivors' features (declared later validation work)

cov-tests (fork of coblean main), 2026-10-26 08:38-09:15Z. Scratch tree ~/coblean_cov = cp -a of
~/coblean_snapshots/coblean-20261025T2114Z (live's state). Nothing in ~/coblean, any snapshot,
~/coblean_mut, ~/coblean_mutfe or ~/fv_paper was changed. Testers: ~/coblean_cov/tools/difftest/cov/
(new files only). Exact comparisons: DISPLAY lines byte for byte (Latin-1, split at line feeds only,
nothing stripped, every DISPLAY ending in '|'), GnuCOBOL exit 0 and a model `stop` signal; every
generated line checked to stay within column 72. GnuCOBOL 3.2 from the tree's third_party.

## Results (n = 60 programs per seed, seeds 1 and 2; runs/full1, runs/full2)

| feature | tester | survivor | result (s1 / s2) |
|---|---|---|---|
| 1 interleaved input files, semantics input-stream READ (hand-built IR, --inputs) | cov_f1inp.py | M #5 Exec.lean:357 | 60/60 ok, 60/60 ok |
| 1 interleaved sequential files, front-end READ (File.lean), reads past EOF (10, 46) | cov_f1multi.py | - | 60/60, 60/60 |
| 2 RECORD VARYING sequential + indexed: min/max/between/min-1, READ/WRITE/REWRITE/DELETE | cov_f2vary.py | M #7 File.lean:98, #9 File.lean:249 | 60/60, 60/60 (full2) |
| 3 ROUNDED / ROUNDED MODE (7 modes) on COMPUTE/ADD/SUBTRACT/MULTIPLY/DIVIDE | cov_f3round.py | - | 60/60, 60/60 |
| 3 ROUNDED MODE PROHIBITED vs exact-rational oracle (model only) | cov_f3prohib.py | M #11 Arith.lean:65 | 60/60, 60/60 (full2) |
| 4 DISPLAY of numeric literals (GnuCOBOL -std=default) | cov_f4disp.py --part lit | M #26 Exec.lean:209 | 60/60, 60/60 |
| 4 DISPLAY of unsigned COMP-3 / unsigned and SIGN SEPARATE DISPLAY items (-std=ibm) | cov_f4disp.py --part items | - | 60/60, 60/60 |
| 5 STRING all BY SIZE, no POINTER (static path) | cov_f5str.py | FE orders 1, 18 | 60/60, 60/60 |
| 6 M-pos documenting test (expected mismatch) | cov_f6mpos.py, f6/ | known defect | 2/2 known-mismatch |

Note: survivor #26 sits in the DISPLAY of a numeric LITERAL (`.num` operand), not of data items
(data items go through numOf + encZoned without a decimal point).

## Controls (planted faults; each caught by the new tester, unmutated baselines all 60/60 ok)

Lean mutants applied to ~/coblean_cov_mut (narrowed cobolrun import, rebuilt per mutant, file restored
after each; runs/ctl, ctl2, ctl3), seed 1 (and 2 for #11):
- #5 Exec.lean:357:62 `!=`->`==`: cov_f1inp 49/60 mismatch.
- #7 File.lean:98:34 `≤`->`<`: cov_f2vary 55/60.
- #9 File.lean:249:81 44->45: cov_f2vary 26/60.
- #11 Arith.lean:65:57 `*`->`+`: cov_f3prohib 12/60 (s1), 15/60 (s2) (first version: 1/60, then
  low-scale exact quotients were added to the generator).
- #26 Exec.lean:209:52 0x2E->0x2F: cov_f4disp lit 60/60.
- File.lean:160:26 46->47 (READ after EOF): cov_f1multi 51/60.
- Round.lean:61:22 `<`->`≤` (NEAREST-EVEN tie): cov_f3round 8/60; Arith.lean:262:81 mode->truncation:
  cov_f3round 59/60 (Round.lean:77:54 did not build: a Round.lean proof breaks; not used).
- Exec.lean:198:20 `==`->`!=` (DISPLAY of USAGE DISPLAY items): cov_f4disp items 60/60.
Front-end mutants applied to copies of the 2306Z front end (~/coblean_cov_fe/{orig,m1,m18}, runs/fectl),
cov_f5str with --fe: original 60/60 + 60/60 ok; order 1 (parser.py:1848 `s = x.tok.val`->pass)
119/120 caught (front-end crash); order 18 (parser.py:1822 `and`->`or`) 118/120 caught.

## Disagreements with GnuCOBOL found (none a coblean semantics bug)

All are GnuCOBOL 3.2 deviations from the standard/IBM or unsettled points; each is left out of
generation by name in the tester's docstring, with a probe in tools/difftest/cov/probes/:
- PROHIBITED: GnuCOBOL raises the size error on EVERY ROUNDED MODE PROHIBITED statement, exact results
  included (12/3, 12.00*3) (p1bprohib.cob). GnuCOBOL cannot be the reference for #11; oracle used.
- G-varmax: WRITE with DEPENDING ON value > maximum: GnuCOBOL cuts the record, status 00; standard and
  coblean 44 (p3vary.cob).
- G-rwshort (new): sequential REWRITE of a variable record with an unchanged length below the maximum:
  GnuCOBOL 44 and the record is not replaced; coblean 00 (p3cvary.cob).
- G-vary39 (new): a new variable-length sequential file whose only WRITE was rejected (44): GnuCOBOL
  then refuses OPEN I-O with status 39 (READ 47, REWRITE 49, CLOSE 42); coblean opens it (p3evary.cob).
- G-rw21 (known): indexed REWRITE (dynamic) of a missing key: GnuCOBOL 21, standard/coblean 23.
- Two errors at once (REWRITE with no current record and a length outside the range): GnuCOBOL 43,
  coblean 44: check order not fixed by the standard (unclear standard).
- DISPLAY formats (-std=ibm, pretty-display: no): numeric literals shown without the decimal point;
  signed COMP-3, COMP/BINARY, COMP-5 and embedded-sign DISPLAY items formatted differently (GnuCOBOL:
  separate sign, binary items with all digits of their storage) from coblean's IBM-style zoned digits
  with an overpunched sign (p2disp.cob, p2blit.cob). Literal '+7.250' (GnuCOBOL keeps '+') and negative
  zero (MOVE -0, literal -0.00: GnuCOBOL keeps the sign) are left out.
- M-pos (known coblean defect, documented, f6/expected.json): START, or READ+DELETE, then a WRITE that
  lands at the position: coblean's READ NEXT returns the new record (mpos1 S3/D4, mpos2 A3/A4/B3).

## Theorem paths

- No disagreement above is a semantics bug, so none needs the at-once message.
- DISPLAY forms GnuCOBOL cannot check (display_paths_v1.py on the 2306Z IRs; notes/display_paths_v1.txt):
  CBACT01C has 5 and CBTRN03C 2 DISPLAY operands that are numeric DISPLAY items with an embedded sign.
  coblean shows their stored bytes (the IBM rule as coblean models it: overpunched last digit);
  GnuCOBOL -std=ibm shows digits plus a separate sign, so no GnuCOBOL-differential test (old or new)
  checks these 7 operands, and the IBM rule itself is not verified here. No theorem program DISPLAYs
  COMP-3/COMP/COMP-5 items or numeric literals with decimals; ACCTINT, BINCNT and RECSUM have no DISPLAY.
- Other constructs: the variable-length, PROHIBITED and STRING-static forms are not on theorem paths
  by the earlier IR walk (~/coblean_runs/defect_scan/defect_paths_v1.txt) except CBACT01C's varying
  output file (WRITE only), a form cov_f2vary covers (in-range WRITEs agree).

## Cost and slips

- 100 guarded runs, 0.147 core-h in total, at most 2 one-core jobs (load 120-165).
- Slip: one inspection command (between the measured 08:58:34Z and 09:00:02Z) ran `rm -f vs.dat vi.dat` inside my own run directory
  ~/coblean_cov/runs/full1/f2vary_s1/p1_0009 (two GnuCOBOL test data files) without a separate delete
  record. Nothing else was deleted outside the testers' documented per-run cleanup.
