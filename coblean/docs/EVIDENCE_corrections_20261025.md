# Corrections to the evidence package of snapshot 20261024T2306Z (declared later change)

Written 2026-10-25 by coblean (the COBOL maintainer session). The 2306Z snapshot and its `docs/EVIDENCE_carddemo.tsv` (sha256
d8559d86507fd4ee51453183f7aec1ff46805a86719aa69bbfa696c235eec673) stay unchanged: they are the checked artifact.
`docs/EVIDENCE_carddemo_corrected_20261025.tsv` is that file with the claim text (column 3) of two rows replaced.
Every value, command, expected value and timestamp is unchanged, and no other row differs. Both corrections came
from an independent read-only review of what each tester compares.

## Changed rows

1. `V.ft`. START is removed from the list of file operations.
   - Old: "Files (sequential and indexed: OPEN, READ, WRITE, REWRITE, DELETE, START, FILE STATUS): …"
   - New: "Files (sequential and indexed: OPEN, READ, WRITE, REWRITE, DELETE, FILE STATUS): …"
   - Reason: tools/difftest/filetest.py never generates a START statement. The word does not occur in the file,
     and its generated operations are OPEN, CLOSE, READ, WRITE, REWRITE and DELETE.
2. `V.st_negzero`. The explanation of the status is corrected.
   - Old: "… every field decodes to the same value (GnuCOBOL keeps a negative zero that the model normalizes); …"
   - New: "… every field decodes to the same value. In the recorded runs the bytes differ only in a stored sign:
     a negative zero … (V.dt_std cases 93, 120, 148), or a packed value moved from an unsigned packed item into a
     signed one, where GnuCOBOL keeps the sign nibble F and the model writes C (V.dt_std cases 65, 81; V.dt_fe
     cases 12, 13); …"
   - Reason: of the 7 ok-negzero cases of the recorded runs (V.dt_std 5, V.dt_fe 2), only 3 are negative zeros.
     The other 4 follow `MOVE` of an unsigned COMP-3 item into a signed COMP-3 item. Each case differs in exactly
     one field:

     | row | case | field | picture | GnuCOBOL bytes | model bytes | value |
     |---|---|---|---|---|---|---|
     | V.dt_std | 65 | N6 | S9(3)V9(4) COMP-3 | 0710000f | 0710000c | 71.0000 |
     | V.dt_std | 81 | N2 | S9(3)V9(2) COMP-3 | 00040f | 00040c | 0.40 |
     | V.dt_std | 93 | N6 | S9(1) COMP-3 | 0d | 0c | 0 |
     | V.dt_std | 120 | N6 | S9(1) SIGN SEPARATE | 302d | 302b | 0 |
     | V.dt_std | 148 | N4 | S9(9) COMP-3 | 000000000d | 000000000c | 0 |
     | V.dt_fe | 12 | N3 | S9(2)V9(1) COMP-3 | 894f | 894c | 89.4 |
     | V.dt_fe | 13 | N6 | S9(8)V9(1) COMP-3 | 000000000f | 000000000c | 0 |

   - How these were obtained: the testers were re-run with `--keep` at the recorded N and seeds on the live tree,
     whose semantics and difftest.py equal the snapshot's, and the tallies equal the recorded ones. Then
     `~/coblean_runs/col72/negzero_check_v1.py` replays the generator's field layout, runs each kept GnuCOBOL
     executable and cobolrun, and prints every field whose bytes differ.
   - The status itself is unchanged: "decodes to the same value" is what difftest.py tests (line 600). Its scope
     is wider than negative zero, because the decoder reads only whether a packed sign nibble is B or D, and
     whether a separate sign byte is '-'.

## Not changed here, also found by the review (verified)

- V.in and V.us set every counter to zero before each statement, so a TALLYING counter that is stored instead
  of incremented is not told apart. With non-zero initial counters, the live semantics (equal to the snapshot's)
  agrees with GnuCOBOL on 240 of 240 programs (INSPECT and UNSTRING, seeds 1 and 2, 60 programs each). Mutants
  that store instead of add are caught 60/60 by those variants and 0/60 by the zeroing testers.
  (~/coblean_runs/tally_chk)
- V.us at 2306Z never displays the final POINTER, the TALLYING count or the overflow phrase: the generated
  DISPLAY line ran past column 72. This is fixed in the live tree (unstringtest.py dc3a4ef7…).
- V.stm does not compare the 11 DISPLAY lines of CBSTM03A's control-block walk. GnuCOBOL's copy has no walk, and
  no other row checks those lines beyond their number.
- V.hand compares DISPLAY lines only: GnuCOBOL's exit status and the model's end signal (the header row) are not
  part of the summary.
- The VAL rows' `must` pattern `^\{` pins neither the case count nor the tester's exit status. An exact
  comparison with the recorded value is what detects a truncated run.
