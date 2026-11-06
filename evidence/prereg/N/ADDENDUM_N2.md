# Addendum N2: the second NIST measurement (PREREG_N_v1; DEVIATIONS 2026-10-25T18:11Z)

Written by the paper's evidence owner at 2026-10-25T18:50:55Z, before any N2 run. Labelled as a later measurement after declared
front-end fixes; reported next to run (b), never replacing it. This file is never edited; changes go to DEVIATIONS.md.

- coblean's draft, adopted as part of this addendum: N/ADDENDUM_N2_inputs_draft.md, sha256
  eb3c7b06b5f124a3f14371f0d7dc33b60c4f12f3e3b7ee9167b6c3f74db4f6a7.
- N2 tree: ~/coblean_snapshots/coblean-nist2-20261025T1848Z = the fixed front end's snapshot coblean-20261025T1839Z
  plus parser.py's D2 change, the NIST pin's CobolRun.lean and the NIST pin's tools/nist. Checked by the evidence owner:
  diff -rq against 1839Z (without .lake, third_party, __pycache__) lists only CobolRun.lean, parser.py and tools/nist;
  the parser.py diff is exactly the D2 change (the `self.unsup("WRITE ... ADVANCING")` line removed, a comment added);
  CobolRun.lean, tools/nist and the cobolrun binary equal the NIST pin's; all 43 Cobol oleans equal the 2306Z pin's.
- Runner run_nist.py 6635004c... and post-step abend_status_v2.py b5934936... unchanged; launcher launch_n2_v2.sh
  (fa69912d...) differs from launch_v1.sh only in taking the tree as an argument, running only N2 and one job at a time
  (diff reviewed). The same six modules, programs, file-directory rule, open-error rule and outcome rule as run (b).
