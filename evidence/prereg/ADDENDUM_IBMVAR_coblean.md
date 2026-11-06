# Addendum: labelled tester run of the COBOL semantics in its IBM variant (coblean snapshot 20261024T2306Z), plan fixed before the run

Recorded by the evidence owner at 2026-10-27T17:28:15Z from coblean's message; no run of this set had started (coblean: runs start
within about an hour, when a job slot frees). Not a pre-registration: a labelled validation measurement, reported apart
from Table tab:fidelity. Purpose: the migration theorems load the IBM variant of the representation, which no
differential test exercised (an agent, item M1).

- Semantics: coblean snapshot 20261024T2306Z (the theorem pin), in a fresh copy; front end on --profile ibm. Per coblean,
  the two profiles differ in exactly three settings (tools/cobolfe/parser.py): character set EBCDIC vs ASCII, zoned sign
  EBCDIC vs ASCII-MF, COMP-5 big-endian vs native; all other settings are shared.
- Reference: the bundled GnuCOBOL 3.2 with -std=ibm -fsign=EBCDIC -fdefault-colseq=EBCDIC; coblean's output compared
  after one fixed EBCDIC-to-ASCII table matched to coblean's code page and to GnuCOBOL's -febcdic-table.
- Testers: the existing generators of the 2306Z testers, at both seeds used for Table tab:fidelity.
- Exclusions, counted and listed, never dropped silently: constructs that are not transparent to the character set
  (raw byte views of packed, binary or COMP-5 fields; hex literals; ORD and CHAR).
- Probe: whether GnuCOBOL with -fsign=EBCDIC prints the overpunched sign on DISPLAY of signed zoned items; if it does,
  the seven DISPSIGN(COMPAT) operands of the theorem programs are tested.
- Control: a planted fault (a corrupted EBCDIC sign table) must fail.
- Deliverables: per tester and seed, agree / mismatch / excluded counts; the exclusion list; mismatch classes; per-program
  coverage for the ten CardDemo programs; sealed directory with hashes.
- Cost per coblean: 3-4 h wall, 1-2 core-h, model tokens about $50-100.
