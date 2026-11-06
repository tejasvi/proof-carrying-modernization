# Exposure scan for the continued-literal front-end defect (written 2026-10-27T22:05:30Z; by the evidence-owner session, no fork; read-only)
Defect (reported by the COBOL maintainer session at about 22:0xZ, for the next revision): a nonnumeric literal continued over 3+ lines loses the
trailing spaces of its middle lines (snapshots 2306Z, 0518Z, 2008Z).
Scan: all CardDemo .cbl/.cpy files under ~/coblean_corpus/carddemo (files.txt, hashes files.sha256); a continuation line
has '-' in column 7; a literal continued over 3+ lines needs two consecutive continuation lines.
Result: files 106 continuation lines 11 consecutive continuation pairs 0; continuation lines per file in continuation_lines.txt (all in CBSTM03A).
So no CardDemo source, in or out of the theorem set, can expose the defect. The NIST exposure (no graded outcome) is the
producer's statement only (coblean_runs/copyrepl/expo/lit3.tsv, changed.tsv), not checked here.
