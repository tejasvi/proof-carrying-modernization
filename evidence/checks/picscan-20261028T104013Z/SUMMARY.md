# Exposure scan for front-end defect E: a PICTURE string that begins with a comma (written 2026-10-28T10:40:34Z; by the evidence-owner session, no fork; read-only)
Defect (reported by the COBOL maintainer session at about 10:3xZ, before any fix, for the next revision): the lexer takes a leading ',' of a
picture string as a separator, so PIC ,ZZ9 is read as ZZ9 (size 3, not 4) in all 48 snapshot front ends up to 0551Z
and the pins; B,ZZ9 is read correctly. Session's own scan: ~/coblean_runs/zz9scan (not used here).
Our scan (scan_v2.awk, written independently): fixed format; column 7 '*' or '/' = comment; columns 8-72 upper-cased;
a hit is PIC or PICTURE (optionally IS) followed by blanks and a string starting with ','; a PIC [IS] at the end of a
line is matched against the first token of the next code line.
Planted control plant.cob: 5 PICTURE clauses, 3 leading-comma strings (one continued on the next line), B,ZZ9 and
ZZ9,99 negatives, one commented-out hit: result "T files 1 pics 5 hits 3" (plant_v2.out).
CardDemo: ~/coblean_corpus/carddemo/src/app, all .cbl/.cpy/.dcl (cd_files.txt, 109 files, hashes cd_files.sha256):
9,143 PICTURE clauses, 0 leading-comma strings (cd_v2.out). This covers the sources of the ten theorem programs.
NIST: ~/nist_work/extract3, all .CBL and copy/ (nist_files.txt, 510 files, nist_files.sha256): 58,366 PICTURE
clauses, 0 leading-comma strings (nist_v2.out).
So no CardDemo or NIST source can expose defect E. (scan.awk/cd.out/nist.out: first run, whose file counter skipped
files that open with a comment line; same clause and hit counts.)
