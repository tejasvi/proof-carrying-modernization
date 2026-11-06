"""Apply one PREREG_M mutation candidate (read-only candidate list) to a copy of the tree.

usage: python3 -I -B apply_cand.py TREE CANDIDATES_TSV ID
Checks that the candidate's `original` text stands at its line and column (1-based, Unicode code
points) in TREE/<file>, replaces it with `replacement`, and prints the changed line. Exits 1 if
the original text is not exactly there.
"""
import csv
import sys


def main():
    tree, tsv, cid = sys.argv[1:4]
    row = next(r for r in csv.DictReader(open(tsv, newline=""), delimiter="\t") if r["id"] == cid)
    path = f"{tree}/{row['file']}"
    lines = open(path, encoding="utf-8").read().split("\n")
    ln, col = int(row["line"]), int(row["col"])
    orig, repl = row["original"], row["replacement"]
    s = lines[ln - 1]
    if s[col - 1:col - 1 + len(orig)] != orig:
        sys.exit(f"original {orig!r} not at {ln}:{col}: {s!r}")
    lines[ln - 1] = s[:col - 1] + repl + s[col - 1 + len(orig):]
    open(path, "w", encoding="utf-8").write("\n".join(lines))
    print(f"{cid}: {s.strip()}  ->  {lines[ln - 1].strip()}")


main()
