"""Apply one PREREG_M part FE candidate (read-only list cands_cobolfe_v1.tsv) to a copy of the tree.

usage: python3 -I -B apply_cand_fe.py TREE CANDIDATES_TSV ID
Checks that `orig` stands at its line and column (1-based) in TREE/<file> (single-line
candidates only), replaces it with `repl`, and prints the changed line.
"""
import csv
import sys


def main():
    tree, tsv, cid = sys.argv[1:4]
    row = next(r for r in csv.DictReader(open(tsv, newline=""), delimiter="\t") if r["id"] == cid)
    if row["line"] != row["end_line"]:
        sys.exit("multi-line candidate")
    path = f"{tree}/{row['file']}"
    lines = open(path, encoding="utf-8").read().split("\n")
    ln, col = int(row["line"]), int(row["col"])
    orig, repl = row["orig"], row["repl"]
    s = lines[ln - 1]
    if s[col - 1:col - 1 + len(orig)] != orig:
        sys.exit(f"orig {orig!r} not at {ln}:{col}: {s!r}")
    lines[ln - 1] = s[:col - 1] + repl + s[col - 1 + len(orig):]
    open(path, "w", encoding="utf-8").write("\n".join(lines))
    print(f"{cid}: {s.strip()}  ->  {lines[ln - 1].strip()}")


main()
