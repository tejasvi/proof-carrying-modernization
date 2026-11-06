"""Render docs/EVIDENCE_carddemo.md from docs/EVIDENCE_carddemo.tsv (the TSV is the source).

usage: python3 -I -B tools/evidence/render_md.py TSV MD
"""
import sys

INTRO = """# CardDemo evidence package (rendered from EVIDENCE_carddemo.tsv)

The TSV is the source; this file only renders it. Every claim has a command that re-checks it
and the exact output it printed when it was checked. The commands use:

- `C`: the coblean snapshot root; `CD`: the CardDemo checkout at commit
  59cc6c2fd7ebd7ef7925cad552a01a4b8b6e4d5e; `OUT`: a fresh scratch directory;
  `TC`: `$HOME/.elan/toolchains/leanprover--lean4---v4.35.0`.
- Each command writes only under `$OUT`, uses one core (`LEAN_NUM_THREADS=1`, Lake builds one
  file at a time) and no network. Run them from any directory, e.g.
  `C=... CD=... OUT=$(mktemp -d) TC=... bash -c '<recheck_cmd>'`.
- Wording: "kernel-checked" = a Lean theorem whose axioms are listed; "agrees" = a differential
  test (GnuCOBOL, Java, Rust) with the per-case results named; "tested" = a single run.
- Every command except row TH0 uses the snapshot's built files under `$C/.lake/build` (Lean
  object files, `cobolrun`). Row TH0 rebuilds all of them from source in `$OUT/tree` (about 20
  min). Rows that do not call GnuCOBOL can then also be run with `C=$OUT/tree` (the copy leaves
  out `third_party/`, which holds GnuCOBOL).
"""


def cell(s):
    return s.replace("|", "\\|")


def main():
    tsv, md = sys.argv[1:3]
    lines = open(tsv, encoding="utf-8").read().rstrip("\n").split("\n")
    cols = lines[0].split("\t")
    rows = [dict(zip(cols, l.split("\t"))) for l in lines[1:]]
    out = [INTRO]
    for sec in dict.fromkeys(r["section"] for r in rows):
        out.append(f"\n## {sec}\n")
        for r in rows:
            if r["section"] != sec:
                continue
            out.append(f"### {r['id']}\n")
            out.append(f"- claim: {r['claim']}")
            out.append(f"- value: {r['value']}")
            out.append(f"- source: {r['source']}")
            out.append(f"- re-check: `{r['recheck_cmd']}`" if "`" not in r["recheck_cmd"]
                       else f"- re-check:\n\n  ```\n  {r['recheck_cmd']}\n  ```")
            out.append(f"- expected: `{r['expected']}`" if "`" not in r["expected"]
                       else f"- expected: {r['expected']}")
            out.append(f"- checked: {r['checked_utc']}\n")
    open(md, "w", encoding="utf-8").write("\n".join(out) + "\n")
    print(f"{len(rows)} claims rendered to {md}")


if __name__ == "__main__":
    main()
