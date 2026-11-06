"""Recompute discrepancy kinds of a finished run with the current classifier (compare.py), without model calls.

    python3 -m veriforch.modernize.relabel PROG ARM LANG

Versions that saved their failing cases (`failing.jsonl`, `failing_final.jsonl`) are relabelled from those files.
Older versions are re-executed on their saved fresh cases (`cases/v<k>.jsonl`, `cases/final_v<k>.jsonl`), which
is deterministic, and the failing files are written then. The summary's discrepancy table is rebuilt from the
relabelled data; the previous table is kept as `discrepancies_before_relabel`.
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter

from . import compare
from .loop import Run


def _load(p):
    return [json.loads(x) for x in p.read_text().splitlines() if x.strip()] if p.exists() else None


def split_lang(lang_dir: str) -> tuple[str, int]:
    """'java' -> ('java', 1); 'rust_s3' -> ('rust', 3) (seeded repetitions live in <lang>_s<seed>)."""
    if "_s" in lang_dir:
        lang, seed = lang_dir.split("_s", 1)
        return lang, int(seed)
    return lang_dir, 1


def relabel(prog: str, arm: str, lang_dir: str) -> dict:
    lang, seed = split_lang(lang_dir)
    r = Run(prog, arm, lang, budget=0.0, attempts=0, n_cases=0, n_final=0, seed=seed)
    summary_p = r.dir / "summary.json"
    summary = json.loads(summary_p.read_text())
    all_disc: dict[tuple, dict] = {}
    for k in summary["versions"]:
        vdir = r.dir / f"v{k}"
        att = json.loads((vdir / "attempt.json").read_text()) if (vdir / "attempt.json").exists() else {}
        if "n" not in att:
            continue
        for tag, fname in ((f"v{k}", "failing.jsonl"), (f"final_v{k}", "failing_final.jsonl")):
            if tag.startswith("final") and "final" not in att:
                continue
            rows = _load(vdir / fname)
            done = att.get("final", {}) if tag.startswith("final") else att
            if rows is None and done.get("pass") is not None and done.get("pass") == done.get("n"):
                rows = []
            if rows is None:
                cases = _load(r.dir / "cases" / f"{tag}.jsonl") or []
                ev = r.evaluate(vdir, cases)
                rows = [{"case_index": i, "case": c, "cobol": e, "translation": x, "diffs": d}
                        for i, c, e, x, d in ev.get("failing", [])]
                with open(vdir / fname, "w") as fh:
                    for row in rows:
                        fh.write(json.dumps(row, ensure_ascii=False) + "\n")
            locs = Counter()
            for row in rows:
                ds = []
                for name, er in row["translation"].items():
                    if "outcome" not in er:
                        ds.append(("crash", f"crash:{name}"))
                        continue
                    ds += [(d["kind"], compare.location_class(d["location"]))
                           for d in compare.classify(row["case"], row["cobol"], er["outcome"])]
                for key in set(ds):
                    locs[key] += 1
            for (kind, loc), n in locs.items():
                all_disc.setdefault((kind, loc), {"kind": kind, "location": loc, "first_version": k, "cases": 0})
                all_disc[(kind, loc)]["cases"] += n
    summary.setdefault("discrepancies_before_relabel", summary.get("discrepancies"))
    summary["discrepancies"] = sorted(all_disc.values(), key=lambda d: (d["first_version"], d["kind"]))
    summary["discrepancies_by_kind"] = dict(Counter(d["kind"] for d in all_disc.values()))
    summary["relabelled"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    summary_p.write_text(json.dumps(summary, indent=1, ensure_ascii=False))
    return summary


if __name__ == "__main__":
    s = relabel(*sys.argv[1:4])
    print(json.dumps(s["discrepancies_by_kind"]))
