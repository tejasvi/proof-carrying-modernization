"""Would CardDemo's own sample data have caught the discrepancies? For every version that failed generated cases,
run it on the program's sample-data case (sample.py) and record whether that case alone exposes a difference.

    python3 -m veriforch.modernize.samplecheck [PROG...]     # writes runs/modernize/SAMPLECHECK.json
"""
from __future__ import annotations

import json
import sys

from .loop import RUNS, Run, HarnessError
from .sample import sample_case


def check(progs: list[str]) -> list[dict]:
    out = []
    for prog in progs:
        for arm in ("guided", "naive"):
            for lang in ("java", "rust"):
                d = RUNS / prog / arm / lang
                if not (d / "summary.json").exists():
                    continue
                s = json.loads((d / "summary.json").read_text())
                if s["status"].startswith("not applicable"):
                    continue
                r = Run(prog, arm, lang, budget=0.0, attempts=0, n_cases=0, n_final=0)
                case, notes = sample_case(r.cobol)
                case = r.normalise(case)
                for v in s["versions"]:
                    a = json.loads((d / f"v{v}" / "attempt.json").read_text())
                    failed = ("compile_error" not in a and "n" in a and
                              (a.get("pass") != a.get("n") or (a.get("final") or {}).get("pass") !=
                               (a.get("final") or {}).get("n")))
                    if not failed:
                        continue
                    try:
                        ev = r.evaluate(d / f"v{v}", [case])
                    except HarnessError as e:
                        out.append({"program": prog, "arm": arm, "lang": lang, "version": v, "error": str(e)[:300]})
                        continue
                    caught = bool(ev.get("failing")) if "compile_error" not in ev else None
                    out.append({"program": prog, "arm": arm, "lang": lang, "version": v,
                                "generated_failing": (a.get("n", 0) - a.get("pass", 0)) or
                                                     ((a.get("final") or {}).get("n", 0) - (a.get("final") or {}).get("pass", 0)),
                                "sample_catches": caught,
                                "sample_kinds": ev.get("kinds") if caught else {}, "sample_notes": sorted(set(notes))})
                    print(json.dumps(out[-1]))
    (RUNS / "SAMPLECHECK.json").write_text(json.dumps(out, indent=1))
    return out


if __name__ == "__main__":
    progs = sys.argv[1:] or sorted(p.name for p in RUNS.iterdir() if p.is_dir() and not p.name.startswith("_"))
    check(progs)
