"""Pre-registration H, part one: the locator's differential check. For each input, the locator's run must reproduce
the pinned run byte for byte once its location tags are removed: same outcome, same message, same stdout.

    python3 -I -B h_locdiff.py PIN_DIR LOC_DIR OUT_TSV

PIN_DIR / LOC_DIR: one h_cirrun1.py result (<input>.json) per input, from vo-cirrun and from h-locate. OUT_TSV: input,
pinned outcome, pinned message, locator outcome, stripped locator message, verdict ("equal" or "LOCATOR FAILURE: ..."),
and the backtrace tags. Exit status 0 when every input of PIN_DIR has an equal locator run.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

TAG = re.compile(r"⟦(?:call \S+ \S+ @\d+:\d+|loop @\d+:\d+)⟧")


def main(argv: list[str]) -> int:
    if len(argv) != 4:
        print(__doc__, file=sys.stderr)
        return 2
    pin_dir, loc_dir, out = Path(argv[1]), Path(argv[2]), Path(argv[3])
    rows = ["input\tpin_outcome\tpin_message\tloc_outcome\tloc_message_stripped\tverdict\ttags"]
    bad = 0
    for p in sorted(pin_dir.glob("*.json")):
        a = json.loads(p.read_text())
        lp = loc_dir / p.name
        if not lp.exists():
            rows.append(f"{p.stem}\t{a['outcome']}\t{a['message']}\t-\t-\tLOCATOR FAILURE: no locator run\t")
            bad += 1
            continue
        b = json.loads(lp.read_text())
        tags = "".join(TAG.findall(b.get("message", "")))
        stripped_msg = TAG.sub("", b.get("message", ""))
        why = []
        if a["outcome"] != b.get("outcome"):
            why.append("outcome")
        if a["message"] != stripped_msg:
            why.append("message")
        if a.get("stdout_sha256") is None or a["stdout_sha256"] != b.get("stdout_untagged_sha256"):
            why.append("stdout")
        verdict = "equal" if not why else "LOCATOR FAILURE: " + ",".join(why) + " differ"
        bad += bool(why)
        rows.append(f"{p.stem}\t{a['outcome']}\t{a['message']}\t{b.get('outcome')}\t{stripped_msg}\t{verdict}\t{tags}")
    out.write_text("\n".join(rows) + "\n")
    print(f"{len(rows) - 1} inputs, {bad} locator failures")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
