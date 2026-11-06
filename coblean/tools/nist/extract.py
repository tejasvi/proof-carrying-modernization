"""Split the NIST COBOL85 suite (newcob.val) into source files, as its EXEC85 program does.

usage: python3 -I -B tools/nist/extract.py NEWCOB.VAL CONF OUTDIR

NEWCOB.VAL is read as untrusted data. Each `*HEADER,COBOL,NAME` ... `*END-OF,NAME` block becomes
OUTDIR/<module>/NAME.CBL (module = the first two letters of NAME), each `*HEADER,CLBRY,NAME` block
OUTDIR/copy/NAME (copybooks) and each `*HEADER,DATA*,NAME` block OUTDIR/data/NAME. The suite
header line before the first block is skipped.

CONF has GnuCOBOL's EXEC85 configuration format (tests/cobol85/EXEC85.conf.in):
  * `X-nnncc value` cards give the text that replaces the implementor-name placeholder `XXXXXnnn`;
  * after `*BEGIN-UPDATE`, `*START NAME` is followed by numbered source lines for program NAME: a
    line whose sequence number (columns 1-6) is already in the program replaces that line, any
    other is inserted in sequence-number order.
Writes OUTDIR/manifest.json: one entry per program (name, module, lines, placeholders replaced,
update lines applied).
"""
import json
import os
import re
import sys


def read_conf(path):
    xcards, updates, cur, in_upd = {}, {}, None, False
    for line in open(path, encoding="latin-1").read().splitlines():
        if line.startswith("*BEGIN-UPDATE"):
            in_upd = True
            continue
        if line.startswith("*END-UPDATE"):
            in_upd = False
            continue
        if in_upd:
            if line.startswith("*START "):
                cur = line.split()[1]
                updates.setdefault(cur, [])
            elif cur and line.strip():
                updates[cur].append(line)
            elif cur and line[:6].strip():
                updates[cur].append(line)
            continue
        # EXEC85's card layout: "X-", card number (3), program-name position (2), filler (1),
        # substitution text (60). Positions >= 55 mean plain text substitution (all of GnuCOBOL's).
        m = re.match(r"^X-(\d{3})(\d\d) (.*)$", line)
        if m:
            if int(m.group(2)) < 55:
                raise SystemExit(f"program-name position cards are not handled: {line}")
            xcards[int(m.group(1))] = m.group(3)[:60].rstrip()
    return xcards, updates


def substitute(line, xcards):
    """EXEC85 D85-X-CARD-CHECK: when columns 12-15 hold XXXX and 17-19 a card number, columns
    12-71 become the card's text; a full stop in column 20 is kept (added after the text), and with
    a space in column 20 a trailing full stop of the text is removed. Returns (line, substituted)."""
    l = line.ljust(80)
    if l[11:15] != "XXXX" or not l[16:19].isdigit():
        return line, False
    n = int(l[16:19])
    if n not in xcards:
        return line, False
    text = xcards[n].rstrip()
    if l[19] == ".":
        text = text.rstrip(".") + "."
    elif l[19] == " ":
        text = text.rstrip(".")
    return (l[:11] + text.ljust(60)[:60] + l[71:]).rstrip(), True


def apply_updates(lines, upd):
    """Replace or insert numbered lines (columns 1-6) in a fixed-format program."""
    by_seq = {l[:6]: i for i, l in enumerate(lines) if l[:6].strip().isdigit()}
    applied = 0
    for u in upd:
        seq = u[:6]
        if seq in by_seq:
            lines[by_seq[seq]] = u
        else:
            # insert before the first line with a larger sequence number
            k = next((i for i, l in enumerate(lines) if l[:6].strip().isdigit() and l[:6] > seq), len(lines))
            lines.insert(k, u)
            by_seq = {l[:6]: i for i, l in enumerate(lines) if l[:6].strip().isdigit()}
        applied += 1
    return lines, applied


def main():
    val, conf, out = sys.argv[1:4]
    xcards, updates = read_conf(conf)
    text = open(val, encoding="latin-1").read().splitlines()
    manifest, i = [], 0
    while i < len(text):
        m = re.match(r"^\*HEADER,(COBOL|CLBRY|DATA\*),([^\s,]+)(?:,(?:SUBRTN|SUBPRG),([^\s,]+))?", text[i])
        if not m:
            i += 1
            continue
        # `*HEADER,COBOL,MAIN,SUBRTN,SUB`: subprogram SUB, called by MAIN
        kind, parent, name = m.group(1), m.group(2), m.group(3) or m.group(2)
        if parent == name:
            parent = None
        j = i + 1
        while j < len(text) and not re.match(rf"^\*END-OF,{re.escape(name)}\b", text[j]):
            j += 1
        if j == len(text):
            raise SystemExit(f"no *END-OF for {name} (header line {i + 1})")
        body = text[i + 1:j]
        i = j + 1
        if kind == "DATA*":
            d = os.path.join(out, "data")
            os.makedirs(d, exist_ok=True)
            open(os.path.join(d, name), "w", encoding="latin-1").write("\n".join(body) + "\n")
            continue
        pairs = [substitute(l, xcards) for l in body]
        body = [l for l, _ in pairs]
        subs = sum(1 for _, s in pairs if s)
        applied = 0
        if name in updates:
            body, applied = apply_updates(body, updates[name])
        if kind == "CLBRY":
            d = os.path.join(out, "copy")
            os.makedirs(d, exist_ok=True)
            open(os.path.join(d, name), "w", encoding="latin-1").write("\n".join(body) + "\n")
            continue
        mod = name[:2]
        d = os.path.join(out, mod)
        os.makedirs(d, exist_ok=True)
        open(os.path.join(d, name + ".CBL"), "w", encoding="latin-1").write("\n".join(body) + "\n")
        manifest.append({"name": name, "module": mod, "caller": parent, "lines": len(body), "placeholders": subs,
                         "updates": applied})
    json.dump(manifest, open(os.path.join(out, "manifest.json"), "w"), indent=0)
    mods = {}
    for e in manifest:
        mods[e["module"]] = mods.get(e["module"], 0) + 1
    print(f"{len(manifest)} programs: " + ", ".join(f"{k} {v}" for k, v in sorted(mods.items())))


if __name__ == "__main__":
    main()
