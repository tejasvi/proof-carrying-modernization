#!/usr/bin/env python3
"""COBOL front end: COBOL source (+ copybooks) -> surface-IR JSON.

usage: cobolfe.py PROGRAM.cob [-I COPYDIR]... [--profile ibm|gnucobol] [--trunc std|opt|bin]
                  [--div-scale N] [--main|--sub] [--free] [-o OUT.json] [--report]
                  [--switch NAME=ON|OFF]...

The output follows the extraction contract `Cobol/Frontend/Surface.lean`.  Statements the
IR cannot express become `unsupported` statements (execution faults there); constructs outside
the statements that the model does not cover make the whole program unsupported (its first
statement faults).  Both are listed on stderr (and in the report).
"""
import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import copybook  # noqa: E402
import lexer  # noqa: E402
import source  # noqa: E402
from parser import parse_program, switch_number  # noqa: E402
from tokens import ParseError  # noqa: E402


def front_end(path, copydirs=(), fmt="fixed", **opts):
    with open(path, encoding="latin-1") as fh:
        text = fh.read()
    lines = source.strip_comment_entries(source.read_lines(text, path, fmt))
    toks = lexer.tokenize(lines)
    used = []
    toks = copybook.expand(toks, [os.path.dirname(os.path.abspath(path))] + list(copydirs), fmt,
                           used=used)
    prog, p = parse_program(toks, **opts)
    return prog, p, used


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("source")
    ap.add_argument("-I", dest="copydirs", action="append", default=[])
    ap.add_argument("--profile", choices=["ibm", "gnucobol"], default="ibm")
    ap.add_argument("--trunc", choices=["std", "opt", "bin"], default="std")
    ap.add_argument("--div-scale", type=int, default=None)
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--main", dest="is_main", action="store_const", const=True)
    g.add_argument("--sub", dest="is_main", action="store_const", const=False)
    ap.add_argument("--free", action="store_true")
    ap.add_argument("-o", dest="out")
    ap.add_argument("--report", action="store_true", help="print a JSON coverage report on stdout")
    ap.add_argument("--tab-width", type=int, default=8,
                    help="tab stops for source lines with tab characters (default 8)")
    ap.add_argument("--switch", dest="switches", action="append", default=[], metavar="NAME=ON|OFF",
                    help="a switch's state at the start of the run (UPSI-0 to UPSI-7; with --profile "
                         "gnucobol also SWITCH-0 to SWITCH-36). Default: OFF, or with --profile "
                         "gnucobol the environment variable COB_SWITCH_n, as GnuCOBOL reads it")
    ap.add_argument("--when-compiled", default=None, metavar="YYYYMMDDhhmmsshh+hhmm",
                    help="value of FUNCTION WHEN-COMPILED (default: the current UTC time)")
    a = ap.parse_args()
    if a.when_compiled is not None and len(a.when_compiled) != 21:
        print("cobolfe: --when-compiled needs 21 characters YYYYMMDDhhmmsshh+hhmm", file=sys.stderr)
        return 2
    switches = {}
    for s in a.switches:
        name, _, v = s.upper().partition("=")
        n = switch_number(a.profile, name)
        if n is None or v not in ("ON", "OFF"):
            print(f"cobolfe: --switch {s}: needs NAME=ON or NAME=OFF, NAME a switch of the {a.profile} profile",
                  file=sys.stderr)
            return 2
        switches[n] = v == "ON"
    source.TAB_WIDTH = a.tab_width
    try:
        prog, p, used = front_end(a.source, a.copydirs, "free" if a.free else "fixed",
                                  profile=a.profile, trunc=a.trunc, div_scale=a.div_scale,
                                  is_main=a.is_main, when_compiled=a.when_compiled, switches=switches)
    except (ParseError, lexer.LexError, copybook.CopyError, source.SourceError) as e:
        print(f"cobolfe: {e}", file=sys.stderr)
        return 1
    unsupported = [u for q in p.unit.programs for u in q.unsupported]
    for where, what in unsupported:
        print(f"cobolfe: unsupported: {where}: {what}", file=sys.stderr)
    if a.out:
        with open(a.out, "w") as fh:
            json.dump(prog, fh, indent=1)
        side = getattr(p.unit, "sidecar", None)
        if side and side["linked"]:
            # the source's other separately compiled programs, for tools/cobolfe/link.py
            with open(a.out + ".link.json", "w") as fh:
                json.dump(side, fh, indent=1)
    if a.report:
        print(json.dumps({"program": prog["name"], "copybooks": used,
                          "paragraphs": len(prog["paras"]),
                          "unsupported": [{"where": w, "what": m} for w, m in unsupported]}, indent=1))
    elif not a.out:
        json.dump(prog, sys.stdout, indent=1)
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
