#!/usr/bin/env python3
"""Surface IR of RECSUM.cob (OPEN/CLOSE are no-ops in the IR: files are record lists).

usage: build_ir.py   (writes recsum.ir.json, IBM profile, and recsum.gnucobol.ir.json, ASCII)
"""
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools"))
from irjson import *  # noqa: E402,F403

IN_FILE, OUT_FILE = 1, 2
IN_REC, IN_ID, IN_AMT, OUT_REC, OUT_ID, OUT_TOTAL = 1, 2, 3, 4, 5, 6
WS, WS_EOF, EOF_88, WS_TOTAL, WS_COUNT = 10, 11, 12, 13, 14

def build(config, eof_n, eof_y):
  return [
    item(IN_REC, 1, "IN-REC", children=[
        item(IN_ID, 5, "IN-ID", pic_x(4)),
        item(IN_AMT, 5, "IN-AMT", pic_9(7, 2, True), usage="packed")]),
    item(OUT_REC, 1, "OUT-REC", children=[
        item(OUT_ID, 5, "OUT-ID", pic_x(4)),
        item(OUT_TOTAL, 5, "OUT-TOTAL", pic_9(11, 2, True), usage="packed")]),
    item(WS, 1, "WS", children=[
        item(WS_EOF, 5, "WS-EOF", pic_x(1), value=val_bytes([eof_n]),
             conds=[(EOF_88, "EOF", [cond_val({"alnum": {"bs": [eof_y]}})])]),
        item(WS_TOTAL, 5, "WS-TOTAL", pic_9(11, 2, True), usage="packed", value=val_fig("zero")),
        item(WS_COUNT, 5, "WS-COUNT", pic_9(5), usage="packed", value=val_fig("zero"))]),
]
paras = [
    para("0000-MAIN", [perform("1000-READ"), perform("2000-PROCESS", loop=loop_until(c_88(EOF_88))),
                       GOBACK]),
    para("1000-READ", [read(IN_FILE, ref(IN_REC), at_end=[set_true(EOF_88)])]),
    para("2000-PROCESS",
         [add([e_ref(IN_AMT)], [rcv(WS_TOTAL)])],
         [add([e_lit(1)], [rcv(WS_COUNT)])],
         [move(o_ref(IN_ID), ref(OUT_ID))],
         [move(o_ref(WS_TOTAL), ref(OUT_TOTAL))],
         [write(OUT_FILE, ref(OUT_REC))],
         [perform("1000-READ")]),
]
here = os.path.dirname(os.path.abspath(__file__))
for name, cfg, n, y in (("recsum.ir.json", IBM, 0xD5, 0xE8),
                        ("recsum.gnucobol.ir.json", GNUCOBOL, ord("N"), ord("Y"))):
    out = os.path.join(here, name)
    json.dump(program("RECSUM", build(cfg, n, y), paras, config=cfg), open(out, "w"), indent=1)
    print(out)
