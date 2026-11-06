#!/usr/bin/env python3
"""Surface IR of BINCNT.cob, as an extractor would emit it (IBM profile, and the GnuCOBOL
profile used by validate.py: ASCII, little-endian COMP-5).  usage: build_ir.py"""
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools"))
from irjson import *  # noqa: E402,F403

WS_REC, WS_CNT, WS_TOTAL, WS_TOTAL_X, WS_HI, WS_LO, WS_OUT = 1, 2, 3, 4, 5, 6, 7

data = [item(WS_REC, 1, "WS-REC", children=[
    item(WS_CNT, 5, "WS-CNT", pic_9(4, 0, True), usage="comp5"),
    item(WS_TOTAL, 5, "WS-TOTAL", pic_9(9, 0, True), usage="comp5"),
    item(WS_TOTAL_X, 5, "WS-TOTAL-X", redefines=WS_TOTAL, children=[
        item(WS_HI, 10, "WS-HI", pic_x(2)),
        item(WS_LO, 10, "WS-LO", pic_x(2))]),
    item(WS_OUT, 5, "WS-OUT", pic_x(2))])]
paras = [para("0000-MAIN",
              [add([e_lit(1)], [rcv(WS_CNT)])],
              [compute([rcv(WS_TOTAL)], e_add(e_ref(WS_TOTAL), e_mul(e_ref(WS_CNT), e_lit(3))))],
              [move(o_ref(WS_HI), ref(WS_OUT))],
              [GOBACK])]
here = os.path.dirname(os.path.abspath(__file__))
for name, cfg in (("bincnt.ir.json", IBM), ("bincnt.gnucobol.ir.json", GNUCOBOL)):
    out = os.path.join(here, name)
    json.dump(program("BINCNT", data, paras, config=cfg, is_main=False), open(out, "w"), indent=1)
    print(out)
