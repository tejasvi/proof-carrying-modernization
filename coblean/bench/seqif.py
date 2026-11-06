#!/usr/bin/env python3
"""Scaling benchmark: N sequential IF statements (validation-style code).

    IF F-i > 0  ADD 1 TO CNT  ADD F-i TO TOTAL  END-IF      (i = 1..N)
    GOBACK.

usage: seqif.py N   (writes seqif_N.ir.json next to this script)
"""
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tools"))
from irjson import *  # noqa: E402,F403

n = int(sys.argv[1])
REC, CNT, TOTAL = 1, 2, 3
fields = [item(10 + i, 5, f"F-{i + 1}", pic_9(5, 0, True), usage="packed") for i in range(n)]
data = [item(REC, 1, "REC", children=fields + [
    item(CNT, 5, "CNT", pic_9(4), usage="packed", value=val_fig("zero")),
    item(TOTAL, 5, "TOTAL", pic_9(9, 0, True), usage="packed", value=val_fig("zero"))])]
body = [[ite(c_rel(">", o_ref(10 + i), o_num(0)),
             [add([e_lit(1)], [rcv(CNT)]), add([e_ref(10 + i)], [rcv(TOTAL)])])] for i in range(n)]
paras = [para("MAIN", *body, [GOBACK])]
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), f"seqif_{n}.ir.json")
json.dump(program("SEQIF", data, paras), open(out, "w"), indent=1)
print(out)
