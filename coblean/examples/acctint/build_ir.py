#!/usr/bin/env python3
"""Surface IR of ACCTINT.cob (+ ACCTREC.cpy), as an extractor would emit it.

usage: build_ir.py [--ascii]   (writes acctint.ir.json, or acctint.gnucobol.ir.json)
"""
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools"))
from irjson import *  # noqa: E402,F403

# data item ids (copybook expanded)
ACCT_REC, ACCT_ID, ACCT_TYPE, ACCT_BALANCE, ACCT_BAL_RAW, ACCT_RATE, ACCT_DAYS = 1, 2, 3, 4, 5, 6, 7
WS_WORK, WS_INTEREST, WS_DAILY_RATE, WS_STATUS = 10, 11, 12, 13
WS_OK, WS_OVERFLOW, WS_SKIPPED = 14, 15, 16


def build(config):
    data = [
        item(ACCT_REC, 1, "ACCT-REC", children=[
            item(ACCT_ID, 5, "ACCT-ID", pic_x(8)),
            item(ACCT_TYPE, 5, "ACCT-TYPE", pic_x(1)),
            item(ACCT_BALANCE, 5, "ACCT-BALANCE", pic_9(13, 2, True), usage="packed"),
            item(ACCT_BAL_RAW, 5, "ACCT-BAL-RAW", pic_x(7), redefines=ACCT_BALANCE),
            item(ACCT_RATE, 5, "ACCT-RATE", pic_9(5, 5, True), usage="packed"),
            item(ACCT_DAYS, 5, "ACCT-DAYS", pic_9(3), usage="binary"),
        ]),
        item(WS_WORK, 1, "WS-WORK", children=[
            item(WS_INTEREST, 5, "WS-INTEREST", pic_9(11, 2, True), usage="packed", value=val_fig("zero")),
            item(WS_DAILY_RATE, 5, "WS-DAILY-RATE", pic_9(9, 8, True), usage="packed", value=val_fig("zero")),
            item(WS_STATUS, 5, "WS-STATUS", pic_x(1), value=val_fig("space"), conds=[
                (WS_OK, "WS-OK", [cond_val({"alnum": {"bs": [0xD2 if config is IBM else ord('K')]}})]),
                (WS_OVERFLOW, "WS-OVERFLOW", [cond_val({"alnum": {"bs": [0xC5 if config is IBM else ord('E')]}})]),
                (WS_SKIPPED, "WS-SKIPPED", [cond_val({"alnum": {"bs": [0xE9 if config is IBM else ord('Z')]}})]),
            ]),
        ]),
    ]
    paras = [
        para("0000-MAIN", [perform("1000-CALC", "1000-EXIT"), GOBACK]),
        para("1000-CALC",
             [ite(c_rel("=", o_ref(ACCT_BAL_RAW), o_fig("LOW-VALUES")),
                  [move(o_fig("ZERO"), ref(ACCT_BALANCE))])],
             [ite(c_or(c_rel("=", o_ref(ACCT_DAYS), o_num(0)),
                       c_and(c_rel("<>", o_ref(ACCT_TYPE), o_str("S")),
                             c_rel("<>", o_ref(ACCT_TYPE), o_str("C")))),
                  [set_true(WS_SKIPPED), go_to("1000-EXIT")])],
             [compute([rcv(WS_DAILY_RATE, "NEAREST-AWAY-FROM-ZERO")], e_div(e_ref(ACCT_RATE), e_lit(365)))],
             [compute([rcv(WS_INTEREST, "NEAREST-AWAY-FROM-ZERO")],
                      e_mul(e_mul(e_ref(ACCT_BALANCE), e_ref(WS_DAILY_RATE)), e_ref(ACCT_DAYS)),
                      on_size=[set_true(WS_OVERFLOW), go_to("1000-EXIT")])],
             [add([e_ref(WS_INTEREST)], [rcv(ACCT_BALANCE)],
                  on_size=[set_true(WS_OVERFLOW)], not_on_size=[set_true(WS_OK)])]),
        para("1000-EXIT", [CONT]),
    ]
    return program("ACCTINT", data, paras, config=config, is_main=False)


if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    ascii_mode = "--ascii" in sys.argv
    out = os.path.join(here, "acctint.gnucobol.ir.json" if ascii_mode else "acctint.ir.json")
    with open(out, "w") as fh:
        json.dump(build(GNUCOBOL if ascii_mode else IBM), fh, indent=1)
    print(out)
