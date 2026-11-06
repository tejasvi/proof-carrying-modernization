"""GnuCOBOL against coblean on the reading position of an indexed file in ACCESS DYNAMIC: 20
hand-made scenarios of START, READ NEXT, keyed READ, WRITE and DELETE (file position indicator).

usage: python3 -I -B pos_check.py ROOT OUTDIR
ROOT: the coblean tree whose front end and cobolrun are probed (its tools/difftest supplies the
paths); OUTDIR: a new directory, one subdirectory per scenario (GnuCOBOL's data file lives
there, so nothing is removed). Prints, per scenario, both systems' DISPLAY lines and whether
they agree; writes OUTDIR/results.jsonl ({"case": i, "status": s}, scenario i in order, statuses
as in ext_common.run) and exits 0 when every scenario agrees, 1 otherwise.
"""
import json
import os
import sys

SCEN = {
    "P01": (["K01", "K06", "K08"], [("start", ">=", "K05"), ("write", "K05"), ("rn",), ("rn",)]),
    "P02": (["K01", "K06", "K08"], [("start", ">", "K04"), ("write", "K05"), ("rn",), ("rn",)]),
    "P03": (["K01", "K06", "K08"], [("start", ">=", "K05"), ("write", "K04"), ("rn",)]),
    "P04": (["K02", "K05", "K07"], [("rk", "K02"), ("del", "K02"), ("write", "K02"), ("rn",)]),
    "P05": (["K02", "K05", "K07"], [("rn",), ("del", "K02"), ("write", "K02"), ("rn",)]),
    "P06": (["K02", "K05", "K07"], [("rn",), ("del", "K02"), ("write", "K03"), ("rn",)]),
    "P07": (["K04", "K05", "K08", "K09"], [("write", "K02"), ("rn",)]),
    "P08": ([], [("write", "K03"), ("rn",)]),
    "P09": (["K04", "K06", "K08"], [("rn",), ("write", "K05"), ("rn",)]),
    "P10": (["K01", "K06", "K08"], [("start", "=", "K06"), ("del", "K06"), ("write", "K07"), ("rn",)]),
    "P11": (["K01", "K06", "K08"], [("start", "=", "K06"), ("del", "K06"), ("write", "K06"), ("rn",)]),
    "P12": (["K01", "K06", "K08"], [("rk", "K06"), ("write", "K07"), ("rn",)]),
    "P13": (["K04", "K05", "K08"], [("del", "K04"), ("write", "K03"), ("rn",)]),
    "P14": (["K04", "K05", "K08"], [("write", "K02"), ("del", "K02"), ("rn",)]),
    "P15": (["K01", "K06", "K08"], [("start", ">=", "K05"), ("rn",), ("write", "K05"), ("rn",)]),
    "P16": (["K04", "K06"], [("rn",), ("rn",), ("rn",), ("write", "K09"), ("rn",)]),
    "P17": (["K01", "K06", "K08"], [("start", "=", "K06"), ("write", "K05"), ("rn",)]),
    "P18": (["K01", "K06", "K08"], [("start", ">=", "K05"), ("write", "K07"), ("rn",), ("rn",)]),
    "P19": (["K02", "K05", "K07"], [("rk", "K05"), ("del", "K05"), ("write", "K04"), ("rn",)]),
    "P20": (["K02", "K05", "K07"], [("rk", "K05"), ("del", "K05"), ("write", "K06"), ("rn",)]),
}


def program(name, init, steps):
    L = ["       IDENTIFICATION DIVISION.", f"       PROGRAM-ID. {name}.",
         "       ENVIRONMENT DIVISION.", "       INPUT-OUTPUT SECTION.", "       FILE-CONTROL.",
         f"           SELECT F1 ASSIGN TO 'F{name}'", "               ORGANIZATION IS INDEXED",
         "               ACCESS MODE IS DYNAMIC", "               RECORD KEY IS RKEY",
         "               FILE STATUS IS FS1.", "       DATA DIVISION.", "       FILE SECTION.",
         "       FD F1.", "       01 REC.", "          05 RKEY PIC X(3).", "          05 RDATA PIC X(4).",
         "       WORKING-STORAGE SECTION.", "       01 FS1 PIC XX.", "       PROCEDURE DIVISION.",
         "       P0.", "           OPEN OUTPUT F1"]
    for k in init:
        L += [f"           MOVE '{k}' TO RKEY", "           MOVE 'INIT' TO RDATA", "           WRITE REC"]
    L += ["           CLOSE F1", "           OPEN I-O F1", "           DISPLAY 'O ' FS1 '|'"]
    for s in steps:
        if s[0] == "start":
            L += [f"           MOVE '{s[2]}' TO RKEY", f"           START F1 KEY IS {s[1]} RKEY",
                  "           DISPLAY 'S ' FS1 '|'"]
        elif s[0] == "rn":
            L += ["           MOVE SPACES TO REC", "           READ F1 NEXT RECORD",
                  "           DISPLAY 'N ' FS1 ' ' RKEY '|'"]
        elif s[0] == "rk":
            L += [f"           MOVE '{s[1]}' TO RKEY", "           READ F1",
                  "           DISPLAY 'K ' FS1 ' ' RKEY '|'"]
        elif s[0] == "write":
            L += [f"           MOVE '{s[1]}' TO RKEY", "           MOVE 'NEWW' TO RDATA",
                  "           WRITE REC", "           DISPLAY 'W ' FS1 '|'"]
        elif s[0] == "del":
            L += [f"           MOVE '{s[1]}' TO RKEY", "           DELETE F1 RECORD",
                  "           DISPLAY 'D ' FS1 '|'"]
    L += ["           CLOSE F1", "           STOP RUN."]
    assert all(len(x) <= 72 for x in L)
    return "\n".join(L) + "\n"


def main():
    root, out = sys.argv[1], sys.argv[2]
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import ext_common as E
    D = E.difftest(root)
    os.makedirs(out)
    agree = 0
    res = open(os.path.join(out, "results.jsonl"), "w")
    for case, (name, (init, steps)) in enumerate(SCEN.items()):
        d = os.path.join(out, name)
        os.makedirs(d)
        st, det = E.run(D, program(name, init, steps), os.path.join(d, name), E.PLAIN_COBC, E.PLAIN_FE)
        res.write(json.dumps({"case": case, "status": st}) + "\n")
        if st in ("ok", "mismatch"):
            g, m = det
            agree += st == "ok"
            print(f"{name} {st}: init {init} steps {steps}")
            print(f"   gnucobol: {' '.join(g)}")
            if st != "ok":
                print(f"   model   : {' '.join(m)}")
        else:
            print(f"{name} {st}: {str(det)[:300]}")
    res.close()
    print(f"{agree} of {len(SCEN)} agree")
    return 0 if agree == len(SCEN) else 1


sys.exit(main())
