"""CBTRN03C inputs from a CBTRN02C run, as TRANREPT.jcl builds them.

usage: python3 -I tools/coverage/tranrept_inputs.py CBTRN02C_OUT.json START END DATA_DIR OUT.json
The transaction file is CBTRN02C's writes to its file 2, sorted by card number (columns
263-278) and filtered on TRAN-PROC-DT (columns 305-314) between START and END, as the SORT
step does; then the cross-reference, transaction type and category files from DATA_DIR and the
date parameter record `START END` (80 bytes, EBCDIC).
"""
import json, sys

def main():
    run, start, end, data, out = sys.argv[1:6]
    r = json.load(open(run))
    recs = [e["write"]["rec"] for e in r["out"] if "write" in e and e["write"]["file"] == 2]
    s, e = start.encode("cp037"), end.encode("cp037")
    sel = [x for x in recs if s <= bytes(x[304:314]) <= e]
    sel.sort(key=lambda x: bytes(x[262:278]))
    def ds(name, n):
        d = open(f"{data}/AWS.M2.CARDDEMO.{name}", "rb").read()
        return [list(d[i:i + n]) for i in range(0, len(d), n)]
    parm = (f"{start} {end}".ljust(80)).encode("cp037")
    files = [[1, sel], [2, ds("CARDXREF.PS", 50)], [3, ds("TRANTYPE.PS", 60)],
             [4, ds("TRANCATG.PS", 60)], [6, [list(parm)]]]
    json.dump(files, open(out, "w"))
    print(f"{len(recs)} transactions written by CBTRN02C, {len(sel)} in [{start}, {end}]")

if __name__ == "__main__":
    main()
