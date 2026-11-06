"""CBSTM03A (+ linked CBSTM03B) inputs, as CREASTMT.jcl builds them.

usage: python3 -I tools/coverage/creastmt_inputs.py CBTRN02C_OUT.json DATA_DIR INPUTS.json ADDRSPACE.json

* TRNXFILE (linked file 3): CBTRN02C's transaction records, sorted by card number and
  transaction id and reformatted as the SORT step does (OUTREC FIELDS=(1:263,16,17:1,262,
  279:279,50)), 328 bytes padded with blanks to the 350-byte record (an assumption about
  DFSORT's padding); the KSDS key is the first 32 bytes.
* XREFFILE, CUSTFILE, ACCTFILE (linked files 4, 5, 6): CardDemo's sample data.
* The address space for SET ADDRESS OF: the PSA at address 0 holds the TCB address at offset
  536 (X'218', where CBSTM03A reads it: PSATNEW in IBM's PSA mapping; the current TCB is
  PSATOLD at X'21C'), the TCB holds the TIOT address at offset 12 (TCBTIO), the TIOT starts
  with the job, step and procedure step names and then has one 20-byte entry per DD statement
  of the job step (length, DD name, UCB address; SYSOUT data sets have no UCB), then zeros.
"""
import json, sys

def ebc(s, n):
    return list(s.ljust(n).encode("cp037"))[:n]

def main():
    run, data, out_in, out_as = sys.argv[1:5]
    r = json.load(open(run))
    tx = [bytes(e["write"]["rec"]) for e in r["out"] if "write" in e and e["write"]["file"] == 2]
    tx.sort(key=lambda x: (x[262:278], x[0:16]))
    trx = [list(x[262:278] + x[0:262] + x[278:328] + bytes([0x40]) * 22) for x in tx]
    def ds(name, n):
        d = open(f"{data}/AWS.M2.CARDDEMO.{name}", "rb").read()
        return [list(d[i:i + n]) for i in range(0, len(d), n)]
    files = [[3, trx], [4, ds("CARDXREF.PS", 50)], [5, ds("CUSTDATA.PS", 500)], [6, ds("ACCTDATA.PS", 300)]]
    json.dump(files, open(out_in, "w"))
    tcb, tiot = 0x1000, 0x2000
    psa = [0] * 540
    psa[536:540] = list(tcb.to_bytes(4, "big"))
    tcbb = [0] * 16
    tcbb[12:16] = list(tiot.to_bytes(4, "big"))
    t = ebc("CREASTMT", 8) + ebc("STEP040", 8) + ebc("", 8)
    dds = [("STEPLIB", True), ("SYSPRINT", False), ("SYSOUT", False), ("TRNXFILE", True),
           ("XREFFILE", True), ("ACCTFILE", True), ("CUSTFILE", True), ("STMTFILE", True),
           ("HTMLFILE", True)]
    for k, (dd, ucb) in enumerate(dds):
        t += [20, 0, 0, 0] + ebc(dd, 8) + [0] * 5 + ([0x00, 0x7a, 0x10 + k] if ucb else [0, 0, 0])
    t += [0] * 24
    json.dump([[0, psa], [tcb, tcbb], [tiot, t]], open(out_as, "w"))
    print(f"{len(trx)} transactions, {len(dds)} DD entries")

if __name__ == "__main__":
    main()
