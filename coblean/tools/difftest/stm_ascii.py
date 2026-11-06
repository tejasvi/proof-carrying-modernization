"""ASCII inputs for CBSTM03A/B, for the comparison with GnuCOBOL (stm_gnucobol.sh, stm_compare.py).

usage: python3 -I tools/difftest/stm_ascii.py IR_ASCII.json INPUTS.json OUTDIR

IR_ASCII.json: the linked IR extracted with `cobolfe.py --profile gnucobol` (ASCII literals and VALUEs).
OUTDIR/ir_ascii.json is that IR with COMP-5 big-endian: the program's only COMP-5 items are its POINTERs,
whose control-block walk GnuCOBOL never runs (stm_gnucobol.sh drops it), and the address space
(creastmt_inputs.py) holds big-endian addresses, like z/OS.
INPUTS.json is creastmt_inputs.py's output (code page 037 records). Writes OUTDIR/inputs_ascii.json and
one file of fixed-length records per input (OUTDIR/f<id>.dat). Records are converted from code page 037
byte by byte, except the sign byte of each signed zoned field (TRNX-AMT, the five amounts of the account
record), which becomes the ASCII overpunch (0x30 + d positive, 0x70 + d negative).
"""
import json, os, sys

SIGNS = {3: [158], 6: [23, 35, 47, 89, 101]}   # linked file id -> offsets of sign bytes

def conv(rec, signs):
    out = bytearray(bytes(rec).decode("cp037").encode("latin-1"))
    for i in signs:
        hi, d = rec[i] >> 4, rec[i] & 15
        assert d <= 9 and hi in (0xC, 0xD, 0xF), (i, hex(rec[i]))
        out[i] = (0x70 if hi == 0xD else 0x30) + d
    return list(out)

def main():
    ir_path, in_path, outdir = sys.argv[1:4]
    ir = json.load(open(ir_path))
    assert ir["config"]["charset"] == "ascii" and ir["config"]["zonedSign"] == "asciiMF", ir["config"]
    ir["config"]["comp5LE"] = False
    json.dump(ir, open(os.path.join(outdir, "ir_ascii.json"), "w"))
    files = json.load(open(in_path))
    out = []
    for fid, recs in files:
        a = [conv(r, SIGNS.get(fid, [])) for r in recs]
        out.append([fid, a])
        with open(os.path.join(outdir, f"f{fid}.dat"), "wb") as f:
            for r in a:
                f.write(bytes(r))
        print(f"file {fid}: {len(a)} records of {sorted(set(map(len, a)))} bytes")
    json.dump(out, open(os.path.join(outdir, "inputs_ascii.json"), "w"))

if __name__ == "__main__":
    main()
