"""Build a cobolrun --inputs file from fixed-length record datasets.

usage: python3 -I tools/coverage/carddemo_inputs.py OUT.json FID:LRECL:PATH ...
Each dataset is cut into records of LRECL bytes (EBCDIC images, as shipped in CardDemo's
app/data/EBCDIC); file FID of the program gets them in order.
"""
import json, sys

def main():
    out = sys.argv[1]
    files = []
    for spec in sys.argv[2:]:
        fid, lrecl, path = spec.split(":", 2)
        data = open(path, "rb").read()
        lrecl = int(lrecl)
        if len(data) % lrecl:
            raise SystemExit(f"{path}: {len(data)} bytes is not a multiple of {lrecl}")
        recs = [list(data[i:i + lrecl]) for i in range(0, len(data), lrecl)]
        files.append([int(fid), recs])
    json.dump(files, open(out, "w"))
    for fid, recs in files:
        print(f"file {fid}: {len(recs)} records")

if __name__ == "__main__":
    main()
