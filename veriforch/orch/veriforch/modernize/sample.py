"""A test case from CardDemo's own sample data (app/data/EBCDIC), per program: realistic inputs next to the
generated ones. Each input file's ASSIGN name selects a dataset; records are cut at the FD record length,
decoded by the record the program reads INTO (sorted by key for indexed files, as in the KSDS), and kept only
if every numeric field holds valid data.
"""
from __future__ import annotations

import json
from pathlib import Path

from .cobol import CobolProgram, decode_record

DATA = Path(__file__).resolve().parents[3] / "targets" / "carddemo_src" / "carddemo" / "app" / "data" / "EBCDIC"
DATASETS = {
    "CARDFILE": "AWS.M2.CARDDEMO.CARDDATA.PS", "XREFFILE": "AWS.M2.CARDDEMO.CARDXREF.PS",
    "CARDXREF": "AWS.M2.CARDDEMO.CARDXREF.PS", "CUSTFILE": "AWS.M2.CARDDEMO.CUSTDATA.PS",
    "ACCTFILE": "AWS.M2.CARDDEMO.ACCTDATA.PS", "DALYTRAN": "AWS.M2.CARDDEMO.DALYTRAN.PS",
    "TCATBALF": "AWS.M2.CARDDEMO.TCATBALF.PS", "DISCGRP": "AWS.M2.CARDDEMO.DISCGRP.PS",
    "TRANTYPE": "AWS.M2.CARDDEMO.TRANTYPE.PS", "TRANCATG": "AWS.M2.CARDDEMO.TRANCATG.PS",
}


def sample_case(cobol: CobolProgram, parm_date: str = "2022-07-18", clock: str = "2022071812000000-0500",
                dateparm: str = "2022-06-01 2022-07-06") -> tuple[dict, list[str]]:
    """The sample-data case and notes on what was left out."""
    m, L, notes = cobol.m, cobol.L, []
    files = {}
    for f in m["files"]:
        if not f["input"]:
            continue
        rec = m["records"][f["record"]]
        n = L.size(L.records[f["fd_record"]][1])
        rows = []
        if f["assign"] == "DATEPARM":
            img = list(dateparm.ljust(n).encode("cp037"))
            rows = [decode_record(rec, img)]
        elif f["assign"] in DATASETS and (DATA / DATASETS[f["assign"]]).exists():
            data = (DATA / DATASETS[f["assign"]]).read_bytes()
            if len(data) % n:
                notes.append(f"{f['fd']}: {len(data)} bytes is not a multiple of {n}; file left empty")
            else:
                imgs = [list(data[i:i + n]) for i in range(0, len(data), n)]
                if f["org"] == "indexed" and f.get("key_span"):
                    o, ln = f["key_span"]
                    imgs.sort(key=lambda b: b[o:o + ln])
                for img in imgs:
                    r = decode_record(rec, (img + [0x40] * rec["size"])[:rec["size"]])
                    if any(isinstance(v, dict) for v in r.values()):
                        notes.append(f"{f['fd']}: record with invalid numeric data dropped")
                        continue
                    rows.append(r)
        else:
            notes.append(f"{f['fd']} ({f['assign']}): no sample dataset; file left empty")
        files[f["fd"]] = {"record": f["record"], "records": rows}
    case = {"program": m["program"], "files": files, "sample": True}
    if m["clock"]:
        case["clock"] = clock
    if m.get("linkage"):
        case["linkage"] = {}
        for lk in m["linkage"]:
            vals = {}
            for fl in m["records"][lk["record"]]["fields"] if "record" in lk else []:
                vals[fl["cobol"]] = (len(parm_date) if fl["kind"] == "num" else parm_date.ljust(fl["len"])[:fl["len"]])
            case["linkage"][lk["name"]] = vals
    return case, notes


if __name__ == "__main__":
    import sys
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    root = Path(__file__).resolve().parents[3]
    for prog in sys.argv[1:]:
        m = json.loads((root / "runs" / "modernize" / prog / "mapping.json").read_text())
        P = CobolProgram(root / "runs" / "modernize" / prog / f"{prog.lower()}.ir.json", m,
                         root / "scratch" / "modernize" / "work")
        case, notes = sample_case(P)
        (root / "runs" / "modernize" / prog / "sample_case.json").write_text(json.dumps(case, ensure_ascii=False))
        o = P.run(case)
        (root / "runs" / "modernize" / prog / "sample_outcome.json").write_text(json.dumps(o, ensure_ascii=False))
        print(prog, {k: len(v["records"]) for k, v in case["files"].items()}, "->", o["end"], len(o["displays"]),
              "displays", {k: len(v) for k, v in o["writes"].items()}, {k: len(v) for k, v in o["rewrites"].items()},
              "rc", o["return_code"], "init_dep", bool(o.get("init_dependent")), sorted(set(notes))[:3])
