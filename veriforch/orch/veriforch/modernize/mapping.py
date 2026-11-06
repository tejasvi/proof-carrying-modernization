"""The mechanical mapping between a COBOL program and its translations (INTERFACES.md, style guides).

`build(ir, source)` reads coblean's surface IR and the program source and returns the mapping as a JSON-able dict:
* `files`: one entry per SELECT, in SELECT order (= the IR's file ids): FD name, ASSIGN name, organisation,
  access, OPEN mode, the record the program reads the file INTO (or the FD record), the record it WRITEs or
  REWRITEs FROM (or the FD record), key fields, and the translation names (Java/Rust parameter and output fields);
* `records`: every 01 record used as a file record or FROM/INTO area, with its elementary fields flattened in
  copybook order (FILLER items numbered `FILLER#k`, REDEFINES subtrees skipped), their offsets, lengths and PICs;
* `clock`: whether the program reads FUNCTION CURRENT-DATE.

Offsets and sizes come from coblean's own layout (`tools/records.py`, the layout of `Cobol/Layout.lean`), so the
mapping agrees with the record images cobolrun reads and writes.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

COBLEAN = Path.home() / "coblean_snapshots" / "coblean-20261024T0857Z"

JAVA_KEYWORDS = set("""abstract assert boolean break byte case catch char class const continue default do double else
enum extends final finally float for goto if implements import instanceof int interface long native new package
private protected public return short static strictfp super switch synchronized this throw throws transient try void
volatile while true false null var record yield""".split())
RUST_KEYWORDS = set("""as break const continue crate else enum extern false fn for if impl in let loop match mod move mut
pub ref return self Self static struct super trait true type unsafe use where while async await dyn abstract become box
do final macro override priv typeof unsized virtual yield try""".split())


def _layout():
    sys.path.insert(0, str(COBLEAN / "tools"))
    import records          # coblean's layout and codecs
    return records


def _words(name: str) -> list[str]:
    return [w for w in name.lower().split("-") if w]


def camel(name: str) -> str:
    w = _words(name)
    out = w[0] + "".join(x[:1].upper() + x[1:] for x in w[1:])
    if out in JAVA_KEYWORDS:
        raise ValueError(f"{name}: camelCase name {out} is a Java keyword")
    return out


def pascal(name: str) -> str:
    return "".join(x[:1].upper() + x[1:] for x in _words(name))


def snake(name: str) -> str:
    out = "_".join(_words(name))
    if out in RUST_KEYWORDS:
        raise ValueError(f"{name}: snake_case name {out} is a Rust keyword")
    return out


def _index(ir: dict) -> dict[int, tuple[dict, str]]:
    """item id -> (item, name of its 01 record)."""
    idx = {}

    def walk(it, top):
        idx[it["id"]] = (it, top)
        for c in it["children"]:
            walk(c, top)
    for it in ir["data"]:
        walk(it, it["name"])
    return idx


def record_fields(L, ir_item: dict) -> list[dict]:
    """Elementary fields of a 01 item, flattened in copybook order: REDEFINES subtrees contribute nothing, FILLERs
    are numbered per record. An elementary item under an OCCURS k (on itself or on its group) is ONE field with
    `occurs: k` and `stride` (bytes between occurrences), its offset that of the first occurrence. Offsets from
    coblean's layout."""
    out: list[dict] = []
    nfill = 0

    def walk(it, off, occ=None):
        nonlocal nfill
        if it["occurs"] != 1:
            if occ is not None:
                raise NotImplementedError(f"nested OCCURS in {it['name']}")
            occ = (it["occurs"], L.size(it))
        if it["pic"] is not None:
            name = it["name"]
            if name == "FILLER":
                nfill += 1
                key, jname, rname = f"FILLER#{nfill}", f"filler{nfill}", f"filler{nfill}"
            else:
                key, jname, rname = name, camel(name), snake(name)
            f = {"cobol": key, "java": jname, "rust": rname, "offset": off, "len": L.size(it), "usage": it["usage"]}
            pic = it["pic"]
            if "alnum" in pic:
                f["kind"] = "alnum"
            elif "num" in pic:
                n = pic["num"]
                if n["digits"] > 18:
                    raise NotImplementedError(f"{name}: more than 18 digits")
                f.update(kind="num", digits=n["digits"], scale=n["scale"], signed=n["signed"],
                         sign_separate=it["signSep"], sign_leading=it["signLead"])
            else:
                raise NotImplementedError(f"{name}: edited PIC in a record")
            if occ is not None:
                f["occurs"], f["stride"] = occ
            out.append(f)
            return
        o, placed = off, {}
        for c in it["children"]:
            sz = L.size(c) * c["occurs"]
            if c["redefines"] is not None and c["redefines"] in placed:
                continue                    # the redefined item's fields stand for the storage
            placed[c["id"]] = o
            walk(c, o, occ)
            o += sz
    walk(ir_item, 0)
    return out


def item_spans(L, rec: dict) -> dict[str, list[int]]:
    """[offset, length] of every named item (group or elementary) of a 01 record, first occurrence."""
    spans: dict[str, list[int]] = {}

    def walk(it, off):
        spans.setdefault(it["name"], [off, L.size(it)])
        o, placed = off, {}
        for c in it["children"]:
            sz = L.size(c) * c["occurs"]
            if c["redefines"] is not None and c["redefines"] in placed:
                walk(c, placed[c["redefines"]])
                continue
            placed[c["id"]] = o
            walk(c, o)
            o += sz
    walk(rec, 0)
    return spans


_SELECT = re.compile(r"\bSELECT\s+([A-Z0-9-]+)\s+ASSIGN\s+TO\s+([A-Z0-9-]+)", re.I)
_FD = re.compile(r"^.{6} \s*FD\s+([A-Z0-9-]+)", re.I | re.M)
_FROM = re.compile(r"\b(RE)?WRITE\s+([A-Z0-9-]+)\s+FROM\s+([A-Z0-9-]+)", re.I)


def _code(source: str) -> str:
    """Fixed-format source without sequence and comment lines (column 7 `*` or `/`)."""
    lines = []
    for ln in source.splitlines():
        if len(ln) > 6 and ln[6] in "*/":
            continue
        lines.append(ln[:72])
    return "\n".join(lines)


def _stmts(x, out):
    if isinstance(x, dict):
        for k, v in x.items():
            if k in ("fopen", "fread", "fwrite", "frewrite", "clock"):
                out.append((k, v))
        for v in x.values():
            _stmts(v, out)
    elif isinstance(x, list):
        for v in x:
            _stmts(v, out)


def _calls(x) -> list[dict]:
    out = []
    if isinstance(x, dict):
        if "call" in x and isinstance(x["call"], dict) and "prog" in x["call"]:
            out.append(x["call"])
        for v in x.values():
            out += _calls(v)
    elif isinstance(x, list):
        for v in x:
            out += _calls(v)
    return out


def _local_calls(x) -> list[dict]:
    """Statically linked CALLs (coblean's link.py: `callLocal` into the callee's paragraphs)."""
    out = []
    if isinstance(x, dict):
        if "callLocal" in x and isinstance(x["callLocal"], dict) and "para" in x["callLocal"]:
            out.append(x["callLocal"])
        for v in x.values():
            out += _local_calls(v)
    elif isinstance(x, list):
        for v in x:
            out += _local_calls(v)
    return out


def build(ir: dict, source: str, overrides: dict | None = None, coblean: Path = COBLEAN) -> dict:
    """`source` is the program's source, followed by the sources of statically linked subprograms (their SELECTs
    come after the main program's, as in the linked IR). `overrides` (per program, harness-side): {"records": {FD:
    01 record}} for files read through a subprogram's LINKAGE area, whose data the main program moves into its own
    record; "exclude_display_patterns": regexes of DISPLAY lines outside the translation (z/OS control-block walks);
    "addrspace": the address-space file cobolrun reads for SET ADDRESS OF."""
    overrides = overrides or {}
    records = _layout()
    L = records.Layout(ir)
    idx = _index(ir)
    code = _code(source)
    selects = _SELECT.findall(code)
    if len(selects) != len(ir["files"]):
        raise ValueError(f"{len(selects)} SELECTs in the source, {len(ir['files'])} files in the IR")
    stmts: list = []
    _stmts(ir["paras"], stmts)
    fd_of_record = {m: n.upper() for n, m in
                    re.findall(r"\bFD\s+([A-Z0-9-]+)\s*\.\s*01\s+([A-Z0-9-]+)", code, re.I)}
    from_by_fdrec: dict[str, set] = {}
    for re_, rec, frm in _FROM.findall(code):
        from_by_fdrec.setdefault((("re" if re_ else "") + "write", rec.upper()), set()).add(frm.upper())
    used: set[str] = set()
    files = []
    for (fd, assign), f in zip(selects, ir["files"]):
        fd, assign = fd.upper(), assign.upper()
        fdrec = idx[f["record"]][0]["name"]
        if fd_of_record.get(fdrec) not in (None, fd):
            raise ValueError(f"file {f['id']}: FD {fd} but record {fdrec} belongs to FD {fd_of_record.get(fdrec)}")
        opens = sorted({v["mode"] for k, v in stmts if k == "fopen" and v["file"] == f["id"]})
        intos = sorted({idx[v["into"]["item"]][1] for k, v in stmts
                        if k == "fread" and v["file"] == f["id"] and v.get("into")})
        if len(intos) > 1 and not overrides.get("records", {}).get(fd):
            raise NotImplementedError(f"{fd} is read INTO several records: {intos}")
        writes = any(k == "fwrite" and v["file"] == f["id"] for k, v in stmts)
        rewrites = any(k == "frewrite" and v["file"] == f["id"] for k, v in stmts)
        reads = any(k == "fread" and v["file"] == f["id"] for k, v in stmts)
        keyed = sorted({v["key"] for k, v in stmts if k == "fread" and v["file"] == f["id"] and v["key"]})

        def from_rec(kind):
            s = from_by_fdrec.get((kind, fdrec), set())
            if len(s) > 1:
                if kind != "write":
                    raise NotImplementedError(f"{fd}: {kind} FROM several records {sorted(s)}")
                # report lines written FROM several layouts: the writes are text, as for a variable-length file
                # (the runners treat any file with "varying" as text writes)
                entry.setdefault("varying", {"min": L.size(idx[f["record"]][0]), "max": L.size(idx[f["record"]][0]),
                                             "depending_on": None, "text_writes": sorted(s)})
                return fdrec
            return next(iter(s)) if s else fdrec
        rec_over = overrides.get("records", {}).get(fd)
        entry = {
            "id": f["id"], "fd": fd, "assign": assign, "org": f["org"], "access": f["access"], "open": opens,
            "input": any(m in ("INPUT", "I-O") for m in opens),
            "fd_record": fdrec,
            "record": rec_over or (intos[0] if intos else fdrec),
            "reads": reads,
            "key": idx[f["key"]][0]["name"] if f["key"] else None,
            "alt_keys": [idx[a][0]["name"] for a, _dups in f["alt"]],
            "alt_key_dups": [bool(d) for _a, d in f["alt"]],
            "keyed_reads_by": [idx[k][0]["name"] for k in keyed],
            "java_param": camel(fd), "rust_param": snake(fd),
        }
        if f.get("minLen") is not None:
            entry["varying"] = {"min": f["minLen"], "max": f["maxLen"],
                                "depending_on": idx[f["dependsOn"]][0]["name"] if f.get("dependsOn") else None}
        if writes:
            entry.update(write_from=from_rec("write"), java_writes=camel(fd) + "Writes",
                         rust_writes=snake(fd) + "_writes")
        if rewrites:
            entry.update(rewrite_from=from_rec("rewrite"), java_rewrites=camel(fd) + "Rewrites",
                         rust_rewrites=snake(fd) + "_rewrites")
        used.update(r for r in (entry["record"] if entry["input"] else None, entry.get("write_from"),
                                entry.get("rewrite_from")) if r)
        files.append(entry)
    by_name = {it["name"]: it for it in ir["data"]}
    # PROCEDURE DIVISION USING: one parameter per linkage 01 item, after the input files and before the clock
    linkage = []
    if "using" in ir:
        # the front end's own list (coblean IRs since 1546Z): in a linked IR only the main program's USING counts
        idx_names = {it_id: idx[it_id][0]["name"] for it_id in idx}
        using = [idx_names.get(u, u) if not isinstance(u, dict) else idx_names.get(u.get("item"), "")
                 for u in ir["using"]]
    else:
        mu = re.search(r"PROCEDURE\s+DIVISION\s+USING\s+([A-Z0-9\s-]+?)\s*\.", code, re.I)
        using = mu.group(1).split() if mu else []
    for name in using:
        name = name.upper()
        if name in ("BY", "REFERENCE", "VALUE", "CONTENT"):
            raise NotImplementedError(f"USING {name}")
        it = by_name[name]
        entry = {"name": name, "java_param": camel(name), "rust_param": snake(name),
                 "offset": L.records[name][0], "size": L.size(it)}
        if it["pic"] is None:
            entry["record"] = name
            used.add(name)
        else:
            entry["field"] = record_fields(L, {"id": -1, "name": name, "pic": None, "occurs": 1,
                                               "redefines": None, "children": [it]})[0]
        linkage.append(entry)
    recs = {}
    for name in sorted(used):
        start, it = L.records[name]
        recs[name] = {"class": pascal(name), "size": L.size(it), "fields": record_fields(L, it)}
    # key items (elementary or group): their [offset, length] in the FD record, for ordering and lookups
    for e in files:
        spans = item_spans(L, L.records[e["fd_record"]][1])
        e["key_span"] = spans[e["key"]] if e["key"] else None
        e["alt_key_spans"] = [spans[a] for a in e["alt_keys"]]
    name = ir["name"]
    return {
        "program": name, "java_class": pascal(name), "rust_crate": name.lower(),
        "charset": ir["config"]["charset"],
        "clock": any(k == "clock" for k, _ in stmts),
        "externals": sorted({c["prog"] for c in _calls(ir["paras"])}),
        "called": sorted({c["para"].split("::")[0] for c in _local_calls(ir["paras"])}),
        **({"exclude_display_patterns": overrides["exclude_display_patterns"]}
           if overrides.get("exclude_display_patterns") else {}),
        **({"addrspace": overrides["addrspace"]} if overrides.get("addrspace") else {}),
        "return_code": any(it["name"] == "RETURN-CODE" for it in ir["data"]),
        "files": files, "linkage": linkage, "records": recs,
        "coblean": Path(coblean).name,
    }


def main(argv: list[str]) -> int:
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("ir")
    ap.add_argument("source")
    ap.add_argument("out")
    ap.add_argument("--extra-source", action="append", default=[], help="a statically linked subprogram's source")
    ap.add_argument("--overrides", help="per-program harness overrides (JSON)")
    ap.add_argument("--coblean", default=str(COBLEAN), help="coblean snapshot directory (its cobolrun runs the IR)")
    a = ap.parse_args(argv[1:])
    src = "\n".join(Path(x).read_text(errors="replace") for x in [a.source] + a.extra_source)
    ov = json.loads(Path(a.overrides).read_text()) if a.overrides else None
    m = build(json.loads(Path(a.ir).read_text()), src, ov, Path(a.coblean))
    Path(a.out).write_text(json.dumps(m, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
