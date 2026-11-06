"""Run a COBOL program on a test case with coblean's reference semantics (`cobolrun`) and decode the outcome.

The test case and the outcome are in the canonical JSON of INTERFACES.md. Records are encoded and decoded with
the mapping's field layout (coblean's layout; numeric codecs as in `Cobol/Codec.lean`).

Initial storage. coblean's theorems quantify over the initial storage (`Program.initState m inp`, with VALUE
clauses written over `m`), so the reference run uses INITIALIZE-like storage: numeric items zero, everything else
spaces, then the VALUE clauses. Each case also runs on two random storages with valid numeric items. If any of
them changes the outcome, the case depends on uninitialized storage: its outcome is not a function of the input,
and the case is marked `init_dependent`.
"""
from __future__ import annotations

import json
import random
import re
import subprocess
from decimal import Decimal
from pathlib import Path

from .mapping import COBLEAN, _layout

COBOLRUN = COBLEAN / ".lake" / "build" / "bin" / "cobolrun"
FUEL = 10_000_000


def _num_item(f: dict) -> dict:
    return {"name": f["cobol"], "usage": f["usage"], "signSep": f.get("sign_separate", False),
            "signLead": f.get("sign_leading", False),
            "pic": {"num": {"digits": f["digits"], "scale": f["scale"], "signed": f["signed"]}}}


def _enc_field(L, f: dict, v) -> list[int]:
    if f["kind"] == "alnum":
        bs = list(v.encode("cp037"))
        if len(bs) != f["len"]:
            raise ValueError(f"{f['cobol']}: {len(bs)} characters for PIC X({f['len']})")
        return bs
    return L.enc_num(_num_item(f), Decimal(int(v)).scaleb(-f["scale"]))


def encode_record(L, rec: dict, values: dict) -> list[int]:
    out = [0x40] * rec["size"]
    for f in rec["fields"]:
        v = values[f["cobol"]]
        if f.get("occurs"):
            if not isinstance(v, list) or len(v) != f["occurs"]:
                raise ValueError(f"{f['cobol']}: needs a list of {f['occurs']} values")
            for i, x in enumerate(v):
                o = f["offset"] + i * f["stride"]
                out[o:o + f["len"]] = _enc_field(L, f, x)
        else:
            out[f["offset"]:f["offset"] + f["len"]] = _enc_field(L, f, v)
    return out


def _dec_sign(b: int):
    zone, d = b >> 4, b & 0xF
    if d > 9:
        return None
    if zone in (0xC, 0xF, 0xA, 0xE):
        return False, d
    if zone in (0xD, 0xB):
        return True, d
    return None


def decode_packed(f: dict, bs: list[int]):
    """Mirror of `Config.decPacked` (NUMPROC(NOPFD)); None on invalid data."""
    digits, signed = f["digits"], f["signed"]
    if len(bs) != digits // 2 + 1:
        return None
    nibs = [x for b in bs for x in (b >> 4, b & 0xF)]
    ds, sgn = nibs[:-1], nibs[-1]
    if signed:
        neg = False if sgn in (0xC, 0xF, 0xA, 0xE) else True if sgn in (0xD, 0xB) else None
    else:
        neg = False if (sgn == 0xF or 0xA <= sgn <= 0xE) else None
    if neg is None or any(d > 9 for d in ds):
        return None
    v = int("".join(map(str, ds)) or "0")
    if v >= 10 ** digits:
        return None
    return -v if neg else v


def decode_zoned(f: dict, bs: list[int]):
    """Mirror of `Config.decZoned` (EBCDIC, NUMPROC(NOPFD)); None on invalid data."""
    digits, signed = f["digits"], f["signed"]
    if f["usage"] == "packed":
        return decode_packed(f, bs)
    if f["usage"] != "display":
        raise NotImplementedError(f"{f['cobol']}: {f['usage']} numeric in a record")
    if f.get("sign_separate"):
        raise NotImplementedError(f"{f['cobol']}: SIGN SEPARATE")
    if len(bs) != digits:
        return None
    lead = f.get("sign_leading", False)
    body = bs[1:] if (signed and lead) else bs[:-1]
    s = bs[0] if (signed and lead) else bs[-1]
    if any(not (0xF0 <= b <= 0xF9) for b in body):
        return None
    w = int("".join(str(b - 0xF0) for b in body) or "0")
    if signed:
        r = _dec_sign(s)
        if r is None:
            return None
        neg, d = r
    else:
        if 0xF0 <= s <= 0xF9:
            neg, d = False, s - 0xF0
        elif s >> 4 >= 0xA and s & 0xF <= 9:
            neg, d = False, s & 0xF
        else:
            return None
    v = d * 10 ** (digits - 1) + w if (signed and lead) else w * 10 + d
    return -v if neg else v


def _dec_field(f: dict, piece: list[int]):
    if f["kind"] == "alnum":
        return bytes(piece).decode("cp037")
    v = decode_zoned(f, piece)
    return v if v is not None else {"invalid": bytes(piece).hex()}


def decode_record(rec: dict, bs: list[int]) -> dict:
    bs = (list(bs) + [0x40] * rec["size"])[:rec["size"]]
    out = {}
    for f in rec["fields"]:
        if f.get("occurs"):
            out[f["cobol"]] = [_dec_field(f, bs[f["offset"] + i * f["stride"]:f["offset"] + i * f["stride"] + f["len"]])
                               for i in range(f["occurs"])]
        else:
            out[f["cobol"]] = _dec_field(f, bs[f["offset"]:f["offset"] + f["len"]])
    return out


def decode_varying(rec_name: str, bs: list[int]) -> dict:
    """A record of a variable-length file: the record text, exactly as long as the record written."""
    return {rec_name: bytes(bs).decode("cp037")}


class CobolProgram:
    def __init__(self, ir_path: Path, mapping: dict, work: Path):
        self.ir_path = Path(ir_path)
        self.ir = json.loads(self.ir_path.read_text())
        self.m = mapping
        self.records = _layout()
        self.L = self.records.Layout(self.ir)
        self.work = Path(work)
        self.work.mkdir(parents=True, exist_ok=True)
        self._mem_size = None

    # ------------------------------------------------------------------ storage
    def _items(self):
        """(absolute offset, item) of every elementary item outside REDEFINES subtrees."""
        out = []

        def walk(it, off):
            if it["pic"] is not None:
                out.append((off, it))
                return
            o, placed = off, {}
            for c in it["children"]:
                sz = self.L.size(c) * c["occurs"]
                if c["redefines"] is not None and c["redefines"] in placed:
                    continue
                placed[c["id"]] = o
                for k in range(c["occurs"]):
                    walk(c, o + k * self.L.size(c))
                o += sz
        placed = set()
        for it in self.ir["data"]:
            if it["redefines"] is not None and it["redefines"] in placed:
                continue
            placed.add(it["id"])
            start, _ = self.L.records[it["name"]]
            for k in range(it["occurs"]):
                walk(it, start + k * self.L.size(it))
        return out

    def mem_size(self) -> int:
        if self._mem_size is None:
            r = self._run([], None, None)
            self._mem_size = len(r["mem"])
        return self._mem_size

    def storage(self, seed: int | None) -> list[int]:
        """seed None: INITIALIZE-like storage; otherwise random storage with valid numeric items."""
        n = self.mem_size()
        mem = [0x40] * n
        rng = random.Random(seed)
        for off, it in self._items():
            sz = self.L.size(it)
            pic = it["pic"]
            if "num" in pic:
                d = pic["num"]["digits"]
                if seed is None:
                    v = 0
                else:
                    v = rng.randrange(10 ** d)
                    if pic["num"]["signed"] and rng.random() < 0.5:
                        v = -v
                bs = self.L.enc_num(it, Decimal(v).scaleb(-pic["num"]["scale"]))
            elif seed is None:
                continue
            else:
                bs = list("".join(rng.choice(" ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-.") for _ in range(sz)
                                  ).encode("cp037"))
            if off + sz <= n:
                mem[off:off + sz] = bs
        return mem

    # ------------------------------------------------------------------ running
    def files_json(self, case: dict) -> list:
        """Input files for cobolrun: each record encoded by the record the program reads INTO, then padded with
        spaces or truncated to the FD record's length (the file's record length)."""
        out = []
        for f in self.m["files"]:
            if not f["input"]:
                continue
            spec = case["files"].get(f["fd"], {"records": []})
            rec = self.m["records"][f["record"]]
            n = self.L.size(self.L.records[f["fd_record"]][1])
            out.append([f["id"], [(encode_record(self.L, rec, r) + [0x40] * n)[:n] for r in spec["records"]]])
        return out

    def with_linkage(self, mem: list[int], case: dict) -> list[int]:
        """The case's linkage values (PROCEDURE DIVISION USING items) written over the storage."""
        mem = list(mem)
        for lk in self.m.get("linkage", []):
            vals = case.get("linkage", {}).get(lk["name"])
            if vals is None:
                raise ValueError(f"case lacks linkage item {lk['name']}")
            if "record" in lk:
                bs = encode_record(self.L, self.m["records"][lk["record"]], vals)
            else:
                bs = encode_record(self.L, {"size": lk["size"], "fields": [dict(lk["field"], offset=0)]},
                                   {lk["field"]["cobol"]: vals})
            mem[lk["offset"]:lk["offset"] + lk["size"]] = bs
        return mem

    def _run(self, files: list, clock: str | None, mem: list[int] | None) -> dict:
        tag = f"{random.getrandbits(48):012x}"
        inp = self.work / f"in_{tag}.json"
        inp.write_text(json.dumps(files))
        run = COBLEAN.parent / self.m.get("coblean", COBLEAN.name) / ".lake" / "build" / "bin" / "cobolrun"
        cmd = [str(run), str(self.ir_path), "--fuel", str(FUEL), "--inputs", str(inp)]
        if self.m.get("externals"):
            cmd += ["--externals", "carddemo"]
        if self.m.get("addrspace"):
            cmd += ["--addrspace", str(self.ir_path.parent / self.m["addrspace"])]
        if clock:
            cmd += ["--clock", clock]
        if mem is not None:
            cmd += ["--mem", bytes(mem).hex()]
        try:
            p = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
        finally:
            inp.unlink(missing_ok=True)
        if p.returncode != 0:
            raise RuntimeError(f"cobolrun failed ({p.returncode}): {p.stderr[-2000:]}")
        return json.loads(p.stdout)

    def outcome(self, raw: dict) -> dict:
        sig = raw["signal"]
        if sig.startswith("stop:"):
            end = "normal"
        elif sig.startswith("fault:"):
            end = "abend"
        else:
            raise RuntimeError(f"cobolrun: {sig} (fuel {FUEL})")
        by_id = {f["id"]: f for f in self.m["files"]}
        displays, writes, rewrites, other = [], {}, {}, []
        excl = [re.compile(x) for x in self.m.get("exclude_display_patterns", [])]
        for ev in raw["out"]:
            if "display" in ev:
                line = bytes(ev["display"]).decode("cp037")
                if not any(x.search(line) for x in excl):   # outside the translation (e.g. z/OS control blocks)
                    displays.append(line)
            elif "write" in ev or "rewrite" in ev:
                k = "write" if "write" in ev else "rewrite"
                f = by_id[ev[k]["file"]]
                if f.get("varying"):
                    r = decode_varying(f[k + "_from"], ev[k]["rec"])
                else:
                    r = decode_record(self.m["records"][f[k + "_from"]], ev[k]["rec"])
                (writes if k == "write" else rewrites).setdefault(f["fd"], []).append(r)
            else:
                other.append(ev)
        rc = None
        if self.m.get("return_code"):
            start, it = self.L.records["RETURN-CODE"]
            rc = int(self.L.dec_num(it, raw["mem"][start:start + self.L.size(it)]))
        out = {"end": end, "displays": displays, "writes": writes, "rewrites": rewrites, "return_code": rc}
        if end == "abend":
            out["detail"] = sig
            if "unsupported" in sig:
                out["unsupported"] = True       # a model limit (e.g. COBDATFT's error path), not program behaviour
        if other:
            out["other_events"] = other
        return out

    def run(self, case: dict, init_check: bool = True) -> dict:
        files = self.files_json(case)
        clock = case.get("clock") if self.m["clock"] else None
        ref = self.outcome(self._run(files, clock, self.with_linkage(self.storage(None), case)))
        if init_check:
            for seed in (1, 2):
                alt = self.outcome(self._run(files, clock, self.with_linkage(self.storage(seed), case)))
                if comparable(alt) != comparable(ref):
                    ref["init_dependent"] = True
                    ref.setdefault("init_alternatives", []).append(alt)
        return ref


def write_init_mem(ir_path: Path, mapping: dict, out: Path, work: Path) -> int:
    """The reference initial storage (the convention in the module doc; linkage area as the convention leaves
    it) as hex, byte-exact with what `run` passes to cobolrun before the linkage overlay."""
    P = CobolProgram(ir_path, mapping, work)
    mem = P.storage(None)
    Path(out).write_text(bytes(mem).hex() + "\n")
    return len(mem)


def comparable(o: dict) -> dict:
    """The parts of an outcome that translations must reproduce."""
    return {k: o.get(k) for k in ("end", "displays", "writes", "rewrites", "files", "return_code")}
