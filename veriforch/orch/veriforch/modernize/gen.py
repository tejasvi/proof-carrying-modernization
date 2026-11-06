"""Random test cases for a COBOL batch program, from its mapping (INTERFACES.md, "Test case JSON").

Every field value is valid for its PIC: numeric fields hold integers within their digits (negative only when
signed), alphanumeric fields strings of exactly their length. Values are drawn with an edge bias (zero, the
maximum, spaces, short words, full-width text, Latin-1 characters) and from the program's own literals (literal
mining). Fields of the same kind and size as a file key (`XREF-ACCT-ID`, `TRANCAT-ACCT-ID`, `ACCT-ID`) draw from a
small shared pool per case, and keyed files get records for most pooled keys, so keyed READs both hit and miss.

Indexed files get unique record keys (and unique alternate keys where duplicates are not allowed) in ascending
key order, as coblean's file model assumes (true of every VSAM KSDS).
"""
from __future__ import annotations

import json
import random
from pathlib import Path

from .cobol import encode_record
from .mapping import _layout

UPPER = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
DIGITS = "0123456789"
PRINT = UPPER + UPPER.lower() + DIGITS + " -./,'&*()#@$%+:;=?!_"
LATIN1 = "ÀÁÂÄÇÈÉÊËÍÑÓÖÜßàáâäçèéêëíñóöüÿ¢£¥§°±µ¿"


def literals(ir: dict) -> tuple[list[str], list[int]]:
    strs, nums = set(), set()

    def walk(x):
        if isinstance(x, dict):
            if "str" in x and isinstance(x["str"], dict) and "s" in x["str"]:
                strs.add(x["str"]["s"])
            if "num" in x and isinstance(x["num"], dict) and "v" in x["num"]:
                nums.add(int(x["num"]["v"]))
            for v in x.values():
                walk(v)
        elif isinstance(x, list):
            for v in x:
                walk(v)
    walk(ir["paras"])
    return sorted(s for s in strs if s.strip()), sorted(nums)


def _sig(f: dict) -> tuple:
    """Pool signature: kind and size. Dates and timestamps have their own pool (`Generator.date`)."""
    if f["cobol"].endswith("DATE") or f["cobol"].endswith("-TS"):
        return ("date", f["cobol"])
    return ("num", f["digits"], f["scale"]) if f["kind"] == "num" else ("alnum", f["len"])


class Generator:
    def __init__(self, mapping: dict, ir: dict, seed: int):
        self.m = mapping
        self.ir = ir
        self.L = _layout().Layout(ir)
        self.rng = random.Random(seed)
        self.strs, self.nums = literals(ir)
        # key signatures: INTO-record fields inside a file's record-key or alternate-key span
        self.key_sigs = set()
        for f in mapping["files"]:
            if not f["input"]:
                continue
            spans = ([f["key_span"]] if f.get("key_span") else []) + [s for s in f.get("alt_key_spans", []) if s]
            for fld in mapping["records"][f["record"]]["fields"]:
                for off, ln in spans:
                    if off <= fld["offset"] and fld["offset"] + fld["len"] <= off + ln:
                        self.key_sigs.add(_sig(fld))

    # ------------------------------------------------------------------ values
    def num(self, f: dict) -> int:
        r, mx = self.rng.random(), 10 ** f["digits"] - 1
        lits = [n for n in self.nums if 0 <= abs(n) * 10 ** f["scale"] <= mx]
        if r < 0.10:
            v = 0
        elif r < 0.15:
            v = mx
        elif r < 0.22 and lits:
            v = abs(self.rng.choice(lits)) * 10 ** f["scale"]
        elif r < 0.35:
            v = self.rng.randint(1, min(mx, 99))
        elif r < 0.70:
            v = self.rng.randint(0, min(mx, 10 ** (f["scale"] + 5)))
        else:
            v = self.rng.randint(0, mx)
        if f["signed"] and self.rng.random() < 0.35:
            v = -v
        return v

    def alnum(self, f: dict) -> str:
        n, name, rng = f["len"], f["cobol"], self.rng
        r = rng.random()
        if r < 0.07:
            return " " * n
        lits = [s for s in self.strs if len(s) <= n]
        if r < 0.20 and lits:
            return rng.choice(lits).ljust(n)
        if name.endswith("DATE") and n == 10 and r < 0.85:
            return self.date()
        if name.endswith("-TS") and n == 26 and r < 0.85:
            return (f"{self.date()} {rng.randint(0, 23):02d}:{rng.randint(0, 59):02d}:{rng.randint(0, 59):02d}."
                    f"{rng.randint(0, 999999):06d}")
        if r < 0.55:
            k = rng.randint(1, n)
            return "".join(rng.choice(UPPER + DIGITS + " ") for _ in range(k)).ljust(n)
        if r < 0.75:
            return "".join(rng.choice(DIGITS) for _ in range(rng.randint(1, n))).ljust(n)
        if r < 0.97:
            return "".join(rng.choice(PRINT) for _ in range(n))
        return "".join(rng.choice(PRINT + LATIN1 + "\x00\x9f") for _ in range(n))

    def date(self) -> str:
        """A date, usually from the case's small date pool (so date comparisons between fields go both ways)."""
        rng = self.rng
        if not hasattr(self, "dates") or rng.random() > 0.75:
            return f"{rng.randint(1990, 2035):04d}-{rng.randint(1, 12):02d}-{rng.randint(1, 28):02d}"
        return rng.choice(self.dates)

    def pool(self, f: dict, pools: dict) -> list:
        sig = _sig(f)
        if sig not in pools:
            k = self.rng.choices([1, 2, 3], weights=[4, 4, 2])[0]
            vals = [self.num(f) if f["kind"] == "num" else self.alnum(f) for _ in range(k)]
            lits = [x for x in self.strs if len(x) <= f["len"] and (len(x) >= 3 or f["len"] < 5)
                    ] if f["kind"] == "alnum" else []
            if lits and self.rng.random() < 0.5:
                vals.append(self.rng.choice(lits).ljust(f["len"]))
            pools[sig] = vals
        return pools[sig]

    def value(self, f: dict, pools: dict):
        if _sig(f) in self.key_sigs and f["cobol"].split("#")[0] != "FILLER":
            if self.rng.random() < self.hit:
                return self.rng.choice(self.pool(f, pools))
        return self.num(f) if f["kind"] == "num" else self.alnum(f)

    def field_value(self, f: dict, pools: dict):
        """A value for a field: a list of `occurs` values for an array field."""
        if f.get("occurs"):
            return [self.value(f, pools) for _ in range(f["occurs"])]
        return self.value(f, pools)

    def _key_fields(self, f: dict, span) -> list[dict]:
        off, ln = span
        return [x for x in self.m["records"][f["record"]]["fields"]
                if off <= x["offset"] and x["offset"] + x["len"] <= off + ln]

    def fill_in(self, f: dict, rows: list, pools: dict) -> list:
        """Referential fill-in: records for (most) combinations of pooled key values, so keyed READs hit."""
        import itertools
        rec = self.m["records"][f["record"]]
        spans = ([f["key_span"]] if f.get("key_span") else []) + [x for x in f.get("alt_key_spans", []) if x]
        for span in spans:
            kf = self._key_fields(f, span)
            if not kf or any(_sig(x) not in self.key_sigs for x in kf):
                continue
            combos = list(itertools.product(*[self.pool(x, pools) for x in kf]))[:27]
            have = {tuple(r[x["cobol"]] for x in kf) for r in rows}
            for combo in combos:
                if combo not in have and self.rng.random() < self.hit:
                    r = {x["cobol"]: self.field_value(x, pools) for x in rec["fields"]}
                    r.update({x["cobol"]: v for x, v in zip(kf, combo)})
                    rows.append(r)
                    have.add(combo)
        return rows

    # ------------------------------------------------------------------ cases
    def _count(self) -> int:
        r = self.rng.random()
        return 0 if r < 0.10 else 1 if r < 0.25 else self.rng.randint(2, 5) if r < 0.75 else self.rng.randint(6, 12)

    def clock(self) -> str:
        rng = self.rng
        off = rng.choice(["-0500", "-0400", "+0000", "+0530", "-0700", "+0100"])
        return (f"{rng.randint(2000, 2035):04d}{rng.randint(1, 12):02d}{rng.randint(1, 28):02d}"
                f"{rng.randint(0, 23):02d}{rng.randint(0, 59):02d}{rng.randint(0, 59):02d}{rng.randint(0, 99):02d}"
                + off)

    def case(self) -> dict:
        pools: dict = {}
        # per case: how often key fields take pooled values and pooled keys get records (keyed READs hit), and
        # the date pool
        self.hit = self.rng.choice([0.6, 0.9, 1.0])
        self.dates = [f"{self.rng.randint(1990, 2035):04d}-{self.rng.randint(1, 12):02d}-{self.rng.randint(1, 28):02d}"
                      for _ in range(self.rng.randint(2, 3))]
        files = {}
        for f in self.m["files"]:
            if not f["input"]:
                continue
            rec = self.m["records"][f["record"]]
            rows = [{fld["cobol"]: self.field_value(fld, pools) for fld in rec["fields"]} for _ in range(self._count())]
            if f["org"] == "indexed" and f.get("key_span"):
                if f.get("keyed_reads_by"):
                    rows = self.fill_in(f, rows, pools)
                rows = self._unique_sorted(f, rec, rows)
            files[f["fd"]] = {"record": f["record"], "records": rows}
        out = {"program": self.m["program"], "files": files}
        if self.m.get("linkage"):
            out["linkage"] = {}
            for lk in self.m["linkage"]:
                if "record" in lk:
                    out["linkage"][lk["name"]] = {x["cobol"]: self.field_value(x, pools)
                                                  for x in self.m["records"][lk["record"]]["fields"]}
                else:
                    out["linkage"][lk["name"]] = self.value(lk["field"], pools)
        if self.m["clock"]:
            out["clock"] = self.clock()
        return out

    def _unique_sorted(self, f: dict, rec: dict, rows: list) -> list:
        off, ln = f["key_span"]
        seen, alt_seen, keep = set(), [set() for _ in f.get("alt_key_spans", [])], []
        for r in rows:
            bs = encode_record(self.L, rec, r)
            k = tuple(bs[off:off + ln])
            if k in seen:
                continue
            alts = [tuple(bs[a[0]:a[0] + a[1]]) if a else None for a in f.get("alt_key_spans", [])]
            dups = f.get("alt_key_dups", [False] * len(alts))
            if any(a is not None and not d and a in s for a, d, s in zip(alts, dups, alt_seen)):
                continue
            seen.add(k)
            for a, s in zip(alts, alt_seen):
                s.add(a)
            keep.append((k, r))
        keep.sort(key=lambda kr: kr[0])
        return [r for _k, r in keep]


def generate(mapping: dict, ir: dict, n: int, seed: int) -> list[dict]:
    g = Generator(mapping, ir, seed)
    return [g.case() for _ in range(n)]


if __name__ == "__main__":
    import sys
    m = json.loads(Path(sys.argv[1]).read_text())
    ir = json.loads(Path(sys.argv[2]).read_text())
    for c in generate(m, ir, int(sys.argv[3]), int(sys.argv[4])):
        print(json.dumps(c))
