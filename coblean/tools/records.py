#!/usr/bin/env python3
"""Record images <-> field values, from a surface-IR program (the layout of `Cobol/Layout.lean`).

    import records
    L = records.Layout(json.load(open("prog.json")))
    L.fields("ACCOUNT-RECORD")                  # [(name, offset_in_record, length, pic, usage)]
    bs = L.encode("ACCOUNT-RECORD", {"ACCT-ID": 1, "ACCT-CURR-BAL": "1500.00", ...})
    L.decode("ACCOUNT-RECORD", bs)              # {"ACCT-ID": 1, "ACCT-CURR-BAL": Decimal("1500.00"), ...}

Numeric values: int or Decimal (or a decimal string). Alphanumeric values: str (encoded in
the program's character set, padded with spaces) or bytes. Fields not given are spaces
(alphanumeric) or zero (numeric). Encodings follow `Cobol/Codec.lean`: zoned decimal with
EBCDIC (C/D/F zones) or ASCII Micro Focus signs, packed decimal (C/D/F sign nibble), big- or
little-endian binary. The usual check is replaying a record through `cobolrun --inputs`.
"""
from decimal import Decimal


def _bin_bytes(d):
    return 2 if d <= 4 else (4 if d <= 9 else 8)


class Layout:
    def __init__(self, prog):
        self.cfg = prog["config"]
        self.items = {}            # name -> list of (offset, item, parent chain)
        self.records = {}
        off = 0
        placed = {}
        for it in prog["data"]:
            sz = self.size(it) * it["occurs"]
            if it["redefines"] is not None and it["redefines"] in placed:
                start = placed[it["redefines"]][0]
            else:
                start = off
                placed[it["id"]] = (start, sz)
                off += sz
            self.records[it["name"]] = (start, it)

    # ---------------------------------------------------------------- sizes
    def size(self, it):
        pic = it["pic"]
        if pic is None:
            off, placed = 0, {}
            for c in it["children"]:
                sz = self.size(c) * c["occurs"]
                if c["redefines"] is not None and c["redefines"] in placed:
                    st, ln = placed[c["redefines"]]
                    off = max(off, st + max(ln, sz))
                    continue
                placed[c["id"]] = (off, sz)
                off += sz
            return off
        if "alnum" in pic:
            return pic["alnum"]["len"]
        if "numEdited" in pic:
            # (ESym.chars, first in a DECIMAL-POINT IS COMMA / CURRENCY SIGN picture: no position)
            return sum(0 if s in ("v", "p") or isinstance(s, dict) else (2 if s in ("cr", "db") else 1)
                       for s in pic["numEdited"]["pic"])
        n = pic["num"]
        u = it["usage"]
        if u == "display":
            return n["digits"] + (1 if n["signed"] and it["signSep"] else 0)
        if u == "packed":
            return n["digits"] // 2 + 1
        return _bin_bytes(n["digits"])

    def fields(self, record):
        """Elementary fields of a record: (name, offset, length, item), first occurrence."""
        _, rec = self.records[record]
        out = []

        def walk(it, off):
            if it["pic"] is not None:
                out.append((it["name"], off, self.size(it), it))
                return
            o, placed = off, {}
            for c in it["children"]:
                sz = self.size(c) * c["occurs"]
                if c["redefines"] is not None and c["redefines"] in placed:
                    walk(c, placed[c["redefines"]])
                    continue
                placed[c["id"]] = o
                walk(c, o)
                o += sz
        walk(rec, 0)
        return out

    # ---------------------------------------------------------------- codecs
    def _char(self, s):
        return list(s.encode("cp037" if self.cfg["charset"] == "ebcdic" else "latin-1"))

    def _digit(self, d):
        return (0xF0 if self.cfg["charset"] == "ebcdic" else 0x30) + d

    def enc_num(self, it, value):
        n = it["pic"]["num"]
        digits, scale, signed = n["digits"], n["scale"], n["signed"]
        v = int((Decimal(str(value)) * (Decimal(10) ** scale)).to_integral_value(rounding="ROUND_DOWN"))
        if not signed and v < 0:
            raise ValueError(f"{it['name']}: negative value for an unsigned field")
        if abs(v) >= 10 ** digits:
            raise ValueError(f"{it['name']}: {value} does not fit {digits} digits")
        u = it["usage"]
        a = abs(v)
        if u == "display":
            ds = [int(c) for c in str(a).rjust(digits, "0")]
            if signed and it["signSep"]:
                sign = self._char("-" if v < 0 else "+")
                body = [self._digit(d) for d in ds]
                return sign + body if it["signLead"] else body + sign
            if signed:
                i = 0 if it["signLead"] else digits - 1
                bs = [self._digit(d) for d in ds]
                if self.cfg["zonedSign"] == "ebcdic":
                    bs[i] = (0xD0 if v < 0 else 0xC0) + ds[i]
                elif self.cfg["zonedSign"] == "asciiMF":
                    bs[i] = (0x70 if v < 0 else 0x30) + ds[i]
                else:
                    bs[i] = ord("}JKLMNOPQR"[ds[i]] if v < 0 else "{ABCDEFGHI"[ds[i]])
                return bs
            return [self._digit(d) for d in ds]
        if u == "packed":
            nib = digits // 2 * 2 + 1
            ds = [int(c) for c in str(a).rjust(nib, "0")]
            ds.append(0xD if v < 0 else (0xC if signed else 0xF))
            return [ds[k] * 16 + ds[k + 1] for k in range(0, len(ds), 2)]
        nb = _bin_bytes(digits)
        le = self.cfg["comp5LE"] if u == "comp5" else self.cfg["binaryLE"]
        return list((v % (1 << (8 * nb))).to_bytes(nb, "little" if le else "big"))

    def dec_num(self, it, bs):
        n = it["pic"]["num"]
        digits, scale, signed = n["digits"], n["scale"], n["signed"]
        u = it["usage"]
        if u == "display":
            neg = False
            ds = []
            body = bs
            if signed and it["signSep"]:
                sign = bs[0] if it["signLead"] else bs[-1]
                neg = sign == self._char("-")[0]
                body = bs[1:] if it["signLead"] else bs[:-1]
            for k, b in enumerate(body):
                ds.append(b & 0x0F)
                last = (k == 0) if it["signLead"] else (k == len(body) - 1)
                if signed and not it["signSep"] and last:
                    if self.cfg["zonedSign"] == "ebcdic":
                        neg = (b >> 4) == 0xD
                    elif self.cfg["zonedSign"] == "asciiMF":
                        neg = (b >> 4) == 0x7
            v = int("".join(map(str, ds)) or "0")
        elif u == "packed":
            nibs = [x for b in bs for x in (b >> 4, b & 0xF)]
            v = int("".join(map(str, nibs[:-1])) or "0")
            neg = nibs[-1] == 0xD
        else:
            le = self.cfg["comp5LE"] if u == "comp5" else self.cfg["binaryLE"]
            v = int.from_bytes(bytes(bs), "little" if le else "big", signed=signed)
            neg = False
        v = -v if neg else v
        return Decimal(v).scaleb(-scale) if scale else v

    def encode(self, record, values):
        start, rec = self.records[record]
        out = [0x40 if self.cfg["charset"] == "ebcdic" else 0x20] * self.size(rec)
        for name, off, ln, it in self.fields(record):
            if name in values:
                val = values[name]
            elif "num" in (it["pic"] or {}):
                val = 0
            else:
                continue
            if "num" in it["pic"]:
                bs = self.enc_num(it, val)
            elif isinstance(val, (bytes, bytearray, list)):
                bs = list(val)
            else:
                bs = self._char(str(val))
            out[off:off + ln] = (bs + out[off + len(bs):off + ln])[:ln] if len(bs) < ln else bs[:ln]
        return out

    def decode(self, record, bs):
        res = {}
        for name, off, ln, it in self.fields(record):
            if name == "FILLER":
                continue
            piece = bs[off:off + ln]
            if "num" in it["pic"]:
                res[name] = self.dec_num(it, piece)
            else:
                res[name] = bytes(piece).decode("cp037" if self.cfg["charset"] == "ebcdic" else "latin-1")
        return res
