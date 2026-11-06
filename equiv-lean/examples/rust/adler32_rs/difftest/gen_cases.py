"""Test cases for the adler32 differential test (zlib 1.3.1 adler32.c vs examples/rust/adler32_rs).

usage: python3 -I gen_cases.py OUT_FILE SEED N

Writes OUT_FILE (little-endian): b"ADL1", u32 count, then per case a kind byte and its arguments:
  0 adler32_z:         u64 adler, u8 is_null, u64 len, then len bytes unless is_null
  1 adler32:           u64 adler, u8 is_null, u32 len, then len bytes unless is_null
  2 adler32_combine:   u64 adler1, u64 adler2, i64 len2
  3 adler32_combine64: u64 adler1, u64 adler2, i64 len2
Fixed cases: the lengths 0, 1, 2, 15, 16, 17, 5551, 5552, 5553, 11104, 11105 with random, all-0xff
and all-zero buffers and initial values with component sums below and at or above BASE; Z_NULL
buffers with every length but 1 (the C reads buf[0] for len == 1); combine with negative, zero,
small, BASE-adjacent and extreme len2.  Then N random cases (lengths near multiples of NMAX,
short, medium and a few long ones; random initial values; random combine arguments).
"""

import random
import struct
import sys

BASE = 65521
NMAX = 5552
FIXED_LENS = [0, 1, 2, 15, 16, 17, 5551, 5552, 5553, 11104, 11105]


def special_adlers(rng):
    vals = [0, 1, 0xFFFFFFFF, 0xFFF0FFF0, 0xFFF1FFF1, 0xFFF1FFF0, 0xFFF0FFF1, 0xFFFFFFF1,
            0xFFF1FFFF, 0x0001FFFF, 0xFFFF0001, 0xFFFFFFFFFFFFFFFF, 0xDEADBEEF12345678]
    for _ in range(4):
        hi = rng.randrange(BASE, 0x10000)
        lo = rng.randrange(BASE, 0x10000)
        vals.append((rng.getrandbits(32) << 32) | (hi << 16) | lo)
    for _ in range(3):
        vals.append(rng.getrandbits(64))
    return vals


def buffer(rng, n, pattern):
    if pattern == 0:
        return rng.randbytes(n)
    if pattern == 1:
        return b"\xff" * n
    return b"\x00" * n


def rand_len(rng):
    r = rng.random()
    if r < 0.35:
        return rng.randrange(0, 40)
    if r < 0.65:
        k = rng.randrange(1, 6)
        return max(0, k * NMAX + rng.randrange(-24, 25))
    if r < 0.95:
        return rng.randrange(0, 3 * NMAX + 100)
    return rng.randrange(3 * NMAX, 1 << 17)


def rand_adler(rng):
    r = rng.random()
    if r < 0.3:
        hi = rng.randrange(BASE - 8, 0x10000)
        lo = rng.randrange(BASE - 8, 0x10000)
        return (rng.getrandbits(32) << 32) | (hi << 16) | lo
    if r < 0.4:
        return 1
    return rng.getrandbits(64)


def rand_len2(rng):
    r = rng.random()
    if r < 0.15:
        return -rng.randrange(1, 1 << 63)
    if r < 0.3:
        return rng.randrange(0, 3 * BASE)
    if r < 0.4:
        return rng.randrange(0, 1 << 63)
    if r < 0.5:
        return BASE * rng.randrange(1, 1 << 40) + rng.randrange(-2, 3)
    return rng.randrange(0, 1 << 32)


def main():
    out, seed, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    recs = []

    def z(kind, adler, data, is_null=False, length=None):
        ln = len(data) if length is None else length
        if kind == 0:
            head = struct.pack("<BQBQ", 0, adler, 1 if is_null else 0, ln)
        else:
            head = struct.pack("<BQBI", 1, adler, 1 if is_null else 0, ln)
        recs.append(head if is_null else head + data)

    def comb(kind, a1, a2, l2):
        recs.append(struct.pack("<BQQq", kind, a1, a2, l2))

    adlers = special_adlers(rng)
    # len == 1 (one subtraction of BASE from each sum) and len < 16, around BASE
    los = [0, 1, 255, 65250, 65264, 65265, 65506, 65507, 65510, 65519, 65520, 65521, 65522, 65530,
           65535]
    his = [0, 1, 65519, 65520, 65521, 65522, 65530, 65534, 65535]
    for lo in los:
        for hi in his:
            for b0 in [0, 1, 14, 15, 16, 128, 254, 255]:
                a = (hi << 16) | lo
                z(0, a, bytes([b0]))
                z(1, (rng.getrandbits(32) << 32) | a, bytes([b0]))
    for ln in range(16):
        for lo in [0, 65520, 65521, 65535]:
            for hi in [0, 65520, 65521, 65535]:
                for pattern in range(3):
                    z(0, (hi << 16) | lo, buffer(rng, ln, pattern))
    for ln in FIXED_LENS:
        for pattern in range(3):
            for a in adlers:
                data = buffer(rng, ln, pattern)
                z(0, a, data)
                z(1, a, data)
    for ln in [0, 2, 3, 15, 16, 17, 5551, 5552, 5553, 11105, (1 << 28) - 1]:
        for a in adlers[:6]:
            z(0, a, b"", is_null=True, length=ln)
            z(1, a, b"", is_null=True, length=ln)
    for ln in [1 << 32, (1 << 63) + 5, (1 << 64) - 1]:
        z(0, adlers[2], b"", is_null=True, length=ln)
    len2s = [-(1 << 63), -BASE, -2, -1, 0, 1, 2, BASE - 1, BASE, BASE + 1, 2 * BASE, (1 << 31) - 1,
             1 << 31, (1 << 32) + 7, (1 << 63) - 1]
    for a1 in adlers[:10]:
        for a2 in adlers[:10]:
            for l2 in len2s:
                comb(2, a1, a2, l2)
                comb(3, a1, a2, l2)
    for _ in range(n):
        r = rng.random()
        if r < 0.7:
            ln = rand_len(rng)
            data = rng.randbytes(ln) if rng.random() < 0.8 else b"\xff" * ln
            z(0 if rng.random() < 0.6 else 1, rand_adler(rng), data)
        elif r < 0.75:
            ln = rng.randrange(0, 1 << 20)
            if ln == 1:
                ln = 0
            z(0 if rng.random() < 0.5 else 1, rand_adler(rng), b"", is_null=True, length=ln)
        else:
            comb(2 if rng.random() < 0.5 else 3, rand_adler(rng), rand_adler(rng), rand_len2(rng))

    with open(out, "wb") as f:
        f.write(b"ADL1")
        f.write(struct.pack("<I", len(recs)))
        for rec in recs:
            f.write(rec)
    print(f"cases: {len(recs)} (seed {seed}, N {n})")


if __name__ == "__main__":
    main()
