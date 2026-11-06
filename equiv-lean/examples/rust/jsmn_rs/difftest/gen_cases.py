# Test inputs for the jsmn differential runs: jsmn's own test/tests.c inputs (each with its token count and with
# other counts) and random JSON (valid documents and mutated ones). Writes cases (u32 num_tokens, u32 len, bytes).
import random
import re
import struct
import sys

def c_literals(src, i):
    """Adjacent C string literals starting at src[i] (after whitespace): (bytes, next index) or None."""
    out = b""
    found = False
    while True:
        m = re.compile(r'\s*"').match(src, i)
        if not m:
            break
        j = m.end()
        buf = bytearray()
        while src[j] != '"':
            ch = src[j]
            if ch == '\\':
                nx = src[j + 1]
                esc = {'n': 10, 't': 9, 'r': 13, '\\': 92, '"': 34, "'": 39, '0': 0, 'b': 8, 'f': 12}
                if nx in esc:
                    buf.append(esc[nx]); j += 2; continue
                if nx == 'x':
                    k = j + 2
                    while src[k] in '0123456789abcdefABCDEF':
                        k += 1
                    buf.append(int(src[j + 2:k], 16) & 255); j = k; continue
                buf.append(ord(nx)); j += 2; continue
            buf += ch.encode('utf-8'); j += 1
        out += bytes(buf); i = j + 1; found = True
    return (out, i) if found else None

def test_inputs(path):
    src = open(path, encoding='utf-8').read()
    cases = []
    for m in re.finditer(r'\bparse\(', src):
        r = c_literals(src, m.end())
        if not r:
            continue
        js, k = r
        rest = src[k:k + 200]
        mm = re.match(r'\s*,\s*([^,]+),\s*([0-9]+)', rest)
        n = int(mm.group(2)) if mm else 8
        cases.append((n, js))
    lits = set()
    for m in re.finditer(r'"', src):
        pass
    for m in re.finditer(r'(?<![\w\'])"', src):
        r = c_literals(src, m.start())
        if r:
            lits.add(r[0])
    return cases, sorted(lits)

ALPHA = b'{}[]":,\\ \t\n\r0123456789abcdefuxyzABCDEFtrunlse-+.E/' + bytes([0, 1, 31, 127, 128, 200, 255])

def rnd_string(rng):
    s = bytearray(b'"')
    for _ in range(rng.randint(0, 8)):
        r = rng.random()
        if r < 0.12:
            s += b'\\' + bytes([rng.choice(b'"/\\bfrnt')])
        elif r < 0.2:
            s += b'\\u' + bytes(rng.choice(b'0123456789abcdefABCDEF') for _ in range(4))
        else:
            s.append(rng.choice(b'abcxyz 019-_.'))
    s += b'"'
    return bytes(s)

def rnd_value(rng, depth):
    r = rng.random()
    if depth > 4 or r < 0.35:
        return rng.choice([b'0', b'-12', b'3.5e7', b'true', b'false', b'null', b'abc', rnd_string(rng),
                           rnd_string(rng)])
    ws = lambda: rng.choice([b'', b'', b' ', b'\n ', b'\t'])
    if r < 0.7:
        items = [rnd_value(rng, depth + 1) for _ in range(rng.randint(0, 4))]
        return b'[' + ws() + (b',' + ws()).join(items) + ws() + b']'
    items = [rnd_string(rng) + ws() + b':' + ws() + rnd_value(rng, depth + 1) for _ in range(rng.randint(0, 4))]
    return b'{' + ws() + (b',' + ws()).join(items) + ws() + b'}'

def mutate(rng, js):
    b = bytearray(js)
    for _ in range(rng.choice([0, 0, 1, 1, 2, 3])):
        op = rng.random()
        p = rng.randint(0, len(b))
        if op < 0.4 or not b:
            b[p:p] = bytes([rng.choice(ALPHA)])
        elif op < 0.7:
            del b[min(p, len(b) - 1)]
        else:
            b[min(p, len(b) - 1)] = rng.choice(ALPHA)
    return bytes(b)

def main():
    tests, out, nrand, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    rng = random.Random(seed)
    cases, lits = test_inputs(tests)
    allc = []
    for n, js in cases:
        for k in sorted({n, 0, 1, 2, 3, 5, 8, 16, 100}):
            allc.append((k, js))
    for js in lits:
        for k in (0, 1, 4, 16, 256):
            allc.append((k, js))
    for _ in range(nrand):
        js = rnd_value(rng, 0)
        if rng.random() < 0.6:
            js = mutate(rng, js)
        if rng.random() < 0.1:
            js = js[:rng.randint(0, len(js))]
        k = rng.choice([0, 1, 2, 3, rng.randint(0, 40), 64, 1000])
        allc.append((k, js))
    with open(out, 'wb') as f:
        for k, js in allc:
            f.write(struct.pack('<II', k, len(js)) + js)
    print(f"{len(cases)} test calls, {len(lits)} test literals, {len(allc)} cases")

main()
