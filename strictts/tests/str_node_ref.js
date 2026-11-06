// Reference outputs from Node/V8 for tests/StrDiff.lean.
//   usage: node tests/str_node_ref.js OUTDIR [SEED]
// Writes OUTDIR/{fmt,parse,bigint,str}.txt; one case per line, fields separated by one space,
// the last field is V8's result. Encodings:
//   double  16 hex digits of the IEEE-754 bit pattern
//   string  "~" for "", else the UTF-16 code units in hex joined by "."
//   list    "L" followed by the items joined by ","   (so "L" is [] and "L~" is [""])
//   "!"     undefined / NaN result / RangeError / SyntaxError, "u" an omitted argument
'use strict';
const fs = require('fs');
const path = require('path');

const outDir = process.argv[2];
if (!outDir) { console.error('usage: node tests/str_node_ref.js OUTDIR [SEED]'); process.exit(2); }
let seed = (Number(process.argv[3] || 20261023) >>> 0) || 1;

// ---------- deterministic PRNG (mulberry32) ----------
function u32() {
  seed = (seed + 0x6D2B79F5) >>> 0;
  let t = seed;
  t = Math.imul(t ^ (t >>> 15), t | 1);
  t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
  return (t ^ (t >>> 14)) >>> 0;
}
const rint = (n) => n <= 0 ? 0 : Math.floor((u32() / 4294967296) * n);   // 0 .. n-1
const rrange = (a, b) => a + rint(b - a + 1);                                // a .. b
const pick = (arr) => arr[rint(arr.length)];
const coin = (p = 0.5) => u32() / 4294967296 < p;
const rbig = (bits) => { let r = 0n; for (let i = 0; i < bits; i += 32) r = (r << 32n) | BigInt(u32()); return r & ((1n << BigInt(bits)) - 1n); };

// ---------- encodings ----------
const dv = new DataView(new ArrayBuffer(8));
function bitsOf(x) { dv.setFloat64(0, x); return dv.getBigUint64(0); }
function ofBits(b) { dv.setBigUint64(0, BigInt.asUintN(64, b)); return dv.getFloat64(0); }
const hex16 = (b) => b.toString(16).padStart(16, '0');
const encD = (x) => hex16(bitsOf(x));
function encS(s) {
  if (s.length === 0) return '~';
  const a = [];
  for (let i = 0; i < s.length; i++) a.push(s.charCodeAt(i).toString(16));
  return a.join('.');
}
const encL = (xs) => 'L' + xs.map(encS).join(',');
const encOpt = (s) => (s === undefined ? '!' : encS(s));

function tryStr(f) { try { return f(); } catch (e) { return '!'; } }

// ---------- double generators ----------
const nextUp = (x) => { const b = bitsOf(x); if (x === 0) return 5e-324; return x > 0 ? ofBits(b + 1n) : ofBits(b - 1n); };
const nextDown = (x) => -nextUp(-x);
function stepUlps(x, k) { let y = x; if (k > 0) for (let i = 0; i < k; i++) y = nextUp(y); else for (let i = 0; i < -k; i++) y = nextDown(y); return y; }
const randBitsDouble = () => ofBits((BigInt(u32()) << 32n) | BigInt(u32()));
function randFiniteDouble() { for (;;) { const x = randBitsDouble(); if (Number.isFinite(x)) return x; } }
function randDigits(n, lead = true) { let s = lead ? String(rrange(1, 9)) : String(rint(10)); for (let i = 1; i < n; i++) s += String(rint(10)); return s; }
function randShortDecimal() { return Number(randDigits(rrange(1, 17)) + 'e' + rrange(-330, 310)); }
function randSubnormal() { return ofBits(coin(0.3) ? BigInt(rrange(1, 2000)) : rbig(52)) * (coin() ? 1 : -1); }
function randDyadic() { return (coin() ? -1 : 1) * rrange(1, 1 << 20) / 2 ** rrange(0, 30); }
function signed(x) { return coin(0.15) ? -x : x; }
function sampleDouble() {
  switch (rint(10)) {
    case 0: case 1: return randFiniteDouble();
    case 2: return signed(randShortDecimal());
    case 3: return randSubnormal();
    case 4: return randDyadic();
    case 5: return signed(rint(2 ** 30) * 2 ** rrange(-20, 60));
    case 6: return signed(Number(randDigits(rrange(1, 6)) + 'e' + rrange(-25, 25)));
    case 7: return signed(stepUlps(10 ** rrange(-30, 30), rrange(-3, 3)));
    case 8: return signed(Math.fround(rint(1 << 24) / 2 ** rrange(0, 40)));
    default: return signed(Number(rrange(0, 99999) + '.' + randDigits(rrange(1, 4), false)));
  }
}

const SPECIAL = [0, -0, NaN, Infinity, -Infinity, 0.1 + 0.2, 0.1, 0.2, 0.3, 5e-324, -5e-324, 1e-323,
  1.7976931348623157e308, -1.7976931348623157e308, 2.2250738585072014e-308, 2.225073858507201e-308,
  1e21, 999999999999999900000, 1e21 - 65536, 123e-20, 1e-6, 1e-7, 1.5e-7, 0.000001234, 2 ** 53, 2 ** 53 - 1,
  2 ** 53 + 2, -(2 ** 53), 2 ** 63, 2 ** 64, 2 ** 1023, 2 ** -1022, 2 ** -1074, 1.005, 2.5, 0.5, 1.5, -2.5, 1.45,
  9.95, 0.125, 1e100, 1e-100, 123.456, 4.35, 0.07, 1e15, 1e16, 1e17, 9007199254740993, 4.940656458412465e-324,
  2 ** 50 + 0.25, 2 ** 50 + 0.75, 1 / 3, 2 / 3, Math.PI, Math.E, 100, 1e20, 1e22, 1e23, 5e-7];

// ---------- writers ----------
fs.mkdirSync(outDir, { recursive: true });
function writer(name) {
  const lines = [];
  return { push: (...f) => lines.push(f.join(' ')), close: () => { fs.writeFileSync(path.join(outDir, name), lines.join('\n') + '\n'); return lines.length; } };
}

// ================= number formatting =================
const F = writer('fmt.txt');
function addTS(x) { F.push('ts', encD(x), String(x)); }
for (const x of SPECIAL) addTS(x);
for (let i = 0; i < 70000; i++) addTS(randBitsDouble());
for (let i = 0; i < 40000; i++) addTS(signed(randShortDecimal()));
for (let i = 0; i < 4000; i++) addTS(2 ** 53 + rrange(-2000, 2000) * (coin() ? 1 : 2));
for (let i = 0; i < 16000; i++) addTS(signed(rint(2 ** 26) * 2 ** 27 + rint(2 ** 27)));
for (let i = 0; i < 4000; i++) addTS(stepUlps(1e21, rrange(-500, 500)));
for (let i = 0; i < 6000; i++) addTS(signed(Number(randDigits(rrange(1, 22)) + 'e' + rrange(0, 6))));
for (let p = -325; p <= 308; p++) { const x = Number('1e' + p); for (let k = -10; k <= 10; k++) addTS(stepUlps(x, k)); }
for (let i = 0; i < 20000; i++) addTS(randSubnormal());
for (let k = -1074; k <= 1023; k++) { const x = 2 ** k; addTS(x); addTS(nextUp(x)); if (k > -1074) addTS(nextDown(x)); }
for (let i = 0; i < 20000; i++) addTS(randDyadic());
for (let i = 0; i < 10000; i++) addTS(signed(Math.fround(randFiniteDouble())));
for (let i = 0; i < 6000; i++) addTS(signed(Number(rrange(0, 999999) + '.' + randDigits(rrange(1, 6), false))));

// toString(radix): integral values (and NaN/Infinity/RangeError cases)
function addTR(x, r) { F.push('tr', encD(x), String(r), tryStr(() => x.toString(r))); }
for (let i = 0; i < 12000; i++) {
  const r = coin(0.03) ? pick([0, 1, 37, 100]) : rrange(2, 36);
  let x;
  switch (rint(6)) {
    case 0: x = rint(1000); break;
    case 1: x = rint(2 ** 31) * 2 ** 22 + rint(2 ** 22); break;
    case 2: x = 2 ** 53 + rrange(-1000, 1000) * 2; break;
    case 3: x = Math.floor(randShortDecimal()); if (!Number.isFinite(x) || x === 0) x = 12345; break;
    case 4: x = rint(2 ** 30) * 2 ** rrange(0, 300); break;
    default: x = pick([NaN, Infinity, -Infinity, 0, -0, 2 ** 1023, 1.7976931348623157e308, 2 ** 64]);
  }
  addTR(signed(x), r);
}

// toFixed / toPrecision / toExponential. Tie cases: doubles whose exact decimal expansion ends in
// a 5 at the rounding position (exact value computed with BigInt), and typed decimals ending in 5
// (1.005 style, usually just below or above the tie).
function decimalShape(d) {   // [fraction digits, significant digits] of a decimal string
  const [ip, fp = ''] = d.split('.');
  return [fp.length, (ip + fp).replace(/^0+/, '').length];
}
function tieCase() {
  let x;
  switch (rint(5)) {
    case 0: x = (2 * rint(2 ** 20) + 1) / 2 ** rrange(1, 12); break;
    case 1: x = rint(10000) + 0.5; break;
    case 2: x = (2 * rint(2 ** 30) + 1) * 2 ** rrange(-60, -1); break;
    case 3: { const d = randDigits(rrange(1, 4)) + '.' + randDigits(rrange(0, 6), false) + '5'; return [Number(d), d]; }
    default: x = (2 * rint(2 ** 25) + 1) * 5 * 10 ** rrange(0, 6);
  }
  const [m, e] = decomp(x);
  return [x, decimalOfDyadic(m, e)];
}
function fmtValue() {
  switch (rint(8)) {
    case 0: return randFiniteDouble();
    case 1: return signed(stepUlps(1e21, rrange(-3, 3)));
    case 2: return pick(SPECIAL);
    case 3: return signed(Number(randDigits(rrange(1, 25)) + 'e' + rrange(-30, 25)));
    default: return signed(sampleDouble());
  }
}
const clampDigits = (n, lo) => Math.max(lo, Math.min(100, n));
const pickDigits = (lo) => coin(0.03) ? pick([101, 102, 1000, lo === 1 ? 0 : 101]) : coin(0.8) ? rrange(lo, 21) : rrange(lo, 100);
for (let i = 0; i < 36000; i++) {
  let x, f;
  if (coin(0.35)) { const [v, d] = tieCase(); x = signed(v); f = coin(0.2) ? rrange(0, 20) : clampDigits(decimalShape(d)[0] - 1, 0); }
  else { x = fmtValue(); f = pickDigits(0); }
  F.push('tf', encD(x), String(f), tryStr(() => x.toFixed(f)));
}
for (let i = 0; i < 36000; i++) {
  let x, p;
  if (coin(0.35)) { const [v, d] = tieCase(); x = signed(v); p = coin(0.2) ? rrange(1, 21) : clampDigits(decimalShape(d)[1] - 1, 1); }
  else { x = fmtValue(); p = pickDigits(1); }
  F.push('tp', encD(x), String(p), tryStr(() => x.toPrecision(p)));
}
for (let i = 0; i < 36000; i++) {
  let x, f;
  if (coin(0.35)) { const [v, d] = tieCase(); x = signed(v); f = coin(0.2) ? rrange(0, 20) : clampDigits(decimalShape(d)[1] - 2, 0); }
  else { x = fmtValue(); f = coin(0.25) ? 'u' : pickDigits(0); }
  F.push('te', encD(x), String(f), tryStr(() => (f === 'u' ? x.toExponential() : x.toExponential(f))));
}
const nF = F.close();

// ================= parsing =================
const P = writer('parse.txt');
const WS = ['\t', '\n', '\v', '\f', '\r', ' ', '\u00a0', '\u1680', '\u2000', '\u2005', '\u200a', '\u2028', '\u2029', '\u202f', '\u205f', '\u3000', '\ufeff'];
const NOT_WS = ['\u180e', '\u200b', '\u0085', '\u0000', '\u00ad', '\u2060'];
function wsPad(s) {
  const n1 = coin(0.6) ? 0 : rrange(1, 3), n2 = coin(0.6) ? 0 : rrange(1, 3);
  let a = '', b = '';
  for (let i = 0; i < n1; i++) a += coin(0.95) ? pick(WS) : pick(NOT_WS);
  for (let i = 0; i < n2; i++) b += coin(0.95) ? pick(WS) : pick(NOT_WS);
  return a + s + b;
}
function decimalOfDyadic(m, e) {   // exact decimal string of m * 2^e (m BigInt >= 0)
  if (e >= 0) return (m << BigInt(e)).toString();
  const k = -e;
  let s = (m * 5n ** BigInt(k)).toString();
  if (s.length <= k) s = '0'.repeat(k - s.length + 1) + s;
  const ip = s.slice(0, s.length - k), fp = s.slice(s.length - k).replace(/0+$/, '');
  return fp ? ip + '.' + fp : ip;
}
function decomp(x) {   // x > 0 finite -> [m BigInt, e]
  const b = bitsOf(x), E = Number((b >> 52n) & 0x7ffn), Fr = b & ((1n << 52n) - 1n);
  return E === 0 ? [Fr, -1074] : [Fr | (1n << 52n), E - 1075];
}
function shiftDecimal(s, extraDigits, delta) {  // s decimal string; return s scaled +delta units of 10^-(fracLen+extra)
  const [ip, fp = ''] = s.split('.');
  const K = fp.length + extraDigits;
  let n = BigInt(ip + fp + '0'.repeat(extraDigits)) + BigInt(delta);
  if (n < 0n) n = 0n;
  let t = n.toString();
  if (t.length <= K) t = '0'.repeat(K - t.length + 1) + t;
  return K === 0 ? t : t.slice(0, t.length - K) + '.' + t.slice(t.length - K);
}
function sciForm(s) {   // random equivalent spelling of a non-negative decimal string
  if (!coin(0.4)) return s;
  const [ip, fp = ''] = s.split('.');
  let digits = (ip + fp).replace(/^0+/, '');
  if (digits === '') return s;
  const lead = (ip + fp).length - digits.length;
  const p = ip.length - lead - 1;   // value = d.ddd * 10^p
  digits = digits.replace(/0+$/, '') || '0';
  const mant = digits.length === 1 ? digits : digits[0] + '.' + digits.slice(1);
  const e = coin(0.5) ? 'e' : 'E';
  return mant + e + (p < 0 ? '-' : (coin(0.5) ? '+' : '')) + Math.abs(p);
}
function midpointStrings(x) {
  const [m, e] = decomp(x);
  const out = [];
  out.push(decimalOfDyadic(2n * m + 1n, e - 1));                       // tie above
  const asym = m === (1n << 52n) && e > -1074;
  out.push(asym ? decimalOfDyadic(4n * m - 1n, e - 2) : decimalOfDyadic(2n * m - 1n, e - 1));   // tie below
  const res = [];
  for (const s of out) {
    res.push(s);
    res.push(shiftDecimal(s, rrange(1, 30), 1));
    res.push(shiftDecimal(s, rrange(1, 30), -1));
    if (s.includes('.')) { const cut = s.indexOf('.') + rrange(1, s.length - s.indexOf('.')); res.push(s.slice(0, cut)); }
  }
  return res;
}
function addNum(s) {
  P.push('sn', encS(s), encD(Number(s)));
  P.push('pf', encS(s), encD(parseFloat(s)));
}
function addPI(s, r) { P.push('pi', encS(s), r === undefined ? 'u' : String(r), encD(parseInt(s, r))); }

const NUM_SPECIAL = ['', ' ', '0', '-0', '+0', '00', '-', '+', '.', '-.', '+.', '.5', '5.', '-.5', '+5.', '.e1', '5.e1', '1e', '1e+', '1e-',
  '1e5', '1E5', '1e+5', '1e-5', 'Infinity', '-Infinity', '+Infinity', 'infinity', 'Infinit', 'Infinityx', 'INFINITY', 'NaN', '0x', '0x1', '0X1F', '-0x1', '+0x1',
  '0x1g', '0o7', '0O17', '0o8', '0b101', '0B2', '0b', '0x.1', '1_000', '1,000', '\u0661', '0.0000001', '1.7976931348623157e308', '1.7976931348623158e308',
  '1.7976931348623159e308', '179769313486231580793728971405303415079934132710037826936173778980444968292764750946649017977587207096330286416692887910946555547851940402630657488671505820681908902000708383676273854845817711531764475730270069855571366959622842914819860834936475292719074168444365510704342711559699508093042880177904174497791.9999999', '2.4703282292062327e-324', '2.4703282292062328e-324',
  '4.9406564584124654e-324', '1e-400', '-1e-400', '1e400', '1e99999999999999999999', '0e99999999999999999999', '0.0e-99999999999999999999', ' 12 ', '\u00a012\ufeff',
  '\u180e12', '12\u180e', '1 2', '0.1', '0.30000000000000004', '9007199254740993', '9007199254740992.5', '9007199254740993.0000000001', '0x20000000000001', '0x20000000000003', '0x1fffffffffffff8', '0x' + 'f'.repeat(260), '0x' + 'f'.repeat(256)];
for (const s of NUM_SPECIAL) { addNum(s); addNum(wsPad(s)); }
for (let i = 0; i < 3000; i++) {   // midpoints with long tails
  let x = coin(0.5) ? Math.abs(randFiniteDouble()) : Math.abs(sampleDouble());
  if (x === 0 || !Number.isFinite(x)) x = 1;
  for (const s of midpointStrings(x)) addNum((coin(0.1) ? '-' : '') + sciForm(s));
}
for (let i = 0; i < 1500; i++) {   // subnormal / overflow boundary region
  const x = coin(0.5) ? ofBits(BigInt(rrange(1, 5000))) : stepUlps(1.7976931348623157e308, -rint(3000));
  for (const s of midpointStrings(x)) addNum(sciForm(s));
}
for (let i = 0; i < 12000; i++) {   // random decimal strings
  let s = (coin(0.2) ? pick(['-', '+']) : '') + (coin(0.85) ? randDigits(rrange(1, 30), coin(0.7)) : '');
  if (coin(0.5)) s += '.' + (coin(0.85) ? randDigits(rrange(0, 30), false) : '');
  if (coin(0.5)) s += pick(['e', 'E']) + (coin(0.5) ? pick(['+', '-']) : '') + (coin(0.95) ? String(rrange(0, coin(0.8) ? 400 : 100000)) : '');
  addNum(coin(0.3) ? wsPad(s) : s);
}
for (let i = 0; i < 6000; i++) { const x = sampleDouble(); addNum(coin(0.3) ? wsPad(String(x)) : String(x)); }
for (let i = 0; i < 4000; i++) {   // non-decimal integer literals
  const [pre, r] = pick([['0x', 16], ['0X', 16], ['0o', 8], ['0O', 8], ['0b', 2], ['0B', 2]]);
  const n = coin(0.7) ? rrange(1, 20) : rrange(10, 300);
  let d = ''; for (let k = 0; k < n; k++) d += pick('0123456789abcdefABCDEF'.split('').filter((c) => parseInt(c, 16) < r));
  if (coin(0.05)) d += pick(['g', '8', '2', '.', ' x', '_1']);
  addNum((coin(0.05) ? pick(['-', '+']) : '') + (coin(0.3) ? wsPad(pre + d) : pre + d));
}
const JUNK = '0123456789.eE+-xXoObBIinfyNa_ '.split('');
for (let i = 0; i < 9000; i++) {
  let s = ''; const n = rrange(0, 10);
  for (let k = 0; k < n; k++) s += coin(0.1) ? pick(['Infinity', '0x', '1e', 'e+']) : pick(JUNK);
  addNum(coin(0.2) ? wsPad(s) : s);
}
// parseInt
const RADIX = () => coin(0.15) ? undefined : coin(0.1) ? pick([0, 1, 37, -1, 100, 2 ** 31 - 1]) : coin(0.3) ? pick([0, 10, 16]) : rrange(2, 36);
const PI_ALPHA = '0123456789abcdefghijklmnopqrstuvwxyzABCXYZ'.split('');
for (let i = 0; i < 16000; i++) {
  const r = RADIX();
  let s = coin(0.15) ? pick(['-', '+']) : '';
  if (coin(0.2)) s += pick(['0x', '0X', '0', '00', '0x0']);
  const n = coin(0.8) ? rrange(0, 12) : rrange(13, 120);
  for (let k = 0; k < n; k++) s += pick(PI_ALPHA);
  if (coin(0.2)) s += pick(['.5', 'e3', ' 1', '_2', 'g', '-']);
  addPI(coin(0.3) ? wsPad(s) : s, r);
}
for (let i = 0; i < 8000; i++) {   // long digit strings, generic radices
  const r = coin(0.8) ? pick([3, 5, 6, 7, 9, 11, 12, 13, 17, 19, 23, 29, 31, 35, 36]) : pick([2, 4, 8, 10, 16, 32]);
  const n = rrange(10, 220);
  let s = String(rrange(1, Math.min(r - 1, 9)));
  for (let k = 1; k < n; k++) { const d = rint(r); s += d < 10 ? String(d) : String.fromCharCode(87 + d); }
  addPI((coin(0.1) ? '-' : '') + s, r);
}
for (let i = 0; i < 3000; i++) addPI(String(sampleDouble()), RADIX());
const nP = P.close();

// ================= BigInt =================
const B = writer('bigint.txt');
function addBI(s) { B.push('bi', encS(s), tryStr(() => BigInt(s).toString())); }
const BI_SPECIAL = ['', ' ', '0', '-0', '+0', '00', '-', '+', '0x', '0x1f', '0X1F', '-0x1f', '+0x1f', '0o17', '0b101', '0b2', '1n', '1e3', '1.0', '1.', '.1',
  'Infinity', '-Infinity', 'NaN', ' 12 ', '\u00a012\ufeff', '\u180e12', '1 2', '1_000', '0x_1', '123456789012345678901234567890', '-123456789012345678901234567890'];
for (const s of BI_SPECIAL) { addBI(s); addBI(wsPad(s)); }
for (let i = 0; i < 8000; i++) {
  let s;
  switch (rint(4)) {
    case 0: s = (coin(0.3) ? pick(['-', '+']) : '') + randDigits(rrange(1, 80), coin(0.8)); break;
    case 1: { const [pre, r] = pick([['0x', 16], ['0X', 16], ['0o', 8], ['0b', 2], ['0B', 2], ['0O', 8]]); s = (coin(0.1) ? pick(['-', '+']) : '') + pre; const n = rrange(0, 60); for (let k = 0; k < n; k++) s += rint(r).toString(r); break; }
    case 2: { s = ''; const n = rrange(0, 8); for (let k = 0; k < n; k++) s += pick(JUNK); break; }
    default: s = randDigits(rrange(1, 30)) + pick(['n', '.0', 'e2', ' ', '-', 'x1']);
  }
  addBI(coin(0.3) ? wsPad(s) : s);
}
for (let i = 0; i < 8000; i++) {
  const v = (coin(0.3) ? -1n : 1n) * (coin(0.2) ? BigInt(rint(1000)) : rbig(rrange(1, 400)));
  const r = coin(0.03) ? pick([0, 1, 37, 64]) : coin(0.2) ? 10 : rrange(2, 36);
  B.push('bt', v.toString(), String(r), tryStr(() => v.toString(r)));
}
const nB = B.close();

// ================= string methods =================
const S = writer('str.txt');
const ALPHA = ['a', 'b', 'c', 'A', 'B', 'Z', '0', '1', ' ', '\t', '\n', '\r', '\v', '\f', '\u00a0', '\ufeff', '\u1680', '\u2000', '\u200a', '\u2028',
  '\u2029', '\u202f', '\u205f', '\u3000', '\u180e', '\u200b', '\u0085', '$', '&', '`', "'", '\u00e9', '\u00df', '\u03a3', '\ud83d\ude00', '\ud800', '\udfff',
  '\udc00', '\udbff', '-', '.', 'x', ','];
function subAlpha() { const k = rrange(2, 6); const a = []; for (let i = 0; i < k; i++) a.push(pick(ALPHA)); return a; }
function rstr(alpha, maxLen = 10) { let s = ''; const n = rint(maxLen + 1); for (let i = 0; i < n; i++) s += pick(alpha); return s; }
function rsub(s) { const a = rint(s.length + 1), b = rrange(a, s.length); return s.slice(a, b); }
function rpat(s, alpha) { return coin(0.5) ? rsub(s) : rstr(alpha, 3); }
const REPL = ['$$', '$&', '$`', "$'", '$', '$1', '$01', '$<', '$<a>', 'x', 'yz', '', '$$$', '$0', '\ud83d\ude00'];
function rrepl() { let s = ''; const n = rint(4); for (let i = 0; i < n; i++) s += pick(REPL); return s; }
const N_STR = 6000;
const ib = (b) => (b ? '1' : '0');
for (let i = 0; i < N_STR; i++) {
  const A = subAlpha(), s = rstr(A, 12), t = rstr(A, 12), n = s.length;
  const pat = rpat(s, A);
  const k = rint(n + 3);
  const kInt = rrange(-n - 3, n + 3);
  const cc = s.charCodeAt(k), cp = s.codePointAt(k);
  S.push('cca', encS(s), k, Number.isNaN(cc) ? '!' : cc);
  S.push('cpa', encS(s), k, cp === undefined ? '!' : cp);
  S.push('cha', encS(s), k, encS(s.charAt(k)));
  S.push('at', encS(s), kInt, encOpt(s.at(kInt)));
  { const a = rrange(-n - 3, n + 3), b = coin(0.2) ? undefined : rrange(-n - 3, n + 3);
    S.push('sl', encS(s), a, b === undefined ? 'u' : b, encS(s.slice(a, b)));
    S.push('ss', encS(s), a, b === undefined ? 'u' : b, encS(s.substring(a, b))); }
  { const p = coin(0.2) ? undefined : rint(n + 3);
    S.push('io', encS(s), encS(pat), p === undefined ? 'u' : p, s.indexOf(pat, p));
    S.push('inc', encS(s), encS(pat), p === undefined ? 'u' : p, ib(s.includes(pat, p)));
    S.push('sw', encS(s), encS(pat), p === undefined ? 'u' : p, ib(s.startsWith(pat, p))); }
  { const p = coin(0.3) ? undefined : rint(n + 3);
    S.push('lio', encS(s), encS(pat), p === undefined ? 'u' : p, s.lastIndexOf(pat, p));
    S.push('ew', encS(s), encS(pat), p === undefined ? 'u' : p, ib(s.endsWith(pat, p))); }
  S.push('tm', encS(s), encS(s.trim()));
  S.push('tms', encS(s), encS(s.trimStart()));
  S.push('tme', encS(s), encS(s.trimEnd()));
  { const m = rint(n + 12), fill = coin(0.2) ? '' : rstr(A, 3);
    S.push('ps', encS(s), m, encS(fill), encS(s.padStart(m, fill)));
    S.push('pe', encS(s), m, encS(fill), encS(s.padEnd(m, fill))); }
  { const r = rint(5); S.push('rp', encS(s), r, encS(s.repeat(r))); }
  { const sep = coin(0.15) ? '' : rpat(s, A), lim = coin(0.5) ? undefined : rint(6);
    S.push('sp', encS(s), encS(sep), lim === undefined ? 'u' : lim, encL(s.split(sep, lim))); }
  { const rp = rrepl();
    S.push('rf', encS(s), encS(pat), encS(rp), encS(s.replace(pat, rp)));
    S.push('ra', encS(s), encS(pat), encS(rp), encS(s.replaceAll(pat, rp))); }
  { const args = []; const na = rint(4); for (let j = 0; j < na; j++) args.push(rstr(A, 4)); S.push('cc', encS(s), encL(args), encS(s.concat(...args))); }
  { let asc = ''; const na = rint(14); for (let j = 0; j < na; j++) asc += String.fromCharCode(coin(0.9) ? rrange(32, 126) : rint(128));
    S.push('up', encS(asc), encS(asc.toUpperCase()));
    S.push('lo', encS(asc), encS(asc.toLowerCase()));
    const mixed = coin(0.5) ? asc : s;
    S.push('asc', encS(mixed), ib(/^[\x00-\x7f]*$/.test(mixed))); }
  { const codes = []; const nc = rint(6); for (let j = 0; j < nc; j++) codes.push(coin(0.7) ? rint(0x10000) : rint(2 ** 33));
    S.push('fcc', codes.length ? codes.join(',') : '~', encS(String.fromCharCode(...codes))); }
  { const cps = []; const nc = rint(5); for (let j = 0; j < nc; j++) cps.push(coin(0.9) ? (coin(0.5) ? rint(0x10000) : rint(0x110000)) : rrange(0x10FFFF, 0x110010));
    S.push('fcp', cps.length ? cps.join(',') : '~', tryStr(() => encS(String.fromCodePoint(...cps)))); }
  { const cps = [...s].map((c) => c.codePointAt(0)); S.push('cps', encS(s), cps.length ? cps.join(',') : '~'); }
  { const u = coin(0.3) ? s.slice(0, rint(n + 1)) + rstr(A, 3) : t;
    S.push('cmp', encS(s), encS(u), ib(s < u) + ib(s <= u) + ib(s > u) + ib(s >= u)); }
  { const parts = []; const np = rint(5); for (let j = 0; j < np; j++) parts.push(rstr(A, 4)); const sep = rstr(A, 2);
    S.push('join', encL(parts), encS(sep), encS(parts.join(sep))); }
}
const nS = S.close();
console.log(`wrote fmt=${nF} parse=${nP} bigint=${nB} str=${nS} lines to ${outDir} (seed ${process.argv[3] || 20261023})`);
