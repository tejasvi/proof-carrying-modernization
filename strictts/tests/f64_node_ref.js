'use strict';
// Reference results from V8 for the StrictTS F64 differential test (driven by tests/F64Diff.lean).
// usage: node tests/f64_node_ref.js IN OUT
// Each IN line is "op arg..." (doubles as 16 hex digits of their bit pattern); each OUT line is
// the result: a double as 16 hex digits (every NaN as 7ff8000000000000), an integer in decimal,
// or 1/0 for booleans.
const fs = require('fs');

const dv = new DataView(new ArrayBuffer(8));
function num(h) { dv.setBigUint64(0, BigInt('0x' + h)); return dv.getFloat64(0); }
function hex(x) {
  if (Number.isNaN(x)) return '7ff8000000000000';
  dv.setFloat64(0, x);
  return dv.getBigUint64(0).toString(16).padStart(16, '0');
}
const f32 = new Float32Array(1);
const u32 = new Uint32Array(f32.buffer);
function f32hex(x) {
  if (Number.isNaN(x)) return '7fc00000';
  f32[0] = x;
  return u32[0].toString(16).padStart(8, '0');
}
const i8 = new Int8Array(1), u8 = new Uint8Array(1), i16 = new Int16Array(1), u16 = new Uint16Array(1);
const u8c = new Uint8ClampedArray(1);
const b = v => (v ? '1' : '0');

const ops = {
  // unary
  jsRound: a => hex(Math.round(num(a))),
  floor: a => hex(Math.floor(num(a))),
  ceil: a => hex(Math.ceil(num(a))),
  trunc: a => hex(Math.trunc(num(a))),
  sqrt: a => hex(Math.sqrt(num(a))),
  sign: a => hex(Math.sign(num(a))),
  abs: a => hex(Math.abs(num(a))),
  neg: a => hex(-num(a)),
  fround: a => hex(Math.fround(num(a))),
  toF32Bits: a => f32hex(num(a)),
  clz32: a => hex(Math.clz32(num(a))),
  bnot: a => hex(~num(a)),
  toInt32: a => String(num(a) | 0),
  toUint32: a => String(num(a) >>> 0),
  toInt8: a => { i8[0] = num(a); return String(i8[0]); },
  toUint8: a => { u8[0] = num(a); return String(u8[0]); },
  toInt16: a => { i16[0] = num(a); return String(i16[0]); },
  toUint16: a => { u16[0] = num(a); return String(u16[0]); },
  toUint8Clamp: a => { u8c[0] = num(a); return String(u8c[0]); },
  isInteger: a => b(Number.isInteger(num(a))),
  isSafeInteger: a => b(Number.isSafeInteger(num(a))),
  isFinite: a => b(Number.isFinite(num(a))),
  isNaN: a => b(Number.isNaN(num(a))),
  toBigInt: a => { const x = num(a); return Number.isInteger(x) ? BigInt(x).toString() : 'none'; },
  // binary
  add: (a, c) => hex(num(a) + num(c)),
  sub: (a, c) => hex(num(a) - num(c)),
  mul: (a, c) => hex(num(a) * num(c)),
  div: (a, c) => hex(num(a) / num(c)),
  rem: (a, c) => hex(num(a) % num(c)),
  min: (a, c) => hex(Math.min(num(a), num(c))),
  max: (a, c) => hex(Math.max(num(a), num(c))),
  imul: (a, c) => hex(Math.imul(num(a), num(c))),
  band: (a, c) => hex(num(a) & num(c)),
  bor: (a, c) => hex(num(a) | num(c)),
  bxor: (a, c) => hex(num(a) ^ num(c)),
  shl: (a, c) => hex(num(a) << num(c)),
  sar: (a, c) => hex(num(a) >> num(c)),
  shr: (a, c) => hex(num(a) >>> num(c)),
  lt: (a, c) => b(num(a) < num(c)),
  le: (a, c) => b(num(a) <= num(c)),
  eq: (a, c) => b(num(a) === num(c)),
  sameValue: (a, c) => b(Object.is(num(a), num(c))),
  sameValueZero: (a, c) => b([num(a)].includes(num(c))),
  // conversions from exact values
  ofBigInt: s => hex(Number(BigInt(s))),
  // "dec <sign> <digits> <exp>": the decimal literal (-)digits e exp, correctly rounded by V8
  dec: (s, d, e) => hex(Number((s === '1' ? '-' : '') + d + 'e' + e)),
};

const lines = fs.readFileSync(process.argv[2], 'utf8').split('\n');
const out = [];
for (const line of lines) {
  if (line === '') continue;
  const parts = line.split(' ');
  const f = ops[parts[0]];
  if (f === undefined) throw new Error('unknown op ' + parts[0]);
  out.push(f(...parts.slice(1)));
}
fs.writeFileSync(process.argv[3], out.join('\n') + '\n');
