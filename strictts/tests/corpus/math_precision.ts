// Math functions that Impl.host computes with libm: log1p and expm1 near 0 keep their precision,
// hypot neither overflows nor underflows and gives Infinity for an infinite argument even with
// NaN. (Printed rounded to 12 digits: the last bits are implementation-approximated.)
const r = (x: number): string => x.toPrecision(12);
console.log([1e-6, 1e-12, -1e-9, 3, -0.5].map((x) => r(Math.log1p(x))).join(" "));
console.log([1e-6, 1e-12, -1e-9, 3, -50].map((x) => r(Math.expm1(x))).join(" "));
console.log(`${Math.log1p(-1)} ${Math.log1p(Infinity)} ${Math.expm1(Infinity)} ${Math.expm1(-Infinity)} ${1 / Math.log1p(-0) === -Infinity} ${1 / Math.expm1(-0) === -Infinity}`);
console.log(`${r(Math.hypot(3e200, 4e200))} ${r(Math.hypot(3e-200, 4e-200))} ${Math.hypot(Infinity, NaN)} ${Math.hypot(NaN, -Infinity)} ${Math.hypot(NaN, 1)} ${Math.hypot(0, -0)} ${Math.hypot(3, 4)}`);
