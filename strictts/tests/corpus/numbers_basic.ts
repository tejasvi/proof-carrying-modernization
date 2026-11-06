// @numbers
// number arithmetic and formatting: IEEE semantics, NaN, Infinity, -0, toString/toFixed.
const a = 0.1 + 0.2;
console.log(`${a} ${a === 0.3} ${0.5 + 0.25}`);
console.log(`${1 / 3} ${2 / 3} ${10 / 4} ${7 % 3} ${-7 % 3} ${5.5 % 2}`);
console.log(`${1 / 0} ${-1 / 0} ${0 / 0} ${(0 / 0) === (0 / 0)} ${Number.isNaN(0 / 0)}`);
console.log(`${-0} ${0 * -1} ${1 / -0} ${-0 === 0}`);
console.log(`${2 ** 53} ${2 ** 53 + 1} ${Number.MAX_SAFE_INTEGER} ${Number.EPSILON}`);
console.log(`${1e21} ${1e-7} ${123456789012345680000} ${0.000001}`);
console.log(`${(1234.5678).toFixed(2)} ${(0.000001234).toPrecision(2)} ${(255).toString(16)} ${(255).toString(2)}`);
console.log(`${(1e21).toFixed(2)} ${(-1.5).toFixed(0)} ${(2.5).toFixed(0)} ${(1.005).toFixed(2)}`);
console.log(`${5 | 3} ${5 & 3} ${5 ^ 3} ${~5} ${1 << 31} ${-1 >>> 0} ${-16 >> 2} ${2 ** 32 | 0}`);
let x = 1;
for (let i = 0; i < 60; i++) x *= 2;
console.log(`${x} ${x + 1 === x}`);
console.log(`${Number("42")} ${Number("  3.5  ")} ${Number("")} ${Number("abc")} ${Number("0x1f")}`);
console.log(`${parseInt("42px")} ${parseInt("ff", 16)} ${parseFloat("3.14abc")} ${parseInt("  -12")}`);
