// @numbers
// Math functions (exactly specified ones) and Number predicates.
const vals = [2.5, -2.5, 3.7, -3.7, 0.5, -0.5];
console.log(vals.map((v) => `${Math.floor(v)},${Math.ceil(v)},${Math.round(v)},${Math.trunc(v)}`).join(" "));
console.log(`${Math.abs(-4)} ${Math.sign(-3)} ${Math.sign(0)} ${Math.sqrt(16)} ${Math.sqrt(2)} ${Math.max(1, 5, 3)} ${Math.min(4, -2)}`);
console.log(`${Math.max()} ${Math.min()} ${Math.max(NaN, 1)} ${Math.hypot(3, 4)} ${Math.fround(5.5)} ${Math.clz32(1)}`);
console.log(`${Math.imul(3, 4)} ${Math.imul(0xffffffff, 5)} ${Math.PI} ${Math.E}`);
console.log(`${Number.isInteger(5)} ${Number.isInteger(5.5)} ${Number.isSafeInteger(2 ** 53)} ${Number.isFinite(1 / 0)}`);
console.log(`${Math.pow(2, 10)} ${2 ** 0.5 === Math.SQRT2} ${Math.round(-0.4)}`);
