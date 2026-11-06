// BigInt semantics: truncating division, remainder sign, exponent, bitwise ops, shifts, asIntN.
const vals: bigint[] = [7n, -7n];
for (const a of vals) {
  for (const b of [2n, -2n]) console.log(`${a}/${b}=${a / b} ${a}%${b}=${a % b}`);
}
console.log(`${2n ** 64n} ${(-2n) ** 3n} ${10n ** 0n}`);
console.log(`${0b1100n & 0b1010n} ${0b1100n | 0b1010n} ${0b1100n ^ 0b1010n} ${~5n}`);
console.log(`${-6n & 3n} ${-6n | 3n} ${-6n ^ 3n}`);
console.log(`${1n << 70n} ${-1024n >> 3n} ${5n >> 10n} ${-5n >> 10n}`);
console.log(`${-(-3n)} ${0n === -0n} ${123456789n * 987654321n}`);
let x = 1n;
for (let i = 0n; i < 70n; i++) x *= 3n;
console.log(`3^70 = ${x}`);
