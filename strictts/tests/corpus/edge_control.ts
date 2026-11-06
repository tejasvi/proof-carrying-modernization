// Edge cases of control flow: continue in do-while, finally with break/continue,
// indexed for-of over entries(), holes-free destructuring, comma and void.
let i = 0n;
let out = "";
do {
  i++;
  if (i === 2n) continue;
  out += `${i}`;
} while (i < 4n);
console.log(`do-continue ${out}`);
const order: string[] = [];
for (const k of ["a", "b", "c"]) {
  try {
    if (k === "b") continue;
    if (k === "c") break;
    order.push(`body ${k}`);
  } finally {
    order.push(`finally ${k}`);
  }
}
console.log(order.join(", "));
for (const [idx, v] of ["x", "y", "z"].entries()) console.log(`entry ${idx === 0 ? "first" : "next"} ${v}`);
const [, second, , fourth] = ["1", "2", "3", "4"];
console.log(`${second} ${fourth}`);
let n = 0n;
const r = (n++, n++, n);
console.log(`comma ${r}`);
const u: undefined = void 0;
console.log(`void ${u === undefined}`);
function early(xs: bigint[]): string {
  for (const x of xs) {
    switch (x) {
      case 0n: return "zero first";
      case 1n: continue;
      default: if (x > 5n) return `big ${x}`;
    }
  }
  return "none";
}
console.log(`${early([1n, 1n, 9n])} ${early([0n])} ${early([1n, 2n])}`);
