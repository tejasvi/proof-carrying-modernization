// Spreads into object literals: conditional spreads `...(c ? { k: v } : {})` and
// `...(c && { k: v })` (the empty object contributes nothing; later properties win), spreads of
// optional values and of unions of records, and spreads of mutable objects (read at the spread).
function flags(young: boolean, ask: boolean): { kind: string; under13?: boolean; reask?: { pending: boolean } } {
  return { kind: "minor", ...(young ? { under13: true } : {}), ...(ask && { reask: { pending: true } }) };
}
for (const [y, a] of [[true, true], [false, true], [true, false], [false, false]] as [boolean, boolean][]) {
  const f = flags(y, a);
  console.log(`${f.kind} ${f.under13 ?? "-"} ${f.reask?.pending ?? "-"}`);
}
function override(n: number): { a: number; b: number } {
  return { a: 1, b: 2, ...(n > 0 ? { a: n } : {}), ...(n > 10 ? {} : { b: -n }) };
}
console.log([0, 5, 20].map((n) => { const o = override(n); return `${o.a}/${o.b}`; }).join(" "));
interface P { x: number; y: number }
const base: P | undefined = [{ x: 1, y: 2 }].find((p) => p.x === 1);
const none: P | undefined = [{ x: 1, y: 2 }].find((p) => p.x === 9);
const q1 = { x: 0, y: 0, ...base, z: 3 };
const q2 = { x: 0, y: 0, ...none, z: 3 };
console.log(`${q1.x},${q1.y},${q1.z} ${q2.x},${q2.y},${q2.z}`);
class Counter { n = 0; label = "c"; bump(): void { this.n++; } }
const cnt = new Counter();
cnt.bump();
const snap = { ...cnt, extra: true };
cnt.bump();
console.log(`${snap.n} ${snap.label} ${snap.extra} ${cnt.n}`);
