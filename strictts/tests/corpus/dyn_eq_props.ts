// === on unknown values compares runtime values (strings by content, numbers by IEEE equality,
// objects by identity, values of different types differ); Record<string, unknown> reads give
// undefined for absent keys; narrowing by typeof, instanceof and `in`; checked casts; an
// optional unknown field narrowed to `{}` (not undefined, not null) is still any value.
class P { constructor(public n: number) {} }
const p1 = new P(1);
const p2 = new P(1);
const xs = [1];
const vals: unknown[] = [1, "1", 1n, true, null, undefined, NaN, -0, 0, p1, p2, xs, [1], "x"];
const rows: string[] = [];
for (const a of vals) {
  let row = "";
  for (const b of vals) row += a === b ? "1" : "0";
  rows.push(row);
}
console.log(rows.join(" "));
const alias: unknown = p1;
console.log(`${alias === p1} ${alias === p2} ${alias !== p2}`);
const rec: Record<string, unknown> = { a: 1, b: "two", c: null, d: [1, 2], f: new Error("bad") };
function describe(v: unknown): string {
  if (typeof v === "number") return `number ${v + 1}`;
  if (typeof v === "string") return `string ${v.toUpperCase()}`;
  if (v === null) return "null";
  if (v === undefined) return "undefined";
  if (v instanceof Error) return `error ${v.message}`;
  if (typeof v === "object" && "length" in v) return "has length";
  return typeof v;
}
console.log(["a", "b", "c", "d", "e", "f"].map((k) => describe(rec[k])).join(", "));
console.log(`${"a" in rec} ${"z" in rec} ${rec.e === undefined} ${String(rec.d)} ${String(rec.f)}`);
function total(items: unknown[]): number {
  let s = 0;
  for (const it of items) if (typeof it === "number" && it === it) s += it;
  return s;
}
console.log(`${total([1, "2", 3, NaN, null, 4])} ${(rec.a as number) * 10} ${(rec.b as string).length}`);
const back = vals[0] as number;
console.log(`${back + 1} ${typeof (vals[1] as string)}`);
interface Signal { band?: unknown }
function bandText(u: Signal): string {
  if (u.band !== undefined && u.band !== null && u.band !== "adult") return "other";
  return "adult or none";
}
console.log([bandText({}), bandText({ band: "adult" }), bandText({ band: "teen" }), bandText({ band: 3 }), bandText({ band: null })].join(","));
