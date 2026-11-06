// @extern
// for…of over unknown values iterates arrays of any element type by index (live: the length is
// read at every step); array methods on unknown values narrowed to any[] act on them as arrays of
// unknown values (JSON arrays here, replayed from the Node run).
function sumAll(xs: any): number {
  let s = 0;
  for (const x of xs) {
    if (typeof x === "number") s += x;
    else if (x === "stop") break;
  }
  return s;
}
console.log(`${sumAll([1, 2, "a", 3])} ${sumAll([1, "stop", 5])} ${sumAll([])}`);
const grow: number[] = [1, 2];
let seen = 0;
const view: any = grow;
for (const x of view) {
  seen++;
  if (grow.length < 5) grow.push(x as number);
}
console.log(`${seen} ${grow.join(",")}`);
const parsed: any = JSON.parse('[3, 1, 2, "x", null]');
if (Array.isArray(parsed)) {
  const nums = parsed.filter((v) => typeof v === "number" && v > 1);
  console.log(`${nums.length} ${parsed.map((v) => String(v)).join("|")} ${parsed.some((v) => v === null)}`);
}
const pairs: unknown = [[1, "a"], [2, "b"]];
for (const p of pairs as any) console.log(`${String(p[0])}=${String(p[1])}`);
