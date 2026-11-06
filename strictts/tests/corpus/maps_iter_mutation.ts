// Live Map/Set iteration: entries added during iteration are visited, deleted ones skipped.
const m = new Map<string, bigint>([["a", 1n], ["b", 2n], ["c", 3n]]);
for (const [k, v] of m) {
  console.log(`visit ${k}=${v}`);
  if (k === "a") { m.delete("b"); m.set("d", 4n); }
  if (k === "c") m.set("a", 10n);
}
console.log([...m.entries()].map(([k, v]) => `${k}${v}`).join(" "));
const s = new Set<string>(["x", "y"]);
for (const v of s) {
  console.log(`set visit ${v}`);
  if (v === "x") { s.delete("y"); s.add("z"); s.add("x"); }
}
console.log([...s].join(","));
const keys = new Map<string, bigint>([["p", 1n]]);
for (const k of keys.keys()) {
  if (k === "p") keys.set("q", 2n);
  console.log(`key ${k}`);
}
