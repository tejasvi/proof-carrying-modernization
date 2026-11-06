// Map basics: insertion order, overwrite, delete, has, size, keys/values/entries snapshots.
const m = new Map<string, bigint>();
m.set("one", 1n).set("two", 2n).set("three", 3n);
m.set("one", 100n);
console.log(`${m.get("one") ?? 0n} ${m.has("two")} ${m.has("four")} size3=${m.size === 3}`);
console.log(`deleted ${m.delete("two")} again ${m.delete("two")}`);
console.log([...m.keys()].join(","));
console.log(Array.from(m.values()).join(","));
console.log([...m.entries()].map(([k, v]) => `${k}:${v}`).join(" "));
m.set("two", 22n);
for (const [k, v] of m) console.log(`${k} => ${v}`);
const byLen = new Map<bigint, string[]>();
for (const w of ["a", "bb", "cc", "d"]) {
  const k = w === "a" || w === "d" ? 1n : 2n;
  const list = byLen.get(k);
  if (list === undefined) byLen.set(k, [w]);
  else list.push(w);
}
for (const [k, ws] of byLen) console.log(`${k}: ${ws.join(" ")}`);
m.clear();
console.log(`cleared ${m.size === 0}`);
const fromEntries = new Map([["x", "X"], ["y", "Y"]]);
const copy = new Map(fromEntries);
copy.set("z", "Z");
console.log(`${[...fromEntries.keys()].join("")} ${[...copy.keys()].join("")}`);
