// Objects used as dictionaries: key order (array indices ascending, then the other keys in
// insertion order), reads and writes, `in`, delete, Object.keys/values/entries, hasOwn,
// literals with numeric, computed and spread keys, ??= and ++ on entries.
const d: Record<string, number> = {};
d["b"] = 1;
d["a"] = 2;
d["10"] = 3;
d["2"] = 4;
d["-1"] = 5;
d["01"] = 6;
d.z = 7;
d[1.5] = 8;
d[4294967294] = 9;
d[4294967295] = 10;
console.log(Object.keys(d).join(","));
console.log(Object.values(d).join(","));
console.log(Object.entries(d).map(([k, v]) => `${k}=${v}`).join(" "));
d["b"] = 11;
delete d["a"];
d["a"] = 12;
d.z++;
d["2"] += 100;
console.log(Object.entries(d).map(([k, v]) => `${k}=${v}`).join(" "));
console.log(`${"a" in d} ${"q" in d} ${"toString" in d} ${Object.hasOwn(d, "toString")} ${d.hasOwnProperty("z")} ${delete d["nothing"]}`);
const counts: { [word: string]: number } = {};
for (const w of "the cat and the hat and the bat".split(" ")) counts[w] = (counts[w] ?? 0) + 1;
console.log(Object.entries(counts).map(([k, v]) => `${k}:${v}`).join(" "));
const idx: Record<string, string> = { 3: "three", 1: "one", x: "ex", [`k${2}`]: "k2", 2.50: "two and a half" };
console.log(Object.entries(idx).map(([k, v]) => `${k}=${v}`).join(" "));
const merged: Record<string, string> = { ...idx, 0: "zero", x: "EX" };
console.log(Object.entries(merged).map(([k, v]) => `${k}=${v}`).join(" "));
const groups: Record<string, string[]> = {};
for (const w of ["apple", "avocado", "banana", "blueberry", "cherry"]) {
  const k = w.charAt(0);
  groups[k] ??= [];
  groups[k].push(w);
}
console.log(Object.keys(groups).map((k) => `${k}:${groups[k].join("/")}`).join(" "));
const opt: Record<string, number | undefined> = { a: undefined };
console.log(`${opt.a ?? "u"} ${"a" in opt} ${opt.b ?? "u"} ${"b" in opt} ${Object.keys(opt).length}`);
