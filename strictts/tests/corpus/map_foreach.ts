// Map.forEach callback arguments (value, key, map) and mutation during forEach.
const m = new Map<string, bigint>([["x", 1n], ["y", 2n]]);
m.forEach((v, k, map) => {
  console.log(`${k}=${v} same=${map === m}`);
  if (k === "x") map.set("z", 3n);
});
const counts = new Map<string, bigint>();
for (const w of ["the", "cat", "the", "hat", "the", "end"]) counts.set(w, (counts.get(w) ?? 0n) + 1n);
counts.forEach((n, w) => console.log(`${w}: ${n}`));
