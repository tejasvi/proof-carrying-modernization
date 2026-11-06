// Nested generic collections: Map<string, Set<bigint>>, Map of arrays, arrays of maps.
const index = new Map<string, Set<bigint>>();
function addTo(key: string, v: bigint): void {
  let s = index.get(key);
  if (s === undefined) {
    s = new Set<bigint>();
    index.set(key, s);
  }
  s.add(v);
}
addTo("a", 1n); addTo("b", 2n); addTo("a", 3n); addTo("a", 1n);
for (const [k, s] of index) console.log(`${k}: ${[...s].join(",")}`);
const grid: Map<string, bigint>[] = [new Map([["x", 1n]]), new Map([["y", 2n]])];
grid[1].set("z", 3n);
console.log(grid.map((m) => [...m.keys()].join("")).join("|"));
const nested: bigint[][] = [[1n], [2n, 3n]];
nested[0].push(4n);
console.log(nested.map((r) => r.join("+")).join(" ; "));
