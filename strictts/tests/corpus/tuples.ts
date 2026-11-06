// Tuples: construction, indexing, destructuring, as map entries and return values.
function divmod(a: bigint, b: bigint): [bigint, bigint] { return [a / b, a % b]; }
const [q, r] = divmod(17n, 5n);
console.log(`q=${q} r=${r}`);
const pair: [string, bigint] = ["x", 1n];
console.log(`${pair[0]}=${pair[1]} len=${pair.length === 2}`);
const entries: [string, bigint][] = [["a", 1n], ["b", 2n]];
const m = new Map(entries);
for (const [k, v] of m) console.log(`${k}->${v}`);
function swap<A, B>(t: [A, B]): [B, A] { return [t[1], t[0]]; }
const sw = swap(pair);
console.log(`${sw[0]} ${sw[1]}`);
const triple: readonly [bigint, string, boolean] = [1n, "two", true];
const [one, two, three] = triple;
console.log(`${one} ${two} ${three}`);
