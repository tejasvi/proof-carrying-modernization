// @panic
// Object types with named properties and a string index signature are dictionaries: a named
// property is a dictionary entry (an optional one may be absent), read at the type TypeScript
// gives it; references share the object (a write through one is seen through another). Where
// the named type is narrower than the index type the read is a checked cast: the last line reads
// a value of the wrong type, which Node prints and the Lean run stops at (a panic).
interface Consent { state?: unknown; v?: unknown; [k: string]: unknown }
interface Shape { name: string; size: number; [k: string]: unknown }
interface Counts { total: number; [k: string]: number }
function stateOf(c: Consent): string { return c.state === undefined ? "absent" : `state=${String(c.state)}`; }
const c1: Consent = { v: 2 };
const c2: Consent = { state: "granted", v: 3, extra: true };
console.log(`${stateOf(c1)} ${stateOf(c2)} ${String(c2.extra)} ${Object.keys(c2).join(",")}`);
const alias = c1;
alias.state = "pending";
c1.note = "x";
console.log(`${stateOf(c1)} ${String(alias.note)} ${c1 === alias} ${Object.keys(c1).join(",")}`);
const counts: Counts = { total: 0 };
for (const w of ["a", "b", "a"]) { counts[w] = (counts[w] ?? 0) + 1; counts.total += 1; }
console.log(`${counts.total} ${counts.a} ${counts.b} ${"c" in counts}`);
const s: Shape = { name: "box", size: 3, color: "red" };
const { name, size } = s;
console.log(`${name} ${size + 1} ${String(s.color)} ${s.name.toUpperCase()}`);
const raw: Record<string, unknown> = { name: "odd", size: "three" };
const odd = raw as Shape;
console.log(`${odd.name} ok`);
console.log(`${odd.size + 1}`);
