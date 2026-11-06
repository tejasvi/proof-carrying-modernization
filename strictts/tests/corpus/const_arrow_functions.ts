// Module-level `const f = (…) => …` are translated as functions, except where code that runs
// before the declaration can reach f: reading f there throws, as in JavaScript (temporal dead
// zone), so such an f stays a module variable.
function early(): number { return later(2); }
let caught = "none";
try { early(); } catch (e) { caught = (e as Error).name; }
const later = (x: number): number => x * 10;
const twice = (x: number): number => later(x) * 2;
const fact = (n: number): number => (n <= 1 ? 1 : n * fact(n - 1));
const apply = (g: (x: number) => number, v: number): number => g(v);
console.log(`${caught} ${early()} ${twice(3)} ${fact(5)} ${apply(twice, 4)} ${[1, 2].map(twice).join(",")}`);
