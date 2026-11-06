// Functions as values: top-level functions passed as callbacks, returned closures, compose.
function double(x: bigint): bigint { return x * 2n; }
function inc(x: bigint): bigint { return x + 1n; }
function apply(f: (x: bigint) => bigint, x: bigint): bigint { return f(x); }
function compose(f: (x: bigint) => bigint, g: (x: bigint) => bigint): (x: bigint) => bigint {
  return (x) => g(f(x));
}
console.log(`${apply(double, 21n)} ${apply(inc, 1n)} ${compose(double, inc)(5n)}`);
const pipeline: ((x: bigint) => bigint)[] = [double, inc, double];
let v = 1n;
for (const f of pipeline) v = f(v);
console.log(`pipeline ${v}`);
console.log([1n, 2n, 3n].map(double).join(","));
const table = new Map<string, (a: bigint, b: bigint) => bigint>([
  ["add", (a, b) => a + b],
  ["mul", (a, b) => a * b],
]);
for (const [name, op] of table) console.log(`${name} ${op(6n, 7n)}`);
function repeat(n: bigint, f: () => void): void { for (let i = 0n; i < n; i++) f(); }
let hits = 0n;
repeat(3n, () => { hits++; });
console.log(`hits ${hits}`);
const maybeFn: ((s: string) => string) | undefined = (s) => s + "?";
console.log(maybeFn?.("ok") ?? "none");
