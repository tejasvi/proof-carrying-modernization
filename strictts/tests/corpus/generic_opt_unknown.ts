// An `unknown` that is undefined at an optional type (an optional field or parameter of type
// unknown, a type parameter T instantiated with unknown in `T | undefined`, a dictionary entry or
// Map value of type unknown that is undefined) is undefined: `=== undefined` and checked
// casts see it so.
interface H { a?: unknown }
const x: unknown = undefined;
const h: H = { a: x };
function opt(p?: unknown): boolean { return p === undefined; }
console.log(`${h.a === undefined} ${opt(x)} ${opt()}`);
const d: Record<string, unknown> = { a: undefined, b: 1 };
const m = new Map<string, unknown>([["k", undefined]]);
console.log(`${m.get("k") === undefined} ${d.a === undefined}`);
const xs: unknown[] = [undefined];
console.log(`${xs.find(() => true) === undefined} ${xs[0] === undefined}`);
function show<T>(v: T | undefined): string { return v === undefined ? "u" : "v"; }
console.log(`${show(d.a)} ${show(d.b)} ${show(d.c)} ${show(m.get("k"))} ${show(h.a)} ${show(x)} ${show(xs[0])}`);
function firstOr<T>(ys: T[]): T | undefined { return ys.length ? ys[0] : undefined; }
console.log(`${firstOr(xs) === undefined} ${firstOr<unknown>([]) === undefined}`);
