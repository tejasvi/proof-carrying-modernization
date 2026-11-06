// @extern
// @panic non-null assertion on undefined
// JSON.stringify is an external call, replayed from the Node run. For undefined, a function or a
// symbol at the top level (and when toJSON gives undefined) its result is undefined, though
// TypeScript types it string: where a string is needed the Lean run stops there (the last line,
// where Node's typeof prints undefined; the catch around the call does not catch a panic); where
// `string | undefined` is expected, it is undefined. Nested undefined and function values are
// left out of objects and become null in arrays, and toJSON is used: the replayed answers carry
// that.
interface Opt { a?: number; b: string | undefined; f?: () => number }
const o: Opt = { b: undefined, f: () => 1 };
console.log(`${JSON.stringify(o)} ${JSON.stringify({ a: 1, b: "x" })} ${JSON.stringify([undefined, 1, null])}`);
class Money {
  constructor(public cents: number) {}
  toJSON(): string { return `${this.cents / 100} EUR`; }
}
console.log(`${JSON.stringify(new Money(250))} ${JSON.stringify({ price: new Money(5), n: 2 })}`);
// (a function's declared result: TypeScript would narrow a `string | undefined` variable
// initialised with the call to string)
function maybe(x: unknown): string | undefined { return JSON.stringify(x); }
const nothing: unknown = undefined;
console.log(`${maybe(nothing) === undefined} ${maybe(0)} ${JSON.stringify(null)} ${JSON.stringify([nothing])}`);
function describe(e: unknown): string {
  if (e instanceof Error) return e.message;
  try { return JSON.stringify(e); } catch { return String(e); }
}
console.log(`${describe(new Error("boom"))} ${describe({ code: 7 })} ${describe("s")} ${describe(null)}`);
console.log(typeof describe(undefined));
