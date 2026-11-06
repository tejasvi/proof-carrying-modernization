// Optional chaining on values of type any/unknown: each `?.` link yields undefined when the
// value before it is undefined or null, without reading a property of it.
function f(p: Record<string, unknown>): unknown { return (p as any)?.a?.b?.c; }
function g(p: unknown): unknown { return (p as any)?.["x"]?.y; }
const show = (x: unknown): string => (x === undefined ? "undefined" : x === null ? "null" : String(x));
console.log([f({}), f({ a: null }), f({ a: { b: {} } }), f({ a: { b: { c: 2 } } }), f({ a: { b: null } })].map(show).join(" "));
console.log([g(undefined), g(null), g({}), g({ x: { y: 3 } }), g({ x: undefined })].map(show).join(" "));
