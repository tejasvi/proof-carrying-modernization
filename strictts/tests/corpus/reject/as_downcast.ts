// @reject as-downcast
// @strict
// (outside the strict subset a narrowing `as` is a checked narrowing: corpus as_narrowing)
type Shape = { kind: "a"; x: bigint } | { kind: "b"; y: bigint };
function f(s: Shape): bigint { return (s as { kind: "a"; x: bigint }).x; }
console.log(`${f({ kind: "a", x: 1n })}`);
