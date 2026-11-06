// @reject no-any
// @strict
// the original subset (--strict / --no-dyn): unknown is only allowed for catch variables
function f(x: unknown): string { return typeof x === "string" ? x : "?"; }
console.log(f("a"));
