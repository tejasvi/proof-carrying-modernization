// @reject no-any
// @strict
// the original subset (--strict / --no-dyn): any is not allowed
function f(x: any): string { return String(x); }
console.log(f("a"));
