// @reject any-op
// a method call on an any value is not one of the operations on unknown values
function f(x: any): string { return x.trim(); }
console.log(f(" a "));
