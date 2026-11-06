// @reject any-op
// arithmetic on an any value is not one of the operations on unknown values (cast it first)
function inc(x: any): number { return x + 1; }
console.log(String(inc(1)));
