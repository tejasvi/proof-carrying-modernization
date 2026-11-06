// @panic non-null assertion on undefined
// A comparison of a bigint held as any: not modelled (Node compares 1n and 2 mathematically and
// prints true), so the model stops there.
function lt(a: any, b: any): boolean { return a < b; }
console.log(`${lt(1, 2)}`);
console.log(`${lt(1n, 2)}`);
