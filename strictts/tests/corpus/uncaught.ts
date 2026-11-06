// An exception escaping the module body ends the program.
function check(x: bigint): bigint {
  if (x > 2n) throw new Error(`too big: ${x}`);
  return x;
}
for (const v of [1n, 2n, 3n, 4n]) {
  console.log(`checked ${check(v)}`);
}
console.log("not reached");
