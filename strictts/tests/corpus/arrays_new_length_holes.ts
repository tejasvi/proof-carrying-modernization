// @panic non-null assertion on undefined
// An array from `new Array(n)` used before all n elements were written: its holes would be
// observable (Node prints 3, the length of an array holding one element), so the model stops
// there.
function partial(n: number): number[] {
  const a = new Array<number>(n);
  a[0] = 1;
  return a;
}
console.log(partial(1).join(","));
console.log(`${partial(3).length}`);
