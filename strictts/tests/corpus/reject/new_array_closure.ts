// @reject unsupported-builtin
// `new Array(n)` whose array is used in a nested function: its holes could be observed there.
function f(n: number): number[] {
  const a = new Array<number>(n);
  const put = (i: number) => { a[i] = i; };
  for (let i = 0; i < n; i++) put(i);
  return a;
}
console.log(f(2).join(","));
