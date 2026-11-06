// The RangeError of `new Int16Array(n)` for a length that is not an index names the length as
// ToString does (V8's message): ±Infinity, a negative or fractional number, a number above
// 2^53 - 1. (NaN and -0.5 are length 0.)
function make(n: number): string {
  try { return `ok ${new Int16Array(n).length}`; } catch (e) { return `${(e as Error).name}: ${(e as Error).message}`; }
}
for (const n of [Infinity, -Infinity, -1, -1.5, 1e300, 2 ** 53, NaN, -0.5, 3]) console.log(make(n));
