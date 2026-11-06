// `<`, `<=`, `>`, `>=` with an operand of type any compare the runtime values as JavaScript does:
// two strings by code units, other primitives as numbers (a string converted when the other side
// is not a string; undefined NaN, null 0, booleans 0 and 1), an object through its string.
function lt(a: any, b: any): boolean { return a < b; }
function le(a: any, b: any): boolean { return a <= b; }
function gt(a: any, b: any): boolean { return a > b; }
function ge(a: any, b: any): boolean { return a >= b; }
const pairs: [any, any][] = [
  [1, 2], ["10", "9"], ["10", 9], [9, "10"], ["a", "b"], ["b", "a"], ["", ""], [null, 0], [null, 1],
  [undefined, 1], [undefined, undefined], [true, false], [true, 1], [NaN, 1], [1, NaN], [[2], 1],
  [[1, 2], "1,3"], [{}, {}], [-0, 0], ["", 0], [" 12 ", 12], ["x", 1], [null, undefined], [[], ""],
];
for (const [a, b] of pairs) {
  console.log(`${lt(a, b)} ${le(a, b)} ${gt(a, b)} ${ge(a, b)}`);
}
// lodash's max: a number against a value of type any
function maxOf(xs: readonly number[]): number | undefined {
  let m: any = undefined;
  for (const x of xs) {
    if (m == null || x > m) {
      m = x;
    }
  }
  return m;
}
console.log(`${maxOf([3, 9, -1])} ${maxOf([])} ${maxOf([NaN, 2])}`);
