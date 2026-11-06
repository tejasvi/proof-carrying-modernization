/**
 * Doubles every element, into a fresh array.
 * @ensures result !== xs
 */
export function doubleAll(xs: number[]): number[] {
  return xs.map((x) => x * 2);
}

/**
 * The same map: the result has as many elements as the argument.
 * @ensures result.length === xs.length
 */
export function doubleAllLen(xs: number[]): number[] {
  return xs.map((x) => x * 2);
}

/**
 * Clamps `x` into `[lo, hi]`.
 * @requires lo <= hi
 * @ensures lo <= result && result <= hi
 */
export function clamp(x: number, lo: number, hi: number): number {
  if (x < lo) {
    return lo;
  }
  if (x > hi) {
    return hi;
  }
  return x;
}

/**
 * The same, with the precondition that `x` is a number (not NaN).
 * @requires lo <= hi && x === x
 * @ensures lo <= result && result <= hi
 */
export function clampChecked(x: number, lo: number, hi: number): number {
  if (x < lo) {
    return lo;
  }
  if (x > hi) {
    return hi;
  }
  return x;
}

console.log(`${doubleAll([1, 2]).length} ${clamp(5, 0, 3)} ${clampChecked(-1, 0, 3)}`);

// ---- specifications (generated from JSDoc by tools/jsdoc_specs.js) ----
function doubleAll__requires(xs: number[]): boolean {
  return true;
}
function doubleAll__ensures(result: number[], xs: number[]): boolean {
  return (result !== xs);
}
function doubleAllLen__requires(xs: number[]): boolean {
  return true;
}
function doubleAllLen__ensures(result: number[], xs: number[]): boolean {
  return (result.length === xs.length);
}
function clamp__requires(x: number, lo: number, hi: number): boolean {
  return (lo <= hi);
}
function clamp__ensures(result: number, x: number, lo: number, hi: number): boolean {
  return (lo <= result && result <= hi);
}
function clampChecked__requires(x: number, lo: number, hi: number): boolean {
  return (lo <= hi && x === x);
}
function clampChecked__ensures(result: number, x: number, lo: number, hi: number): boolean {
  return (lo <= result && result <= hi);
}
