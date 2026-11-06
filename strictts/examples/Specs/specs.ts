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
