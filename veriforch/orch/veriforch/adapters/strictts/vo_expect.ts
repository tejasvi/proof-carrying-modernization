// verif-orchestrator: the vitest matchers used by generated test functions (extract_tests.js), written in the
// StrictTS subset. A failed check throws, so a test function returns normally exactly when every expectation
// of the test case holds.

/** Throws when an expectation fails. */
export function vo_check(pass: boolean): void {
  if (!pass) {
    throw new Error('expectation failed');
  }
}

/** Object.is on numbers (vitest toBe/toEqual): NaN equals NaN, and 0 differs from -0. */
export function vo_is_num(a: number, b: number): boolean {
  if (Number.isNaN(a)) {
    return Number.isNaN(b);
  }
  if (a === 0 && b === 0) {
    return 1 / a === 1 / b;
  }
  return a === b;
}

/** toEqual on number arrays: same length and Object.is elementwise. */
export function vo_eq_num_arr(a: number[], b: number[]): boolean {
  if (a.length !== b.length) {
    return false;
  }
  for (let i = 0; i < a.length; i++) {
    if (!vo_is_num(a[i], b[i])) {
      return false;
    }
  }
  return true;
}

/** toBeCloseTo(expected, precision): equal infinities pass; otherwise |expected - received| < 10^-precision / 2.
 * vitest computes `10 ** -precision` with the engine's pow, which ECMAScript leaves implementation-approximated
 * (StrictTS: `Impl.pow`); the check uses the correctly rounded value instead, 1 / 10^precision with the power of
 * ten computed exactly (exact up to 10^22), so the theorem does not depend on the engine's pow. */
export function vo_close(received: number, expected: number, precision: number): boolean {
  if (received === Number.POSITIVE_INFINITY && expected === Number.POSITIVE_INFINITY) {
    return true;
  }
  if (received === Number.NEGATIVE_INFINITY && expected === Number.NEGATIVE_INFINITY) {
    return true;
  }
  let scale = 1;
  let k = precision < 0 ? -precision : precision;
  while (k > 0) {
    scale = scale * 10;
    k = k - 1;
  }
  const tolerance = precision < 0 ? scale / 2 : 1 / scale / 2;
  return Math.abs(expected - received) < tolerance;
}
