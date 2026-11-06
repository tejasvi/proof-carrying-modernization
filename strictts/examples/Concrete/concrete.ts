// Test cases in the style of verif-orchestrator's es-toolkit unit tests: each `test…` function runs
// its expectations and throws when one fails, so "the test returns normally" says that they all hold.
// The theorems (ConcreteProofs.lean) are proved by running the code on the literals (`ts_eval`).

/** Throws when an expectation fails. */
export function check(pass: boolean): void {
  if (!pass) {
    throw new Error('expectation failed');
  }
}

/** Object.is on numbers: NaN equals NaN, 0 differs from -0. */
export function isNum(a: number, b: number): boolean {
  if (Number.isNaN(a)) {
    return Number.isNaN(b);
  }
  if (a === 0 && b === 0) {
    return 1 / a === 1 / b;
  }
  return a === b;
}

/** |expected - received| < 10^-precision / 2, with the power of ten computed by a loop. */
export function close(received: number, expected: number, precision: number): boolean {
  let scale = 1;
  let k = precision;
  while (k > 0) {
    scale = scale * 10;
    k = k - 1;
  }
  return Math.abs(expected - received) < 1 / scale / 2;
}

export function median(nums: readonly number[]): number {
  if (nums.length === 0) {
    return NaN;
  }
  const sorted = nums.slice().sort((a, b) => a - b);
  const middleIndex = Math.floor(sorted.length / 2);
  if (sorted.length % 2 === 0) {
    return (sorted[middleIndex - 1] + sorted[middleIndex]) / 2;
  } else {
    return sorted[middleIndex];
  }
}

export function lerp(start: number, stop: number, fraction: number): number {
  if (fraction === 1) {
    return stop;
  }
  return start + (stop - start) * fraction;
}

export function round(value: number, precision = 0): number {
  if (!Number.isInteger(precision)) {
    throw new Error('Precision must be an integer.');
  }
  const multiplier = Math.pow(10, precision);
  return Math.round(value * multiplier) / multiplier;
}

/** How many elements are even (a loop with `%`). */
export function countEven(xs: number[]): number {
  let c = 0;
  for (const x of xs) {
    if (x % 2 === 0) {
      c = c + 1;
    }
  }
  return c;
}

export function testMedianOdd(): void {
  check(isNum(median([5, 2, 1, 4, 3]), 3));
}

export function testMedianEven(): void {
  check(isNum(median([1, 2, 3, 4]), 2.5));
}

export function testMedianEmpty(): void {
  check(isNum(median([]), NaN));
}

export function testLerp(): void {
  check(isNum(lerp(0, 100, 0.5), 50));
  check(isNum(lerp(10, 20, 0.25), 12.5));
  check(isNum(lerp(0, 1, 0.75), 0.75));
  check(isNum(lerp(-10, 10, 0.5), 0));
}

export function testLerpOutside(): void {
  check(isNum(lerp(0, 100, 1.5), 150));
  check(isNum(lerp(0, 100, -0.5), -50));
  check(isNum(lerp(10, 20, 2), 30));
}

export function testCountEven(): void {
  const xs = [1, 2, 3, 4, 5, 6, 7];
  check(isNum(countEven(xs), 3));
  check(xs.length % 2 === 1);
}

export function testClose(): void {
  check(close(0.1 + 0.2, 0.3, 5));
  check(!close(0.1 + 0.2, 0.3, 20));
}

export function testRound(): void {
  check(isNum(round(1.5), 2));
  check(isNum(round(1.4), 1));
  check(isNum(round(-1.5), -1));
  check(isNum(round(0), 0));
}

export function testRoundPrecision(): void {
  check(isNum(round(1.2345, 2), 1.23));
  check(isNum(round(-1.2365, 2), -1.24));
}
