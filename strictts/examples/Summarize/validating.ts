// Functions that validate their arguments before a loop. `ts_auto` splits on the validation
// test before summarizing: in one case the function throws, in the other the loop runs.

export function maxOf(xs: number[]): number {
  if (xs.length === 0) {
    throw new Error("maxOf: empty array");
  }
  let m = -Infinity;
  for (const x of xs) {
    if (x > m) {
      m = x;
    }
  }
  return m;
}

export function mean(xs: number[]): number {
  if (xs.length === 0) {
    throw new Error("mean: empty array");
  }
  let s = 0;
  for (const x of xs) {
    s += x;
  }
  return s / xs.length;
}

export function sumScaled(xs: number[], factor: number): number {
  if (factor < 0) {
    throw new RangeError("sumScaled: negative factor");
  }
  let s = 0;
  for (const x of xs) {
    s += x * factor;
  }
  return s;
}

export function sumNonNegative(xs: number[]): number {
  if (xs.some((x) => x < 0)) {
    throw new RangeError("sumNonNegative: negative input");
  }
  let s = 0;
  for (const x of xs) {
    s += x;
  }
  return s;
}

export function firstAbove(xs: number[], threshold: number): number | undefined {
  if (Number.isNaN(threshold)) {
    throw new Error("firstAbove: threshold is NaN");
  }
  for (const x of xs) {
    if (x > threshold) {
      return x;
    }
  }
  return undefined;
}

export function countBetween(xs: number[], lo: number, hi: number): number {
  if (lo > hi) {
    throw new RangeError("countBetween: empty range");
  }
  if (xs.length === 0) {
    return 0;
  }
  let n = 0;
  for (const x of xs) {
    if (lo <= x && x <= hi) {
      n++;
    }
  }
  return n;
}

// straight-line code after the validation: the read `xs[0]` is in bounds in the remaining case
export function firstOrThrow(xs: number[]): number {
  if (xs.length === 0) {
    throw new Error("firstOrThrow: empty array");
  }
  return xs[0];
}

// an early return on the empty array, then the last element: `xs.length - 1` is an index
export function lastOr(xs: number[], d: number): number {
  if (xs.length === 0) {
    return d;
  }
  return xs[xs.length - 1];
}

export function sqrtChecked(x: number): number {
  if (x < 0) {
    throw new RangeError("sqrtChecked: negative input");
  }
  return Math.sqrt(x);
}

function safeMax(xs: number[]): number {
  try {
    return maxOf(xs);
  } catch (e) {
    return NaN;
  }
}

console.log(`${maxOf([3, 1, 4])} ${mean([1, 2, 3])} ${sumScaled([1, 2], 3)} ${sumNonNegative([1, 2])}`);
console.log(`${firstAbove([1, 5, 7], 4)} ${countBetween([1, 5, 7], 2, 7)} ${safeMax([])}`);
console.log(`${firstOrThrow([2, 1])} ${sqrtChecked(9)} ${lastOr([1, 2], 0)} ${lastOr([], 7)}`);
