export function firstNegative(xs: number[]): number {
  let found = 0;
  for (const x of xs) {
    if (x < 0) {
      found = x;
      break;
    }
  }
  return found;
}

export function hasNegative(xs: number[]): boolean {
  let any = false;
  for (const x of xs) {
    if (x < 0) {
      any = true;
      break;
    }
  }
  return any;
}

export function takeUntilZero(xs: number[]): number[] {
  const out: number[] = [];
  for (const x of xs) {
    if (x === 0) {
      break;
    }
    out.push(x);
  }
  return out;
}

console.log(`${firstNegative([1, -2, -3])} ${hasNegative([1, 2])} ${takeUntilZero([1, 2, 0, 3]).length}`);
