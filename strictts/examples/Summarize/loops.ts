export function maxOf(xs: number[]): number {
  let m = -Infinity;
  for (const x of xs) {
    if (x > m) {
      m = x;
    }
  }
  return m;
}

export function maxOfReduce(xs: number[]): number {
  return xs.reduce((m, x) => (x > m ? x : m), -Infinity);
}

export function range(xs: number[]): number {
  let lo = Infinity;
  let hi = -Infinity;
  for (const x of xs) {
    if (x < lo) {
      lo = x;
    }
    if (x > hi) {
      hi = x;
    }
  }
  return hi - lo;
}

export function countPositive(xs: number[]): number {
  let n = 0;
  for (const x of xs) {
    if (x <= 0) {
      continue;
    }
    n = n + 1;
  }
  return n;
}

export function joinWords(ws: string[]): string {
  let out = "";
  let first = true;
  for (const w of ws) {
    if (!first) {
      out = out + " ";
    }
    out = out + w;
    first = false;
  }
  return out;
}

export function positives(xs: number[]): number[] {
  const out: number[] = [];
  for (const x of xs) {
    if (x > 0) {
      out.push(x);
    }
  }
  return out;
}

export function positivesFilter(xs: number[]): number[] {
  return xs.filter((x) => x > 0);
}

export function hasNegative(xs: number[]): boolean {
  let found = false;
  for (const x of xs) {
    if (x < 0) {
      found = true;
    }
  }
  return found;
}

export function hasNegativeSome(xs: number[]): boolean {
  return xs.some((x) => x < 0);
}

export function allPositive(xs: number[]): boolean {
  let ok = true;
  for (const x of xs) {
    if (!(x > 0)) {
      ok = false;
    }
  }
  return ok;
}

export function allPositiveEvery(xs: number[]): boolean {
  return xs.every((x) => x > 0);
}

export function firstNegative(xs: number[]): number | undefined {
  return xs.find((x) => x < 0);
}

export function firstNegativeIndex(xs: number[]): number {
  return xs.findIndex((x) => x < 0);
}

export function lastNegative(xs: number[]): number | undefined {
  return xs.findLast((x) => x < 0);
}

export function lastNegativeIndex(xs: number[]): number {
  return xs.findLastIndex((x) => x < 0);
}

export function touchAll(xs: number[]): void {
  xs.forEach((x) => {
    const y = x + 1;
  });
}

export function sortAsc(xs: number[]): number[] {
  return xs.sort((a, b) => a - b);
}

console.log(`${maxOf([3, 1, 4, 1, 5])} ${maxOfReduce([3, 1, 4, 1, 5])} ${range([3, 1, 4])} ${countPositive([1, -2, 3])}`);
console.log(joinWords(["a", "b"]));
console.log(`${positives([1, -2, 3]).length}`);
console.log(`${positivesFilter([1, -2, 3]).length} ${hasNegative([1, -2])} ${hasNegativeSome([1, 2])}`);
console.log(`${allPositive([1, 2])} ${allPositiveEvery([1, -2])} ${firstNegative([1, -2, -3]) === undefined} ${firstNegativeIndex([1, -2, -3])}`);
console.log(`${lastNegative([1, -2, -3]) === undefined} ${lastNegativeIndex([1, -2, -3])}`);
touchAll([1, 2]);
console.log(`${sortAsc([3, 1, 2])[0]}`);
