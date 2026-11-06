// Number-theory loops whose termination ts_auto has no argument for (bounds that are not an array
// length, while loops, `while (true)` with a return). For "never panics" (and "never panics or
// throws") no termination argument is needed: no iteration panics, from any state.

export function smallestFactor(n: number): number {
  if (n < 2) {
    throw new RangeError("smallestFactor: n < 2");
  }
  for (let d = 2; d * d <= n; d++) {
    if (n % d === 0) {
      return d;
    }
  }
  return n;
}

export function divisorSum(n: number): number {
  let total = 0;
  for (let d = 1; d <= n / 2; d++) {
    if (n % d === 0) {
      total += d;
    }
  }
  return total;
}

export function gcd(a: number, b: number): number {
  if (a < 0 || b < 0) {
    throw new RangeError("gcd: negative argument");
  }
  while (b !== 0) {
    const r = a % b;
    a = b;
    b = r;
  }
  return a;
}

export function oddFactorial(n: number): number {
  let p = 1;
  for (let k = n; k > 0; k -= 2) {
    p *= k;
  }
  return p;
}

export function heronSqrt(x: number, eps: number): number {
  if (x < 0) {
    throw new RangeError("heronSqrt: negative argument");
  }
  let r = x;
  while (true) {
    const next = (r + x / r) / 2;
    if (Math.abs(next - r) < eps) {
      return next;
    }
    r = next;
  }
}

// the loop fills a Set allocated before it: one heap cell changes
export function divisorSet(n: number): Set<number> {
  if (n <= 0) {
    throw new RangeError("divisorSet: n <= 0");
  }
  const ds = new Set<number>();
  for (let d = 1; d * d <= n; d++) {
    if (n % d === 0) {
      ds.add(d);
      ds.add(n / d);
    }
  }
  return ds;
}

// a counter that must stay a valid index: `a[i]` and `b[i]` read in bounds because `i` stays a
// natural number below `a.length`, which the validation made equal to `b.length`
export function hamming(a: string, b: string): number {
  if (a.length !== b.length) {
    throw new RangeError("hamming: lengths differ");
  }
  let d = 0;
  for (let i = 0; i < a.length; i++) {
    if (a[i] !== b[i]) {
      d++;
    }
  }
  return d;
}

console.log(`${divisorSet(12).size} ${hamming("karolin", "kathrin")}`);
console.log(`${smallestFactor(91)} ${divisorSum(28)} ${gcd(84, 36)} ${oddFactorial(7)} ${heronSqrt(2, 1e-9)}`);
