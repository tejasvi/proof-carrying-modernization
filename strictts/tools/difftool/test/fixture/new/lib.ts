// Interface fixture (new version): one function per verdict of strictts-diff.
export function label(score: number): string {
  return score >= 90 ? "A" : score >= 75 ? "B" : "C";
}

export function magnitude(x: number): number {
  return Math.abs(x);
}

export function limitOf(x: number | undefined): number {
  return x ?? 10;
}

export function total(xs: number[]): number[] {
  return xs.map((x) => x * 2);
}

// unchanged helper (recursion: outside the reach of the automatic proofs)
function negFrom(xs: number[], i: number): boolean {
  return i < xs.length && (xs[i] < 0 || negFrom(xs, i + 1));
}

export function anyNegative(xs: number[]): boolean {
  return xs.some((x) => x < 0);
}

export function matches(re: RegExp, s: string): boolean {
  return s.search(re) >= 0;
}

export function extra(n: number): number {
  return n * 2;
}
