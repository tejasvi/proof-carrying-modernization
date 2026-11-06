// Interface fixture (old version): one function per verdict of strictts-diff.
export function label(score: number): string {
  let l: string;
  if (score >= 90) {
    l = "A";
  } else if (score >= 75) {
    l = "B";
  } else {
    l = "C";
  }
  return l;
}

export function magnitude(x: number): number {
  return x < 0 ? -x : x;
}

// loose equality is outside the StrictTS subset, so the counterexample (x = 0) is checked in
// Node only
export function limitOf(x: number | undefined): number {
  return x == undefined || x == 0 ? 10 : x;
}

// the push loop allocates the result like `map` does: proved for allocated argument arrays
export function total(xs: number[]): number[] {
  const out: number[] = [];
  for (const x of xs) {
    out.push(x * 2);
  }
  return out;
}

// unchanged helper (recursion: outside the reach of the automatic proofs)
function negFrom(xs: number[], i: number): boolean {
  return i < xs.length && (xs[i] < 0 || negFrom(xs, i + 1));
}

export function anyNegative(xs: number[]): boolean {
  return negFrom(xs, 0);
}

export function matches(re: RegExp, s: string): boolean {
  return re.test(s);
}

export function legacy(n: number): number {
  return n + 1;
}
