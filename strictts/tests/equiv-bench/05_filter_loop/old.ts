export function positives(xs: number[]): number[] {
  const out: number[] = [];
  for (let i = 0; i < xs.length; i++) {
    if (xs[i] > 0) {
      out.push(xs[i]);
    }
  }
  return out;
}
