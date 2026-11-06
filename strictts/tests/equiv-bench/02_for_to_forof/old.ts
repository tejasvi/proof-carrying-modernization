export function sumSquares(xs: number[]): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) {
    s += xs[i] * xs[i];
  }
  return s;
}
