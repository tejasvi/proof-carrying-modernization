export function sumSquares(xs: number[]): number {
  let s = 0;
  for (const x of xs) {
    s += x * x;
  }
  return s;
}
