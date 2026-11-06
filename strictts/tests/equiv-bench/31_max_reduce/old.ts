export function maxOf(xs: number[]): number {
  let m = -Infinity;
  for (const x of xs) {
    m = Math.max(m, x);
  }
  return m;
}
