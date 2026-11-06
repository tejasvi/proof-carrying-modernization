export function sortedCopy(xs: number[]): number[] {
  const c = xs.slice();
  c.sort((a, b) => a - b);
  return c;
}
