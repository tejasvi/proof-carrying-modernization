export function maxOf(xs: number[]): number {
  return xs.reduce((a, b) => Math.max(a, b), -Infinity);
}
