export function half(x: number): number {
  if (!Number.isInteger(x) || x < 0 || x > 2147483647) return -1;
  return x >> 1;
}
