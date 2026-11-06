export function halfIndex(x: number): number {
  const y = x | 0;
  if (y < 0) return -1;
  return Math.floor(y / 2);
}
