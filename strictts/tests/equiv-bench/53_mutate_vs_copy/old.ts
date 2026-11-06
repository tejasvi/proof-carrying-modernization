export function median(xs: number[]): number {
  const s = xs.sort((a, b) => a - b);
  return s.length === 0 ? NaN : s[Math.floor(s.length / 2)];
}
