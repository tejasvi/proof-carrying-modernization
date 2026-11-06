export function average(xs: number[]): number {
  let t = 0;
  let c = 0;
  for (const v of xs) {
    t += v;
    c += 1;
  }
  return c === 0 ? 0 : t / c;
}
