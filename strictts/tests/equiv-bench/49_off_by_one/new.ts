export function sumAll(xs: number[]): number {
  let s = 0;
  for (let i = 0; i < xs.length - 1; i++) s += xs[i];
  return s;
}
