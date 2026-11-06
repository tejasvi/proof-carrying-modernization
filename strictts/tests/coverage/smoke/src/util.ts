// Smoke project for `--coverage --emit-lean` (tests/difftest/run.js): covered functions, a
// blocked one, a covered caller of the blocked one (left out), a module-level arrow, a class.
export const SCALE = 3;
export const scaled = (x: number): number => x * SCALE;
export function sumTo(n: number): number {
  let s = 0;
  for (let i = 1; i <= n; i++) s += scaled(i);
  return s;
}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export function loose(x: any): number { return x.length + 1; }
export function usesLoose(xs: string[]): number { return loose(xs) + 1; }
