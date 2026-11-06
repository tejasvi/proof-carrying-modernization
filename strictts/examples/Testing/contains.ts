// A tempting refactoring that is NOT equivalent: includes uses SameValueZero, indexOf uses ===.
export function hasIndexOf(xs: number[], x: number): boolean {
  return xs.indexOf(x) !== -1;
}
export function hasIncludes(xs: number[], x: number): boolean {
  return xs.includes(x);
}
// Looks equivalent but is not: for x = -0, `x < 0` is false, so absA returns -0 while Math.abs returns +0.
export function absA(x: number): number {
  return x < 0 ? -x : x;
}
export function absB(x: number): number {
  return Math.abs(x);
}
