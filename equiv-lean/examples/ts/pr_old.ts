// PR diff demo (equiv-lean, StrictTS bridge): the module BEFORE the change.
// Index loops; `contains` leaves the loop with an early `return`.
export function sum(xs: number[]): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) {
    s = s + xs[i];
  }
  return s;
}

export function contains(xs: number[], v: number): boolean {
  for (let i = 0; i < xs.length; i++) {
    if (xs[i] === v) {
      return true;
    }
  }
  return false;
}

console.log(String(sum([1, 2, 3.5])));
console.log(String(contains([1, 2, 3], 2)));
