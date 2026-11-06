// PR diff demo (equiv-lean, StrictTS bridge): the module AFTER the change.
// for…of loops; `contains` sets a flag and leaves the loop with `break`.
export function sum(xs: number[]): number {
  let s = 0;
  for (const x of xs) {
    s = s + x;
  }
  return s;
}

export function contains(xs: number[], v: number): boolean {
  let found = false;
  for (const x of xs) {
    if (x === v) {
      found = true;
      break;
    }
  }
  return found;
}

console.log(String(sum([1, 2, 3.5])));
console.log(String(contains([1, 2, 3], 2)));
