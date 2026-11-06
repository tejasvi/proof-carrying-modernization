// Counted loops (`for (let i = 0; i < xs.length; i++)`) next to their for…of and
// array-method versions.
export function sumIdx(xs: number[]): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) {
    s = s + xs[i];
  }
  return s;
}

export function sumOf(xs: number[]): number {
  let s = 0;
  for (const x of xs) {
    s = s + x;
  }
  return s;
}

export function sumReduce(xs: number[]): number {
  return xs.reduce((acc, x) => acc + x, 0);
}

export function doubleIdx(xs: number[]): number[] {
  const out: number[] = [];
  for (let i = 0; i < xs.length; i++) {
    out.push(xs[i] * 2);
  }
  return out;
}

export function doubleMap(xs: number[]): number[] {
  return xs.map((x) => x * 2);
}

export function sumBelow10(): number {
  let s = 0;
  for (let i = 0; i < 10; i++) {
    s = s + i;
  }
  return s;
}

export function square(x: number): number {
  return x * x;
}

export function sumSquares(xs: number[]): number {
  let s = 0;
  for (const x of xs) {
    s = s + square(x);
  }
  return s;
}

export function sumSquaresIdx(xs: number[]): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) {
    s = s + square(xs[i]);
  }
  return s;
}

export function sumSquaresReduce(xs: number[]): number {
  return xs.reduce((acc, x) => acc + square(x), 0);
}

console.log(`${sumIdx([1, 2, 3])} ${sumOf([1, 2, 3])} ${sumReduce([1, 2, 3])}`);
console.log(`${doubleIdx([1, 2]).length} ${doubleMap([1, 2]).length}`);
console.log(`${sumBelow10()}`);
console.log(`${sumSquares([1, 2])} ${sumSquaresIdx([1, 2])}`);
console.log(`${sumSquaresReduce([1, 2])}`);
