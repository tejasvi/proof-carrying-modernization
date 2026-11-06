// Two implementations of the same function; the proof shows they are interchangeable.
export function sumLoop(xs: number[]): number {
  let s = 0;
  for (const x of xs) {
    s = s + x;
  }
  return s;
}

export function sumReduce(xs: number[]): number {
  return xs.reduce((acc, x) => acc + x, 0);
}

console.log(String(sumLoop([1, 2, 3.5])));
console.log(String(sumReduce([1, 2, 3.5])));
