// Counted loops that read a second array at the counter: the bound is the first array's
// length; a hypothesis says the second array is at least as long.
export function dot(xs: number[], ys: number[]): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) {
    s = s + xs[i] * ys[i];
  }
  return s;
}

export function countDiff(xs: number[], ys: number[]): number {
  let n = 0;
  for (let i = 0; i < xs.length; i++) {
    if (xs[i] !== ys[i]) n++;
  }
  return n;
}
