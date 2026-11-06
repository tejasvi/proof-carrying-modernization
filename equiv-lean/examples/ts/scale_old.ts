// Fresh-allocation demo (equiv-lean, StrictTS bridge): BEFORE, two chained maps
// (allocates an intermediate array; the result is the second allocation).
export function scale(xs: number[]): number[] {
  return xs.map((x) => x + 1).map((x) => 2 * x);
}

console.log(scale([1, 2, 3]).join(","));
