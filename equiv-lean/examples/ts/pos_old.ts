// Fresh-allocation demo (equiv-lean, StrictTS bridge): BEFORE, filter + map
// (two allocations: the filtered array, then the result).
export function doublePositives(xs: number[]): number[] {
  return xs.filter((x) => x > 0).map((x) => 2 * x);
}

console.log(doublePositives([1, -2, 3]).join(","));
