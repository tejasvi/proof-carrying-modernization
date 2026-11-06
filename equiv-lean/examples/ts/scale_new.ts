// Fresh-allocation demo (equiv-lean, StrictTS bridge): AFTER, the maps fused
// (one allocation; the result lives at a different address).
export function scale(xs: number[]): number[] {
  return xs.map((x) => 2 * (x + 1));
}

console.log(scale([1, 2, 3]).join(","));
