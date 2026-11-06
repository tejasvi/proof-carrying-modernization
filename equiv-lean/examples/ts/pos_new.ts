// Fresh-allocation demo (equiv-lean, StrictTS bridge): AFTER, one loop pushing into a
// fresh array (one allocation).
export function doublePositives(xs: number[]): number[] {
  const out: number[] = [];
  for (const x of xs) {
    if (x > 0) {
      out.push(2 * x);
    }
  }
  return out;
}

console.log(doublePositives([1, -2, 3]).join(","));
