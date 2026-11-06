// A table-driven hash over a number array (the shape of CRC-32): the loop state indexes the
// table after a mask.
export function tableHash(xs: number[], table: number[]): number {
  let h = 0;
  for (let i = 0; i < xs.length; i++) {
    h = (h >>> 8) ^ table[(h ^ xs[i]) & 0xFF];
  }
  return h;
}
