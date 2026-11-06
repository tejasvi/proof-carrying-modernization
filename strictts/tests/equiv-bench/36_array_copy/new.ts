export function sortedCopy(xs: number[]): number[] {
  return xs.concat([]).sort((a, b) => a - b);
}
