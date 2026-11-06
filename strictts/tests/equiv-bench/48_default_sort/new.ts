export function ordered(xs: number[]): number[] {
  return xs.slice().sort((a, b) => a - b);
}
