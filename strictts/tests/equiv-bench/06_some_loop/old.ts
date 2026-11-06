export function anyNegative(xs: number[]): boolean {
  for (const x of xs) {
    if (x < 0) {
      return true;
    }
  }
  return false;
}
