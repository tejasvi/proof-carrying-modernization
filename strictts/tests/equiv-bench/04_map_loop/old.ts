export function doubled(xs: number[]): number[] {
  const out: number[] = [];
  for (const x of xs) {
    out.push(x * 2);
  }
  return out;
}
