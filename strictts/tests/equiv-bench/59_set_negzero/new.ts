export function distinct(xs: number[]): number[] {
  const out: number[] = [];
  for (const x of xs) {
    if (!out.includes(x)) out.push(x);
  }
  return out;
}
