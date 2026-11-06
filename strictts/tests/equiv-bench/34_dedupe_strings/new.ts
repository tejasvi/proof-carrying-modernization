export function unique(xs: string[]): string[] {
  const out: string[] = [];
  for (const x of xs) {
    if (!out.includes(x)) out.push(x);
  }
  return out;
}
