export function charCount(s: string): number {
  let n = 0;
  for (const _c of s) n++;
  return n;
}
