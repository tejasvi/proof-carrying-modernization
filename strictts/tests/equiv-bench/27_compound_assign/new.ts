export function countSpaces(s: string): number {
  let n = 0;
  for (let i = 0; i < s.length; i++) {
    if (s.charAt(i) === " ") n += 1;
  }
  return n;
}
