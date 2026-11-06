export function countSpaces(s: string): number {
  let n = 0;
  for (let i = 0; i < s.length; i = i + 1) {
    if (s.charAt(i) === " ") {
      n = n + 1;
    }
  }
  return n;
}
