export function vowelCount(s: string): number {
  let n = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charAt(i);
    if (c === "a" || c === "e" || c === "i" || c === "o" || c === "u") n++;
  }
  return n;
}
