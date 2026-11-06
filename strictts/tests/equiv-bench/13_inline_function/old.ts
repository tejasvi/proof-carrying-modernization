function isVowel(c: string): boolean {
  return c === "a" || c === "e" || c === "i" || c === "o" || c === "u";
}
export function vowelCount(s: string): number {
  let n = 0;
  for (let i = 0; i < s.length; i++) {
    if (isVowel(s.charAt(i))) n++;
  }
  return n;
}
