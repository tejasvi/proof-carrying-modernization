// Synchronous calls of library functions that StrictTS does not model: regular expressions and
// `String.prototype.normalize` are external calls answered by the world's oracle. `ts_auto`
// splits on each answer that no hypothesis fixes (an error, or a value of each form).

export function isLowerWord(s: string): boolean {
  return /^[a-z]+$/.test(s);
}

export function checkedName(s: string): string {
  if (/^\s*$/.test(s)) {
    throw new Error("checkedName: blank name");
  }
  return s.trim();
}

export function nameLength(s: string): number {
  return s.normalize("NFC").length;
}

export function bothWords(a: string, b: string): boolean {
  return /^\w+$/.test(a) && /^\w+$/.test(b);
}

export function sumIfWord(xs: number[], s: string): number {
  if (!/^[a-z]+$/.test(s)) {
    return -1;
  }
  let t = 0;
  for (const x of xs) {
    t += x;
  }
  return t;
}

export function words(s: string): string[] {
  return s.split(/\s+/);
}

console.log(`${isLowerWord("abc")} ${checkedName(" Ann ")} ${nameLength("abc")} ${bothWords("a", "b")}`);
console.log(`${sumIfWord([1, 2], "ab")} ${words("a b c").length}`);
