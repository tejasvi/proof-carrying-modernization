export function indexOfLong(words: string[], n: number): number {
  for (let i = 0; i < words.length; i++) {
    if (words[i].length > n) {
      return i;
    }
  }
  return -1;
}
