export function indexOfLong(words: string[], n: number): number {
  return words.findIndex((w) => w.length > n);
}
