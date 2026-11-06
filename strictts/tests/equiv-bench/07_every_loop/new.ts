export function allShort(words: string[], max: number): boolean {
  return words.every((w) => w.length <= max);
}
