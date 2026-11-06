export function allShort(words: string[], max: number): boolean {
  for (const w of words) {
    if (!(w.length <= max)) {
      return false;
    }
  }
  return true;
}
