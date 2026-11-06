export function counts(words: string[]): Map<string, number> {
  const m = new Map<string, number>();
  for (const w of words) {
    const c = m.get(w);
    if (c === undefined) {
      m.set(w, 1);
    } else {
      m.set(w, c + 1);
    }
  }
  return m;
}
