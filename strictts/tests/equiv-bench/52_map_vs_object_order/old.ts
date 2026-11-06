export function firstSeen(words: string[]): string[] {
  const m = new Map<string, boolean>();
  for (const w of words) m.set(w, true);
  return Array.from(m.keys());
}
