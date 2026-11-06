export function firstSeen(words: string[]): string[] {
  const o: Record<string, boolean> = {};
  for (const w of words) o[w] = true;
  return Object.keys(o);
}
