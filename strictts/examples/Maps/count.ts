// Word counting with a Map: each key ends up mapped to its number of occurrences.
export function countWords(words: string[]): Map<string, number> {
  const counts = new Map<string, number>();
  for (const w of words) {
    counts.set(w, (counts.get(w) ?? 0) + 1);
  }
  return counts;
}

const c = countWords(["a", "b", "a"]);
console.log(String(c.get("a") ?? 0));
