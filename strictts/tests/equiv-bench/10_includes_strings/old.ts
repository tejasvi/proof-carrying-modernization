export function hasTag(tags: string[], tag: string): boolean {
  let found = false;
  for (const t of tags) {
    if (t === tag) {
      found = true;
    }
  }
  return found;
}
