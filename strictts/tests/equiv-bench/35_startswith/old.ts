export function hasPrefix(s: string, p: string): boolean {
  return s.slice(0, p.length) === p;
}
