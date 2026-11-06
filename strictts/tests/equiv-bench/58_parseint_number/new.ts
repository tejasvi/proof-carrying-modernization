export function qty(s: string): number {
  const n = Number(s);
  return Number.isNaN(n) ? 0 : n;
}
