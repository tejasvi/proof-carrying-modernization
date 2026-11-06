export function parseAge(s: string): number {
  const n = Number(s);
  if (!Number.isInteger(n) || n < 0) throw new Error(`bad age: ${s}`);
  return n;
}
