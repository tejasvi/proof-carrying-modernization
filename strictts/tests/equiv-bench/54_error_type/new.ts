export function parseAge(s: string): number {
  const n = Number(s);
  if (!Number.isInteger(n) || n < 0) throw new TypeError(`bad age: ${s}`);
  return n;
}
