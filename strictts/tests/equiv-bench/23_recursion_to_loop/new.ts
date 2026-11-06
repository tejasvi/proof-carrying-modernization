export function factorial(n: number): number {
  if (!Number.isInteger(n) || n < 0 || n > 20) return -1;
  let r = 1;
  for (let i = n; i > 1; i--) r = r * i;
  return r;
}
