function fact(n: number): number {
  return n <= 1 ? 1 : n * fact(n - 1);
}
export function factorial(n: number): number {
  if (!Number.isInteger(n) || n < 0 || n > 20) return -1;
  return fact(n);
}
