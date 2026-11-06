export async function scaled(n: number, k: number): Promise<number> {
  const m = n * k;
  return m + 1;
}
