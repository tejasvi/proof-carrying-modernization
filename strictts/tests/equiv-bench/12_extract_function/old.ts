export function describe(celsius: number): string {
  const f = celsius * 9 / 5 + 32;
  if (f > 90) {
    return "hot " + String(f);
  }
  return "ok " + String(f);
}
