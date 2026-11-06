function toFahrenheit(c: number): number {
  return c * 9 / 5 + 32;
}
export function describe(celsius: number): string {
  const f = toFahrenheit(celsius);
  return (f > 90 ? "hot " : "ok ") + String(f);
}
