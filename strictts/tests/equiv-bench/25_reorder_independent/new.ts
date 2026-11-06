export function summary(name: string, items: number[]): string {
  const count = items.length;
  const first = count > 0 ? items[0] : 0;
  const upper = name.trim();
  return `${upper}:${count}:${first}`;
}
