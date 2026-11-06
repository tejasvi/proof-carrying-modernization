export function summary(name: string, items: number[]): string {
  const upper = name.trim();
  const count = items.length;
  const first = count > 0 ? items[0] : 0;
  return `${upper}:${count}:${first}`;
}
