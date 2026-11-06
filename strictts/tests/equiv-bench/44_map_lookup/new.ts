export function weight(size: string): number {
  const table = new Map<string, number>([["s", 1], ["m", 2], ["l", 4]]);
  return table.get(size) ?? 0;
}
