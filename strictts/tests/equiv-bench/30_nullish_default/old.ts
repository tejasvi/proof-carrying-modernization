export function pageSize(requested: number | undefined): number {
  const n = requested === undefined ? 20 : requested;
  return Math.min(n, 100);
}
