export function pageSize(requested: number | undefined): number {
  return Math.min(requested ?? 20, 100);
}
