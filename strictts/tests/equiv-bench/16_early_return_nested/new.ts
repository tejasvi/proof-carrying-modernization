export function shipping(total: number, member: boolean): number {
  if (member && total > 50) return 0;
  if (member) return 2;
  if (total > 100) return 0;
  return 5;
}
