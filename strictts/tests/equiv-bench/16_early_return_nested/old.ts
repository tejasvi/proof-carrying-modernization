export function shipping(total: number, member: boolean): number {
  if (member) {
    if (total > 50) {
      return 0;
    } else {
      return 2;
    }
  } else {
    if (total > 100) {
      return 0;
    } else {
      return 5;
    }
  }
}
