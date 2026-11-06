export function intersection<T>(firstArr: readonly T[], secondArr: readonly T[]): T[] {
  return firstArr.filter(item => {
    return secondArr.includes(item);
  });
}
