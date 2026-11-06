export function intersection<T>(firstArr: readonly T[], secondArr: readonly T[]): T[] {
  const secondSet = new Set(secondArr);

  return firstArr.filter(item => {
    return secondSet.has(item);
  });
}
