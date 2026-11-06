export function difference<T>(firstArr: T[], secondArr: T[]): T[] {
  const secondSet = new Set(secondArr);

  return firstArr.filter(item => !secondSet.has(item));
}
