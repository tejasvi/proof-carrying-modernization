export function difference<T>(firstArr: T[], secondArr: T[]): T[] {
  return firstArr.filter(item => {
    return !secondArr.includes(item);
  });
}
