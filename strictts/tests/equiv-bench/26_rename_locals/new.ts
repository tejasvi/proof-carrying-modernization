export function average(values: number[]): number {
  let total = 0;
  let count = 0;
  for (const value of values) {
    total += value;
    count += 1;
  }
  return count === 0 ? 0 : total / count;
}
