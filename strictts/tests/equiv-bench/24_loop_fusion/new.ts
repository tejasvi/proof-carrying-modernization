export function stats(xs: number[]): string {
  let sum = 0;
  let big = 0;
  for (const x of xs) {
    sum += x;
    if (x > 10) big++;
  }
  return `${sum}/${big}`;
}
