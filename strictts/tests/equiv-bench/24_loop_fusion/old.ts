export function stats(xs: number[]): string {
  let sum = 0;
  for (const x of xs) sum += x;
  let big = 0;
  for (const x of xs) if (x > 10) big++;
  return `${sum}/${big}`;
}
