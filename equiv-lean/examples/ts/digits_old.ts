// PR diff demo (equiv-lean, StrictTS bridge): BEFORE, a do…while loop.
export function digits(n: number): number {
  let count = 0;
  let m = n;
  do {
    count++;
    m = Math.floor(m / 10);
  } while (m > 0);
  return count;
}

console.log(String(digits(12345)));
