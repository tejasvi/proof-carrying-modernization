// PR diff demo (equiv-lean, StrictTS bridge): AFTER, while (true) with a break.
export function digits(n: number): number {
  let count = 0;
  let m = n;
  while (true) {
    count++;
    m = Math.floor(m / 10);
    if (!(m > 0)) {
      break;
    }
  }
  return count;
}

console.log(String(digits(12345)));
