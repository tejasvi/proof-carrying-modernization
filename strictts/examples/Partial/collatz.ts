// The Collatz iteration. Whether this loop ends for every positive integer is an open problem
// (the Collatz conjecture), so no proof of termination is known.
export function collatz(n: number): number {
  let steps = 0;
  while (n !== 1) {
    n = n % 2 === 0 ? n / 2 : 3 * n + 1;
    steps = steps + 1;
  }
  return steps;
}

console.log(String(collatz(27)));
