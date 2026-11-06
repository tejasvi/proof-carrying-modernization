// Recursive arrow functions bound to const.
function run(): void {
  const base = 3n;
  const pow3 = (k: bigint): bigint => (k === 0n ? 1n : base * pow3(k - 1n));
  console.log(`3^5 = ${pow3(5n)}`);
  const collatz = (n: bigint, steps: bigint): bigint =>
    n === 1n ? steps : collatz(n % 2n === 0n ? n / 2n : 3n * n + 1n, steps + 1n);
  console.log(`collatz(27) = ${collatz(27n, 0n)}`);
}
run();
const hanoi = (n: bigint, from: string, to: string, via: string, out: string[]): void => {
  if (n === 0n) return;
  hanoi(n - 1n, from, via, to, out);
  out.push(`${from}->${to}`);
  hanoi(n - 1n, via, to, from, out);
};
const moves: string[] = [];
hanoi(3n, "A", "C", "B", moves);
console.log(moves.join(" "));
