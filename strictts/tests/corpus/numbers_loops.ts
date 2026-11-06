// @numbers
// Number loops: index-based array loops, fibonacci, primes, averages.
function fib(n: number): number {
  let a = 0, b = 1;
  for (let i = 0; i < n; i++) { const t = a + b; a = b; b = t; }
  return a;
}
console.log(`${fib(10)} ${fib(50)} ${fib(80)}`);
function primes(limit: number): number[] {
  const sieve: boolean[] = new Array<boolean>(limit + 1).fill(true);
  const out: number[] = [];
  for (let i = 2; i <= limit; i++) {
    if (!sieve[i]) continue;
    out.push(i);
    for (let j = i * i; j <= limit; j += i) sieve[j] = false;
  }
  return out;
}
console.log(primes(50).join(" "));
const data = [3, 1, 4, 1, 5, 9, 2, 6];
let sum = 0;
for (let i = 0; i < data.length; i++) sum += data[i];
console.log(`sum ${sum} avg ${sum / data.length}`);
const sorted = [...data].sort((p, q) => p - q);
console.log(sorted.join(","));
console.log(`${data.indexOf(1)} ${data.lastIndexOf(1)}`);
const matrix: number[][] = [];
for (let r = 0; r < 3; r++) {
  const row: number[] = [];
  for (let c = 0; c < 3; c++) row.push(r * 3 + c);
  matrix.push(row);
}
console.log(matrix.map((row) => row.join(" ")).join(" / "));
let k = 10;
while (k > 0) k -= 3;
console.log(`k=${k}`);
