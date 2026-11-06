// Recursion, bigint arithmetic, conditional expressions.
function fact(n: bigint): bigint {
  return n <= 0n ? 1n : n * fact(n - 1n);
}
function fib(n: bigint): bigint {
  if (n < 2n) return n;
  return fib(n - 1n) + fib(n - 2n);
}
function gcd(a: bigint, b: bigint): bigint {
  while (b !== 0n) {
    const t = a % b;
    a = b;
    b = t;
  }
  return a;
}
console.log(`fact(25) = ${fact(25n)}`);
console.log(`fib(15) = ${fib(15n)}`);
console.log(`gcd(1071, 462) = ${gcd(1071n, 462n)}`);
console.log(`2^100 = ${2n ** 100n}`);
