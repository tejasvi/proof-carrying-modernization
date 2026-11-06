// Nested function declarations: hoisting, recursion, captured variables (lambda lifting).
function outer(n: bigint): string {
  const prefix = `n${n}`;
  let calls = 0n;
  const early = describe(n);
  function describe(k: bigint): string {
    calls++;
    return k <= 0n ? prefix : `${k}:${describe(k - 1n)}`;
  }
  function twice(k: bigint): string { return describe(k) + "|" + describe(k); }
  return `${early} / ${twice(1n)} / calls=${calls}`;
}
console.log(outer(2n));
function evenOdd(n: bigint): string {
  function isEven(k: bigint): boolean { return k === 0n ? true : isOdd(k - 1n); }
  function isOdd(k: bigint): boolean { return k === 0n ? false : isEven(k - 1n); }
  return `${n} even=${isEven(n)} odd=${isOdd(n)}`;
}
console.log(evenOdd(7n));
function makeGreeter(greeting: string): (name: string) => string {
  function greet(name: string): string { return `${greeting}, ${name}`; }
  return greet;
}
console.log(makeGreeter("Hello")("world"));
