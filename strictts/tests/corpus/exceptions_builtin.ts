// Exceptions thrown by library operations, caught by the program.
function safeDiv(a: bigint, b: bigint): string {
  try {
    return `${a / b}`;
  } catch (e) {
    if (e instanceof RangeError) return `RangeError: ${e.message}`;
    return "other";
  }
}
console.log(safeDiv(7n, 2n));
console.log(safeDiv(-7n, 2n));
console.log(safeDiv(1n, 0n));
const empty: bigint[] = [];
try {
  empty.reduce((a, b) => a + b);
} catch (e) {
  console.log(`${(e as Error).name}: ${(e as Error).message}`);
}
try {
  console.log(`${2n ** -1n}`);
} catch (e) {
  console.log((e as Error).name);
}
