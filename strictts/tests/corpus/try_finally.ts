// try / catch / finally: ordering, finally overriding, rethrow, nested.
function f(x: bigint): string {
  try {
    if (x === 0n) throw new Error("zero");
    return "ok";
  } catch (e) {
    if (e instanceof Error) return `caught ${e.message}`;
    return "?";
  } finally {
    console.log(`finally ${x}`);
  }
}
console.log(f(1n));
console.log(f(0n));
function g(): string {
  try {
    return "try";
  } finally {
    console.log("g finally");
  }
}
console.log(g());
function h(): bigint {
  let n = 0n;
  for (const k of [1n, 2n, 3n]) {
    try {
      if (k === 2n) continue;
      n += k;
    } finally {
      n += 10n;
    }
  }
  return n;
}
console.log(`h = ${h()}`);
function nested(): void {
  try {
    try {
      throw new TypeError("inner");
    } catch (e) {
      console.log(`inner catch ${(e as Error).name}`);
      throw new RangeError("rethrown");
    } finally {
      console.log("inner finally");
    }
  } catch (e) {
    if (e instanceof RangeError) console.log(`outer catch RangeError ${e.message}`);
  }
}
nested();
try { throw new Error(); } catch (e) { console.log(`empty message: [${(e as Error).message}]`); }
