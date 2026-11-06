// Errors: String(e), template of names, instanceof on error kinds, errors from callbacks.
const errs: Error[] = [new Error("plain"), new TypeError("typed"), new RangeError(""), new Error()];
for (const e of errs) {
  console.log(`${String(e)} | name=${e.name} | msg=[${e.message}] | type? ${e instanceof TypeError}`);
}
function thrower(x: bigint): bigint { if (x === 2n) throw new RangeError(`bad ${x}`); return x * 10n; }
try {
  [1n, 2n, 3n].map(thrower);
} catch (e) {
  console.log(`map stopped: ${(e as Error).message}`);
}
const m = new Map<string, bigint>([["a", 1n], ["b", 2n]]);
try {
  m.forEach((v, k) => { if (k === "b") throw new Error(`in forEach ${v}`); });
} catch (e) {
  if (e instanceof Error) console.log(e.message);
}
function rethrow(): void {
  try { throw new SyntaxError("s"); } catch (e) { throw e; }
}
try { rethrow(); } catch (e) { console.log(`rethrown ${(e as Error).name}`); }
