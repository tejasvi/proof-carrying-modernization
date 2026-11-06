// Throwing an unknown value: it must be an Error (a checked cast), and is thrown as such.
function fail(e: unknown): never { throw e; }
const errs: unknown[] = [new TypeError("t1"), new Error("e2"), new RangeError("")];
for (const x of errs) {
  try {
    fail(x);
  } catch (e) {
    console.log(`${(e as Error).name}: [${(e as Error).message}] ${e instanceof Error} ${e instanceof TypeError}`);
  }
}
