// instanceof with a library class (Date, typed arrays): decided on the value's type, and for
// unknown values on the runtime type.
function kind(x: Date | number | Uint8Array): string {
  return x instanceof Date ? "date" : x instanceof Uint8Array ? `bytes ${x.length}` : `num ${x}`;
}
console.log(`${kind(5)} ${kind(new Uint8Array(3))}`);
function isBytes(u: unknown): boolean { return u instanceof Uint8Array; }
console.log(`${isBytes(new Uint8Array(1))} ${isBytes([1])} ${isBytes("x")}`);
