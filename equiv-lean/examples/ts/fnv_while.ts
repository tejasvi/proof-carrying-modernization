// TS <-> Rust demo (equiv-lean, StrictTS bridge): FNV-1a, 32 bits, over a byte array, written
// with a `while` loop and the index declared before the hash (the environment is [h, i, data],
// against the Rust state (h, i)).  The Rust side is examples/rust/bits/src/lib.rs (`fnv1a32`).
export function fnvWhile(data: Uint8Array): number {
  let i = 0;
  let h = 0x811c9dc5;
  while (i < data.length) {
    h ^= data[i];
    h = Math.imul(h, 0x01000193) >>> 0;
    i++;
  }
  return h;
}

console.log(String(fnvWhile(new Uint8Array([104, 101, 108, 108, 111]))));
