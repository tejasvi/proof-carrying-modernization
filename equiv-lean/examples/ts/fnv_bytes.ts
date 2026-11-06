// TS <-> Rust demo (equiv-lean, StrictTS bridge): FNV-1a, 32 bits, over a byte array.
// The Rust side is examples/rust/bits/src/lib.rs (`fnv1a32`, with u32::wrapping_mul),
// translated by Charon + Aeneas to EquivLean/Demo/Gen/Aeneas/Bits/Funs.lean.
export function fnv1a32(data: Uint8Array): number {
  let h = 0x811c9dc5;
  for (let i = 0; i < data.length; i++) {
    h ^= data[i];
    h = Math.imul(h, 0x01000193) >>> 0;
  }
  return h;
}

console.log(String(fnv1a32(new Uint8Array([104, 101, 108, 108, 111]))));
