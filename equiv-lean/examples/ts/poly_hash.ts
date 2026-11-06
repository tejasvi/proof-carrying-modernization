// TS <-> Rust demo (equiv-lean, StrictTS bridge): a polynomial hash over a byte array, in int32
// arithmetic (h = 31 * h + byte, wrapping).  The Rust side is examples/rust/polyhash/src/lib.rs
// (`poly_hash`, with i32::wrapping_mul and i32::wrapping_add), translated by Charon + Aeneas to
// EquivLean/Demo/Gen/Aeneas/PolyHash/Funs.lean.
export function polyHash(data: Uint8Array): number {
  let h = 0;
  for (let i = 0; i < data.length; i++) {
    h = (Math.imul(h, 31) + data[i]) | 0;
  }
  return h;
}

console.log(String(polyHash(new Uint8Array([104, 101, 108, 108, 111]))));
