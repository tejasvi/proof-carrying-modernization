import EquivLean.Bridge.TS.AutoXLang
import EquivLean.Demo.Gen.TS.PolyHash
import EquivLean.Demo.Gen.Aeneas.PolyHash.Funs
import EquivLean.Demo.TS.FnvXLang

/-!
# Demo: TypeScript ↔ Rust polynomial hash in int32, with a generated coupling

* TypeScript: `examples/ts/poly_hash.ts` (`h = (Math.imul(h, 31) + data[i]) | 0` over a
  `Uint8Array`), translated by the pinned StrictTS front end to `Demo/Gen/TS/PolyHash.lean`;
* Rust: `examples/rust/polyhash/src/lib.rs` (`h = h.wrapping_mul(31).wrapping_add(data[i] as i32)`
  over `&[u8]`, `h : i32`), translated by Charon + Aeneas to `Demo/Gen/Aeneas/PolyHash/Funs.lean`.

`poly_equiv`: for a `Uint8Array` and a byte slice holding the same bytes, the TypeScript function
returns the `number` holding the Rust `i32` result (`F64.ofInt32 h.bv`) and leaves the world
unchanged, and the two are safe on the same inputs.  One `equiv_ts_rust` call
(`Bridge/TS/AutoXLang.lean`): the coupling of the two loops is generated (the TypeScript `h` and
`i` hold the Rust `h : i32` and `i : usize`, as `F64.ofInt32 h.bv` and `F64.ofNat i.val`; the bound
`i.val ≤ d.val.length`), the exit relation is the implication between the continuations.  Given:
the arithmetic of one iteration on each side (`ts_step`: `Math.imul` and `| 0` on int32 doubles,
`imul_ofInt32_ofNat` and `bor_zero_add_ofInt32_ofNat`; `rust_step`: Aeneas' `bv` lemmas), the byte
correspondence and the outcome relation.
-/

namespace EquivLean.Demo.TS.AutoPolyHash
open EquivLean EquivLean.TS StrictTS
open _root_.Aeneas _root_.Aeneas.Std
open EquivLean.Demo.Gen.TS
open EquivLean.Demo.TS.FnvXLang (BytesCorr)

abbrev TT := PolyHash.TT

/-- The TypeScript outcome holds the Rust `i32` (`number` = int32) and the world is unchanged. -/
def PolyRel (w : World TT) (o : Out TT (Val TT .num)) (r : Except Error I32) : Prop :=
  ∃ h : I32, r = .ok h ∧ o = (.ok (.num (F64.ofInt32 h.bv)), w)

/-- One TypeScript iteration on doubles: `(Math.imul(h, 31) + b) | 0`. -/
theorem ts_step (x : BitVec 32) (b : BitVec TAKind.u8.width) :
    (((F64.ofInt32 x).imul (F64.ofNat 31)) + F64.ofUintN b).bor (F64.ofNat 0) =
      F64.ofInt32 (x * BitVec.ofNat 32 31 + BitVec.ofNat 32 b.toNat) := by
  have hb : b.toNat < 256 := b.isLt
  rw [ofUintN_eq_ofNat, imul_ofInt32_ofNat _ (by omega), bor_zero_add_ofInt32_ofNat _ (by omega)]

/-- One Rust iteration on bit vectors. -/
theorem rust_step (h : I32) (x : U8) :
    (core.num.I32.wrapping_add (core.num.I32.wrapping_mul h 31#i32) (UScalar.hcast .I32 x)).bv =
      (h.bv : BitVec 32) * BitVec.ofNat 32 31 + BitVec.ofNat 32 x.val := by
  simp only [core.num.I32.wrapping_add_bv_eq, core.num.I32.wrapping_mul_bv_eq, UScalar.hcast_bv_eq]
  have e1 : I32.bv 31#i32 = 31#32 := rfl
  have e2 : BitVec.ofNat 32 x.val = BitVec.setWidth 32 x.bv := BitVec.ofNat_toNat 32 x.bv
  rw [e1, e2]
  rfl

/-- **TypeScript ≈ Rust** (the polynomial hash over the same bytes), with no coupling written. -/
theorem poly_equiv (I : Impl) (a : Nat) (bytes : Array (BitVec TAKind.u8.width)) (d : Slice U8)
    (w : World TT) (hw : w.heap.get? (.tarr .u8, a) = some bytes) (hc : BytesCorr bytes d)
    (hlen : bytes.size < 4294967296) :
    Equiv (PolyRel w) (call I PolyHash.program PolyHash.polyHashRef (.cons (.tarr a) .nil) w)
      (polyhash.poly_hash d) := by
  obtain ⟨hsize, hget⟩ := hc
  equiv_ts_rust [PolyHash.polyHash_call, PolyHash.polyHashDef, polyhash.poly_hash,
    polyhash.poly_hash_loop] with [ts_step, rust_step, hget, PolyRel]

end EquivLean.Demo.TS.AutoPolyHash

#print axioms EquivLean.Demo.TS.AutoPolyHash.ts_step
#print axioms EquivLean.Demo.TS.AutoPolyHash.rust_step
#print axioms EquivLean.Demo.TS.AutoPolyHash.poly_equiv
