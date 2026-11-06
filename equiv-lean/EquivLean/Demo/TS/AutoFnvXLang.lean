import EquivLean.Bridge.TS.AutoXLang
import EquivLean.Demo.TS.FnvXLang
import EquivLean.Demo.Gen.TS.FnvWhile

/-!
# Demo: TypeScript ↔ Rust FNV-1a with a generated coupling (no invariant written)

`Demo/TS/FnvXLang.lean` pairs the TypeScript `for` loop of `fnv1a32` (`Gen/TS/FnvBytes.lean`) with
the Aeneas `loop` of `bits.fnv1a32` (`Gen/Aeneas/Bits/Funs.lean`) through a hand-written coupling
(`fnvJ`) and loop-exit relation (`fnvLoopR`).  Here the same theorems are proved by `sim_ts_rust`
and `equiv_ts_rust` (`Bridge/TS/AutoXLang.lean`), which generate both:

* the coupling: the world at loop entry, and the environment `[i, h, data]` holding the Rust loop
  variables `(h, i)` as numbers, `F64.ofNat i.val` (`usize`) and `F64.ofUint32 h.bv` (`u32`),
  paired in declaration order; plus the bound `i.val ≤ d.val.length` from the Rust condition
  `i < data.len()`;
* the loop-exit relation: the implication between the continuations after the two loops.

Given (`with […]`): the arithmetic of one iteration on each side (`ts_step`: the int32 bridge of
`Bridge/TS/Corr.lean`; `rust_step`: Aeneas' `bv` lemmas, both from `FnvXLang.lean`), the byte
correspondence `hget` and the outcome relation `FnvRel`.

`fnv_while_equiv`: the same against `examples/ts/fnv_while.ts` (`Gen/TS/FnvWhile.lean`), a
`while` loop that declares the index before the hash.  Its environment is `[h, i, data]`, so
declaration order pairs `i` with the Rust `h`; the coupling that closes is the second attempt,
which pairs the variables in the order of their first assignment in the two loop bodies (`h`,
then `i`).
-/

namespace EquivLean.Demo.TS.AutoFnvXLang
open EquivLean EquivLean.TS StrictTS
open _root_.Aeneas _root_.Aeneas.Std
open EquivLean.Demo.Gen.TS EquivLean.Demo.TS.FnvXLang

section
variable (I : Impl) (a : Nat) (bytes : Array (BitVec TAKind.u8.width)) (d : Slice U8)
  (w : World TT)

/-- **TypeScript ⊑ Rust**, with no coupling written. -/
theorem fnv_ts_sim_rust (hw : w.heap.get? (.tarr .u8, a) = some bytes) (hc : BytesCorr bytes d)
    (hlen : bytes.size < 4294967296) :
    Sim (FnvRel w) (call I FnvBytes.program FnvBytes.fnv1a32Ref (.cons (.tarr a) .nil) w)
      (bits.fnv1a32 d) := by
  obtain ⟨hsize, hget⟩ := hc
  sim_ts_rust [FnvBytes.fnv1a32_call, FnvBytes.fnv1a32Def, bits.fnv1a32, bits.fnv1a32_loop]
    with [ts_step, rust_step, hget, FnvRel]

/-- **Rust ⊑ TypeScript**, with no coupling written. -/
theorem fnv_rust_sim_ts (hw : w.heap.get? (.tarr .u8, a) = some bytes) (hc : BytesCorr bytes d)
    (hlen : bytes.size < 4294967296) :
    Sim (fun r o => FnvRel w o r) (bits.fnv1a32 d)
      (call I FnvBytes.program FnvBytes.fnv1a32Ref (.cons (.tarr a) .nil) w) := by
  obtain ⟨hsize, hget⟩ := hc
  sim_ts_rust [FnvBytes.fnv1a32_call, FnvBytes.fnv1a32Def, bits.fnv1a32, bits.fnv1a32_loop]
    with [ts_step, rust_step, hget, FnvRel]

/-- **TypeScript ≈ Rust** (FNV-1a over the same bytes), both directions in one call. -/
theorem fnv_equiv (hw : w.heap.get? (.tarr .u8, a) = some bytes) (hc : BytesCorr bytes d)
    (hlen : bytes.size < 4294967296) :
    Equiv (FnvRel w) (call I FnvBytes.program FnvBytes.fnv1a32Ref (.cons (.tarr a) .nil) w)
      (bits.fnv1a32 d) := by
  obtain ⟨hsize, hget⟩ := hc
  equiv_ts_rust [FnvBytes.fnv1a32_call, FnvBytes.fnv1a32Def, bits.fnv1a32, bits.fnv1a32_loop]
    with [ts_step, rust_step, hget, FnvRel]

/-- **TypeScript `while` ≈ Rust**: variables paired by order of first assignment. -/
theorem fnv_while_equiv (hw : w.heap.get? (.tarr .u8, a) = some bytes) (hc : BytesCorr bytes d)
    (hlen : bytes.size < 4294967296) :
    Equiv (FnvRel w) (call I FnvWhile.program FnvWhile.fnvWhileRef (.cons (.tarr a) .nil) w)
      (bits.fnv1a32 d) := by
  obtain ⟨hsize, hget⟩ := hc
  equiv_ts_rust [FnvWhile.fnvWhile_call, FnvWhile.fnvWhileDef, bits.fnv1a32, bits.fnv1a32_loop]
    with [ts_step, rust_step, hget, FnvRel]

end

end EquivLean.Demo.TS.AutoFnvXLang

#print axioms EquivLean.Demo.TS.AutoFnvXLang.fnv_ts_sim_rust
#print axioms EquivLean.Demo.TS.AutoFnvXLang.fnv_rust_sim_ts
#print axioms EquivLean.Demo.TS.AutoFnvXLang.fnv_equiv
#print axioms EquivLean.Demo.TS.AutoFnvXLang.fnv_while_equiv
