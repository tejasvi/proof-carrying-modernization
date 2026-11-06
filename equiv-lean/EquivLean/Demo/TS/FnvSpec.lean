import EquivLean.Demo.TS.FnvXLang
import EquivLean.Demo.Aeneas.Fnv

/-!
# Demo: chaining a migration through a common reference (`Equiv.trans`)

`fnv_equiv` (TypeScript ≈ Rust, `Demo/TS/FnvXLang.lean`) composed with eq-aeneas's
`fnv1a32_equiv_fnv` (Rust ≈ the pure Lean fold `fnv`, `Demo/Aeneas/Fnv.lean`): the TypeScript
function computes the FNV-1a fold of the bytes, as a uint32 `number`, and leaves the world
unchanged.
-/

namespace EquivLean.Demo.TS.FnvSpec
open EquivLean EquivLean.TS StrictTS
open _root_.Aeneas _root_.Aeneas.Std
open EquivLean.Demo.Gen.TS EquivLean.Demo.TS.FnvXLang

/-- **TypeScript ≈ pure FNV-1a**, through the Rust function. -/
theorem fnv_equiv_spec (I : Impl) (a : Nat) (bytes : Array (BitVec TAKind.u8.width))
    (d : Slice U8) (w : World TT) (hw : w.heap.get? (.tarr .u8, a) = some bytes)
    (hc : BytesCorr bytes d) (hlen : bytes.size < 4294967296) :
    Equiv (fun (o : Out TT (Val TT .num)) (r : BitVec 32) => o = (.ok (.num (F64.ofUint32 r)), w))
      (call I FnvBytes.program FnvBytes.fnv1a32Ref (.cons (.tarr a) .nil) w)
      (pureVal (EquivLean.Demo.Aeneas.Fnv.fnv d.val)) :=
  ((fnv_equiv I a bytes d w hw hc hlen).trans
    (EquivLean.Demo.Aeneas.Fnv.fnv1a32_equiv_fnv d)).mono fun _ _ ⟨_, ⟨_, h1, h2⟩, h3⟩ => by
      subst h1 h2; cases h3; rfl

end EquivLean.Demo.TS.FnvSpec
