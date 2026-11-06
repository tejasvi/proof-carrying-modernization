import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Demo.Gen.Aeneas.Bits.Funs

/-!
# FNV-1a on real Charon + Aeneas output: the loop against a pure Lean function

`bits.fnv1a32` (from `examples/rust/bits/src/lib.rs`) is a `while i < data.len()` loop with a
checked `i += 1`, an `as u32` cast, `^=` and `wrapping_mul`.  `fnv1a32_spec` shows that it
never panics and returns the left fold `fnv` of the byte list, with the one-sided loop rule
`wp_loop` (invariant: folding the remaining bytes from the current hash gives the result).
`fnv1a32_equiv_fnv` restates this as an equivalence with a pure Lean value (`pureVal`), the
form used to compare the Rust function with another encoding through `Sim.trans`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.Aeneas.Fnv

/-- One FNV-1a step on 32 bits. -/
def fnvStep (h : BitVec 32) (b : U8) : BitVec 32 := (h ^^^ b.bv.setWidth 32) * 0x01000193#32

/-- FNV-1a, 32 bits, of a list of bytes. -/
def fnv (l : List U8) : BitVec 32 := l.foldl fnvStep 0x811c9dc5#32

theorem foldl_drop_succ {α β : Type} (f : β → α → β) (b : β) (l : List α) (i : Nat)
    (h : i < l.length) : (l.drop i).foldl f b = (l.drop (i + 1)).foldl f (f b l[i]) := by
  rw [List.drop_eq_getElem_cons h, List.foldl_cons]

theorem fnv1a32_spec (d : Slice U8) : wp (bits.fnv1a32 d) (fun o => o = .ok ⟨fnv d.val⟩) := by
  unfold bits.fnv1a32 bits.fnv1a32_loop
  refine wp_loop (loop_shape _)
    (fun p => p.2.val ≤ d.val.length ∧ (d.val.drop p.2.val).foldl fnvStep p.1.bv = fnv d.val)
    (fun p => d.val.length - p.2.val) ?_ _ ⟨by simp, by simp [fnv]⟩
  rintro ⟨h, i⟩ ⟨hi, hinv⟩
  have hlen := d.property
  aeneas_wp [bits.fnv1a32_loop.body] at *
  split_ifs with h1 h2
  · simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
    rw [foldl_drop_succ _ _ _ _ h1] at hinv
    refine ⟨⟨by omega, ?_⟩, by omega⟩
    rw [← hinv]
    congr 1
  · exfalso; scalar_tac
  · simp only [loopCls_done]
    have : i.val = d.val.length := by omega
    rw [this, List.drop_length, List.foldl_nil] at hinv
    rw [← hinv]

/-- The Rust function is equivalent to the pure Lean function (its result, never a panic). -/
theorem fnv1a32_equiv_fnv (d : Slice U8) :
    Equiv (fun o r => o = .ok ⟨r⟩) (bits.fnv1a32 d) (pureVal (fnv d.val)) :=
  equiv_pureVal_iff.2 (fnv1a32_spec d)

end EquivLean.Demo.Aeneas.Fnv

#print axioms EquivLean.Demo.Aeneas.Fnv.fnv1a32_equiv_fnv
