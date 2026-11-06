import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Demo.Gen.Aeneas.Bits.Funs

/-!
# A loop replaced by a branch-free computation (real Charon + Aeneas output)

`examples/rust/bits/src/lib.rs` has two population counts: `popcount` (Kernighan's loop:
clear the lowest set bit until zero, with checked `v - 1` and `c + 1`) and `popcount_swar`
(branch-free SWAR, with checked `-` and `+` and a wrapping multiplication).  A PR that replaces
the first by the second is behaviour-preserving, panics included (neither panics):

* `popcount_swar_spec`: symbolic execution with the bit-vector forms of the scalar lemmas and
  `bv_decide` (the checked operations never overflow);
* `popcount_spec`: the loop, by the one-sided loop rule `wp_loop` (invariant
  `c + swar v = swar x`, variant `v`), with three `bv_decide` facts about `swar`;
* `popcount_equiv_swar`: `Equiv (· = ·)` of the two Rust functions.

The specification `swar` is the SWAR algorithm on `BitVec 32`; it is also the closed form
against which the TypeScript side can be compared.  `bv_decide` adds one native-code axiom per
use (`<theorem>._native.bv_decide.ax_1`), see `#print axioms` at the end.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.Aeneas.Popcount

/-- Population count of a 32-bit word, branch-free (the specification). -/
def swar (x : BitVec 32) : BitVec 32 :=
  let v := x - ((x >>> 1) &&& 0x55555555#32)
  let v := (v &&& 0x33333333#32) + ((v >>> 2) &&& 0x33333333#32)
  let v := (v + (v >>> 4)) &&& 0x0f0f0f0f#32
  (v * 0x01010101#32) >>> 24

theorem swar_le (x : BitVec 32) : swar x ≤ 32#32 := by
  unfold swar; bv_decide

theorem swar_step (v : BitVec 32) (h : v ≠ 0#32) : swar (v &&& (v - 1#32)) + 1#32 = swar v := by
  unfold swar; bv_decide

theorem and_sub_lt (v : BitVec 32) (h : v ≠ 0#32) : (v &&& (v - 1#32)) < v := by
  bv_decide

theorem swar_zero : swar 0#32 = 0#32 := by
  unfold swar; bv_decide

theorem swar_toNat_le (x : BitVec 32) : (swar x).toNat ≤ 32 := by
  have := swar_le x
  rw [BitVec.le_def] at this
  simpa using this

theorem swar_step_toNat (v : BitVec 32) (h : v ≠ 0#32) :
    (swar (v &&& (v - 1#32))).toNat + 1 = (swar v).toNat := by
  have h1 := swar_step v h
  have h2 := swar_toNat_le (v &&& (v - 1#32))
  rw [← h1, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.one_mod]
  omega

/-- The branch-free version computes `swar` and never panics. -/
theorem popcount_swar_spec (x : U32) :
    wp (bits.popcount_swar x) (fun o => o = .ok ⟨swar x.bv⟩) := by
  unfold bits.popcount_swar
  simp only [wp_bind, wp_lift, wp_UScalar_shr, wp_UScalar_sub_bvc, wp_UScalar_add_bvc,
    UScalar.bv_and, core.num.U32.wrapping_mul_bv_eq, Except.ok.injEq, UScalar.mk.injEq,
    reduceCtorEq]
  simp [swar]
  bv_decide

/-- Kernighan's loop computes `swar` too, and never panics. -/
theorem popcount_spec (x : U32) : wp (bits.popcount x) (fun o => o = .ok ⟨swar x.bv⟩) := by
  unfold bits.popcount bits.popcount_loop
  refine wp_loop (loop_shape _)
    (fun p => p.2.val + (swar p.1.bv).toNat = (swar x.bv).toNat) (fun p => p.1.val) ?_ _
    (by simp)
  rintro ⟨v, c⟩ hinv
  simp only at hinv
  have hx := swar_toNat_le x.bv
  simp only [bits.popcount_loop.body, wp_bind, wp_ite, wp_lift, wp_ok, wp_UScalar_sub_bvc,
    wp_UScalar_add_val, bne_iff_ne, ne_eq]
  by_cases hv : v.val = 0
  · have hv' : v.bv = 0#32 := by apply BitVec.eq_of_toNat_eq; simp [hv]
    have hv0 : v = 0#u32 := UScalar.eq_of_val_eq (by rw [hv]; rfl)
    rw [ite_eq_right (not_not.2 hv0)]
    simp only [loopCls_done, Except.ok.injEq]
    rw [hv', swar_zero] at hinv
    apply UScalar.eq_of_val_eq
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at hinv
    exact hinv
  · have hv' : v.bv ≠ 0#32 := fun h => hv (by show v.bv.toNat = 0; rw [h]; rfl)
    have hv0 : ¬ v = 0#u32 := fun h => hv (by rw [h]; rfl)
    rw [ite_eq_left hv0]
    have h1 : 1#32 ≤ v.bv := by bv_decide
    have h1' : (1#u32 : U32).bv ≤ v.bv := h1
    rw [ite_eq_left h1']
    have hc : c.val + (1#u32 : U32).val ≤ UScalar.max .U32 := by
      simp only [UScalar.max_UScalarTy_U32_eq, U32.max_eq]
      have : (1#u32 : U32).val = 1 := rfl
      omega
    rw [dite_eq_left hc]
    simp only [loopCls_cont]
    have hstep := swar_step_toNat v.bv hv'
    have hlt : (v.bv &&& (v.bv - 1#32)).toNat < v.bv.toNat := by
      have := and_sub_lt v.bv hv'
      rwa [BitVec.lt_def] at this
    refine ⟨?_, ?_⟩
    · show c.val + 1 + (swar (v.bv &&& (v.bv - 1#32))).toNat = (swar x.bv).toNat
      omega
    · exact hlt

/-- The PR "replace Kernighan's loop by SWAR" preserves the behaviour, panics included. -/
theorem popcount_equiv_swar (x : U32) :
    Equiv (· = ·) (bits.popcount_swar x) (bits.popcount x) :=
  equiv_of_wp_eq (popcount_swar_spec x) (popcount_spec x)

end EquivLean.Demo.Aeneas.Popcount

#print axioms EquivLean.Demo.Aeneas.Popcount.popcount_equiv_swar
