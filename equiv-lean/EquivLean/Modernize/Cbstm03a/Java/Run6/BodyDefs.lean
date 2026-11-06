import EquivLean.Modernize.Cbstm03a.Java.Run6.Lem

/-!
# CBSTM03A → Java `run`, statement 179: the loop body's wrappers for `jvc`

`SlotsK`: the table memory kept folded during the symbolic run (`jvc` would destructure it), with the rewrite rule
that folds it in the callee contracts. The table memory and the `Result` object carry over the callees' `Grows`
and the allocation of the substring; the offsets `tranOff` computes for counters in `1 … 9999` do not overflow.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space GrowsK grows_split
  growsK_elim grows_refl grows_trans forall2_imp)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg6

@[irreducible] def SlotsK (σ : State) (a : Addr) (m : Nat → JChar) : Prop := SlotsAt σ a m

theorem slots_k (σ : State) (a : Addr) (m : Nat → JChar) : SlotsAt σ a m ↔ SlotsK σ a m := by
  unfold SlotsK; exact Iff.rfl

/-! ## Frames -/

theorem resAtL_grows {σ σ' : State} {res ld ls lh : Addr} {d s t : List JStr} {ab : Bool}
    (h : ResAtL σ res ld ls lh d s t ab) (hg : Grows σ σ') : ResAtL σ' res ld ls lh d s t ab := by
  obtain ⟨fs, hr, f1, f2, f3, f4, n1, n2, n3, ⟨xd, md, hd, fd⟩, ⟨xs, ms, hs, fs'⟩, ⟨xh, mh, hh, fh⟩⟩ := h
  have hm : ∀ {v : Value} {z : JStr}, JStrAt σ v z → JStrAt σ' v z := by
    intro v z hv
    obtain ⟨x, rfl, hx⟩ := hv
    exact ⟨x, rfl, EquivLean.Modernize.Cbstm03b.Java.heap_grows hg hx⟩
  exact ⟨fs, EquivLean.Modernize.Cbstm03b.Java.heap_grows hg hr, f1, f2, f3, f4, n1, n2, n3,
    ⟨xd, md, EquivLean.Modernize.Cbstm03b.Java.heap_grows hg hd, forall2_imp (fun _ _ h => hm h) fd⟩,
    ⟨xs, ms, EquivLean.Modernize.Cbstm03b.Java.heap_grows hg hs, forall2_imp (fun _ _ h => hm h) fs'⟩,
    ⟨xh, mh, EquivLean.Modernize.Cbstm03b.Java.heap_grows hg hh, forall2_imp (fun _ _ h => hm h) fh⟩⟩

theorem grows_alloc (σ : State) (o : Obj) : Grows σ (σ.alloc o).2 :=
  ⟨by rw [State.next_alloc]; exact Nat.le_succ _, fun _ hy => State.heap_alloc_of_lt hy o⟩

theorem slotsAt_grows {σ σ' : State} {a : Addr} {m : Nat → JChar} (h : SlotsAt σ a m) (hg : Grows σ σ') :
    SlotsAt σ' a m := by
  obtain ⟨vs, h1, h2, h3⟩ := h
  refine ⟨vs, EquivLean.Modernize.Cbstm03b.Java.heap_grows hg h1, h2, fun i hi => ?_⟩
  rcases h3 i hi with h | ⟨x, t, e1, e2, e3, e4⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, t, e1, EquivLean.Modernize.Cbstm03b.Java.heap_grows hg e2, e3, e4⟩

theorem slotsK_growsK {σ σ' : State} {a : Addr} {m : Nat → JChar} (h : SlotsK σ a m) (hg : GrowsK σ σ') :
    SlotsK σ' a m := by
  unfold SlotsK at h ⊢; exact slotsAt_grows h (growsK_elim hg)

/-! ## Texts and numbers the run computes -/

theorem memRd_length (m : Nat → JChar) (off : Int) (n : Nat) : (memRd m off n).length = n := by
  simp [memRd]

theorem bmod64_self' {v : Int} (h0 : -9223372036854775808 ≤ v) (h1 : v < 9223372036854775808) :
    v.bmod (2 ^ 64) = v := bmod64_self h0 h1

/-- `tranOff(cr, tr)` for card and transaction numbers in `1 … 9999`: no overflow. -/
theorem tranOff_toInt {cr tr : I64} (h1 : 1 ≤ cr.toInt) (h2 : cr.toInt < 10000) (h3 : 1 ≤ tr.toInt)
    (h4 : tr.toInt < 10000) :
    ((cr - 1) * 3356 + 16 + (tr - 1) * 334 : I64).toInt = (cr.toInt - 1) * 3356 + 16 + (tr.toInt - 1) * 334 := by
  have e1 : (1 : I64).toInt = 1 := by decide
  have e2 : (3356 : I64).toInt = 3356 := by decide
  have e3 : (16 : I64).toInt = 16 := by decide
  have e4 : (334 : I64).toInt = 334 := by decide
  simp only [BitVec.toInt_add, BitVec.toInt_mul, BitVec.toInt_sub, e1, e2, e3, e4]
  simp (disch := omega) only [bmod64_self']

theorem tranOff_lb {cr tr : I64} (h1 : 1 ≤ cr.toInt) (h2 : cr.toInt < 10000) (h3 : 1 ≤ tr.toInt)
    (h4 : tr.toInt < 10000) : -2147483648 < ((cr - 1) * 3356 + 16 + (tr - 1) * 334 : I64).toInt := by
  rw [tranOff_toInt h1 h2 h3 h4]; omega

theorem tranOff16_toInt {cr tr : I64} (h1 : 1 ≤ cr.toInt) (h2 : cr.toInt < 10000) (h3 : 1 ≤ tr.toInt)
    (h4 : tr.toInt < 10000) :
    ((cr - 1) * 3356 + 16 + (tr - 1) * 334 + 16#64 : I64).toInt =
      (cr.toInt - 1) * 3356 + 16 + (tr.toInt - 1) * 334 + 16 := by
  have e3 : (16#64 : I64).toInt = 16 := by decide
  rw [BitVec.toInt_add, tranOff_toInt h1 h2 h3 h4, e3]
  exact bmod64_self' (by omega) (by omega)

theorem tranOff16_lb {cr tr : I64} (h1 : 1 ≤ cr.toInt) (h2 : cr.toInt < 10000) (h3 : 1 ≤ tr.toInt)
    (h4 : tr.toInt < 10000) : -2147483648 < ((cr - 1) * 3356 + 16 + (tr - 1) * 334 + 16#64 : I64).toInt := by
  rw [tranOff16_toInt h1 h2 h3 h4]; omega

end EquivLean.Modernize.Cbstm03a.Java.Seg6
