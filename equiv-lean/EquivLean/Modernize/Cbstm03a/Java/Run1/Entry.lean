import EquivLean.Modernize.Cbstm03a.Java.Run1.Lem

/-!
# CBSTM03A → Java `run`: the entry path (statements 0 … 12)

`res = new Cbstm03a$Result()` (the constructor inlined: three new `ArrayList`s), `trnxTexts = new
String[trnxFile.length]`, `i = 0`: the TRNXFILE loop's invariant `inv12` with no text stored.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space grows_refl)

namespace EquivLean.Modernize.Cbstm03a.Java

open Seg1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000 in
theorem run_entry_vc (g : RunG) : RunEntryVC g := by
  intro args σ0 hpre
  obtain ⟨hargs, ⟨et1, xs1, hh1, hl1, hf1⟩, -, -, -, ⟨hcpi, -⟩, hinit⟩ := hpre
  subst hargs
  have hk := hid_intro (forall2_length hf1)
  clear hf1
  unfold runWP
  jvc [runCallees, runInv]
  have hlen := hid_elim hk
  refine ⟨σ0.next, σ0.next + 1, σ0.next + 1 + 1, σ0.next + 1 + 1 + 1, σ0.next + 1 + 1 + 1 + 1,
    BitVec.ofNat 32 xs1.length, 0, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · refine resAtL_ctor ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · hsimp <;> rfl
    · hsimp <;> rfl
    · hsimp <;> rfl
    · hsimp <;> rfl
    · jdisch
    · jdisch
    · jdisch
  · jdisch
  · jdisch
  · jdisch
  · jdisch
  · refine ⟨?_, fun x hx => ?_⟩
    · simp only [State.next_alloc, State.next_setObj]; jdisch
    · hsimp
  · simp only [State.alloc_inits, State.setObj_inits]
  · simp only [State.alloc_statics, State.setObj_statics]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · rw [bv32_toInt_ofNat_of_lt hl1, hlen]
  · rw [i32_zero_toInt]
  · rw [i32_zero_toInt, bv32_toInt_ofNat_of_lt hl1]; omega
  · rw [i32_zero_toInt]
    simp only [Int.toNat_zero, List.take_zero, Nat.sub_zero]
    rw [← hlen]
    apply textsAt_new
    hsimp
  · jdisch

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_entry_vc
