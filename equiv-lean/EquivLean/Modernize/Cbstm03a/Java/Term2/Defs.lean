import EquivLean.Modernize.Cbstm03a.Java.Iface2
import EquivLean.Modernize.Cbstm03a.Java.Iface1
import EquivLean.Modernize.Cbstm03a.Java.Iface3

/-!
# CBSTM03A → Java, termination of the memory and text helpers: shared definitions

* `contractOK_mono`: a contract that holds holds for a stronger precondition and a weaker postcondition.
* The slot geometry: position `o` lies in its slot, `slotSt (slotIdx o) ≤ o < slotSt (slotIdx o) + slotLn …`
  (the step of `memWrite`'s and `memRead`'s loops is at least one character).
* `SlotOk σ vs`: every slot is `null` or a string (what the loops of `memWrite`/`memRead` load from the array).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Term2

open EquivLean.Modernize.Cbstm03a.Java

/-- A contract that holds holds for a stronger precondition and a weaker postcondition. -/
theorem contractOK_mono {P : Program} {sig : MethodSig} {S S' : Spec} (h : ContractOK P sig S)
    (hpre : ∀ args σ, S'.pre args σ → S.pre args σ)
    (hpost : ∀ args σ o, S'.pre args σ → S.post args σ o → S'.post args σ o) : ContractOK P sig S' :=
  ⟨fun m ht args σ o hp hx => hpost args σ o hp (h.1 m ht args σ o (hpre args σ hp) hx),
   fun c h1 h2 h3 args σ o hp hx => hpost args σ o hp (h.2 c h1 h2 h3 args σ o (hpre args σ hp) hx)⟩

/-! ## Slot geometry -/

theorem slotIdx_div (o : Nat) : slotIdx o / 11 = o / 3356 := by unfold slotIdx; split <;> omega

theorem slotIdx_mod (o : Nat) : slotIdx o % 11 = if o % 3356 < 16 then 0 else 1 + (o % 3356 - 16) / 334 := by
  unfold slotIdx; split <;> omega

theorem slotSt_slotIdx (o : Nat) :
    slotSt (slotIdx o) = o / 3356 * 3356 + if o % 3356 < 16 then 0 else 16 + (o % 3356 - 16) / 334 * 334 := by
  unfold slotSt
  rw [slotIdx_div, slotIdx_mod]
  by_cases h : o % 3356 < 16
  · simp only [h, ite_true]
  · simp only [h, ite_false]
    split <;> omega

theorem slotLn_slotIdx (o : Nat) : slotLn (slotIdx o) = if o % 3356 < 16 then 16 else 334 := by
  unfold slotLn
  rw [slotIdx_mod]
  by_cases h : o % 3356 < 16
  · simp only [h, ite_true]
  · simp only [h, ite_false]
    split <;> omega

theorem slotIdx_lt (o : Nat) (h : o < 171156) : slotIdx o < 561 := by
  unfold slotIdx; split <;> omega

theorem slotSt_le (o : Nat) : slotSt (slotIdx o) ≤ o := by
  rw [slotSt_slotIdx]; split <;> omega

theorem lt_slotSt_add (o : Nat) : o < slotSt (slotIdx o) + slotLn (slotIdx o) := by
  rw [slotSt_slotIdx, slotLn_slotIdx]; split <;> omega

theorem slotLn_cases (i : Nat) : slotLn i = 16 ∨ slotLn i = 334 := by
  unfold slotLn; split <;> simp

/-! ## The slots array -/

/-- Every slot is `null` or a string. -/
def SlotOk (σ : State) (vs : List Value) : Prop :=
  ∀ v ∈ vs, v = .null ∨ ∃ y s, v = .ref y ∧ σ.heap y = some (.str s)

theorem slotOk_of_slotsAt {σ : State} {a : Addr} {m : Nat → JChar} {vs : List Value}
    (hs : SlotsAt σ a m) (ha : σ.heap a = some (.array (.cls "java.lang.String") vs)) : SlotOk σ vs := by
  obtain ⟨vs', ha', hl, hv⟩ := hs
  rw [ha] at ha'
  cases ha'
  intro v hv'
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv'
  rcases hv i (by omega) with ⟨h1, -⟩ | ⟨y, t, h1, h2, -⟩
  · left; rw [List.getElem?_eq_getElem hi] at h1; exact Option.some.inj h1
  · right; rw [List.getElem?_eq_getElem hi] at h1; exact ⟨y, t, Option.some.inj h1, h2⟩

end EquivLean.Modernize.Cbstm03a.Java.Term2
