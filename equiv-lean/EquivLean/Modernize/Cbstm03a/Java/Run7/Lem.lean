import EquivLean.Modernize.Cbstm03a.Java.RunPure
import EquivLean.Modernize.Cbstm03b.Java.TrnxFin

/-!
# CBSTM03A → Java `run`, the ACCTFILE loop (statement 52): shared lemmas of `CbARun7.*`

Frames for the executor (`KeepsK`, `keeps_split`, as `GrowsK`/`grows_split`), facts hidden from it (`Hid`), the
lengths of the record texts, heap frames of the text arrays and the `Result` object, `int` index arithmetic.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK growsK_elim
  grows_split grows_refl grows_trans keeps_trans keeps_of_grows keeps_setObj keeps_refl forall2_imp heap_grows
  zpadStr_length fixStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg7

/-! ## Hiding facts from `jvc` -/

/-- A fact kept out of `jvc`'s reach (it rewrites with every hypothesis it can read). -/
@[irreducible] def Hid (p : Prop) : Prop := p

theorem hid_intro {p : Prop} (h : p) : Hid p := by unfold Hid; exact h
theorem hid_elim {p : Prop} (h : Hid p) : p := by unfold Hid at h; exact h

/-- A callee's `Keeps`, kept folded across the symbolic executor. -/
@[irreducible] def KeepsK (A : Addr → Prop) (σ σ' : State) : Prop := Keeps A σ σ'

theorem keepsK_elim {A : Addr → Prop} {σ σ' : State} (h : KeepsK A σ σ') : Keeps A σ σ' := by
  unfold KeepsK at h; exact h

/-- `Keeps` for the executor: a folded copy, and the facts it unfolds to. -/
theorem keeps_split (A : Addr → Prop) (σ σ' : State) :
    Keeps A σ σ' ↔ KeepsK A σ σ' ∧ σ.next ≤ σ'.next ∧ ∀ y, y < σ.next → ¬ A y → σ'.heap y = σ.heap y := by
  constructor
  · intro h; exact ⟨by unfold KeepsK; exact h, h.1, h.2⟩
  · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩

/-! ## `int` arithmetic -/

theorem i32_toInt_add_one {i n : I32} (h : i.toInt < n.toInt) : (i + 1).toInt = i.toInt + 1 := by
  have h1 := bv32_toInt_lt n
  have h2 := bv32_le_toInt i
  have h3 : (1 : I32).toInt = 1 := by decide
  rw [BitVec.toInt_add, h3]
  exact bmod32_of_bounds (by omega) (by omega)

theorem i32_zero_toInt : (0 : I32).toInt = 0 := by decide

/-! ## Lists -/

theorem forall2_length {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → xs.length = ys.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [forall2_length h]

theorem forall2_append {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} {xs' : List α} {ys' : List β}, Forall2 R xs ys → Forall2 R xs' ys' →
      Forall2 R (xs ++ xs') (ys ++ ys')
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons h1 h2, h => .cons h1 (forall2_append h2 h)

theorem forall2_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} (_ : Forall2 R xs ys) (k : Nat) (hx : k < xs.length) (hy : k < ys.length),
      R (xs[k]'hx) (ys[k]'hy)
  | _ :: _, _ :: _, .cons h _, 0, _, _ => h
  | _ :: _, _ :: _, .cons _ h, k + 1, hx, hy =>
    forall2_getElem h k (Nat.lt_of_succ_lt_succ hx) (Nat.lt_of_succ_lt_succ hy)

theorem set_append_replicate {α : Type} (xs : List α) (v d : α) (m : Nat) :
    (xs ++ List.replicate (m + 1) d).set xs.length v = (xs ++ [v]) ++ List.replicate m d := by
  induction xs with
  | nil => simp [List.replicate_succ]
  | cons x xs ih => simp [ih]

theorem take_succ_getElem {α : Type} (T : List α) (k : Nat) (hk : k < T.length) :
    T.take (k + 1) = T.take k ++ [T[k]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  rfl

/-! ## The record texts -/

theorem trnxTextR_length (t : TrnxR) : (trnxTextR t).length = 350 := by
  simp [trnxTextR, zuI, zsI, zpadStr_length, fixStr_length]

theorem acctTextR_length (t : AcctR) : (acctTextR t).length = 300 := by
  simp [acctTextR, zuI, zsI, zpadStr_length, fixStr_length]

theorem T1_length (g : RunG) : g.T1.length = g.trs.length := by simp [RunG.T1]

theorem T4_length (g : RunG) : g.T4.length = g.ars.length := by simp [RunG.T4]

theorem R1_length (g : RunG) : g.R1.length = g.trs.length := by simp [RunG.R1, RunG.T1]

end EquivLean.Modernize.Cbstm03a.Java.Seg7
