import EquivLean.Modernize.Cbstm03a.Java.RunInv
import EquivLean.Modernize.Cbstm03b.Java.TrnxFin

/-!
# CBSTM03A → Java, `run`'s segments 117, 140, 153: shared facts

Wrappers that keep facts away from `jvc` (`Kp`, `KeepsK`), lists of strings element by element, the lengths of
the record texts, and the searches of the model (`custFind`, `acctFind`) by their first match.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space GrowsK grows_split
  growsK_elim fixStr_length zpadStr_length keeps_trans keeps_of_grows keeps_refl keeps_alloc)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg3

/-- A fact kept folded across the symbolic executor. -/
@[irreducible] def Kp (p : Prop) : Prop := p

theorem Kp.intro {p : Prop} (h : p) : Kp p := by unfold Kp; exact h
theorem Kp.elim {p : Prop} (h : Kp p) : p := by unfold Kp at h; exact h

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

theorem keeps_growsK {A : Addr → Prop} {σ0 σ σ' : State} (h : Keeps A σ0 σ) (hg : GrowsK σ σ') :
    Keeps A σ0 σ' := keeps_trans h (keeps_of_grows (growsK_elim hg))

theorem keeps_keepsK {A : Addr → Prop} {σ0 σ σ' : State} (h : Keeps A σ0 σ) (hk : KeepsK A σ σ') :
    Keeps A σ0 σ' := keeps_trans h (keepsK_elim hk)

theorem keeps_alloc2 {A : Addr → Prop} {σ0 σ : State} {o : Obj} (h : Keeps A σ0 σ) :
    Keeps A σ0 (σ.alloc o).2 := keeps_trans h (keeps_alloc A σ o)

/-- `Keeps A σ0 σ` for a state built from `σ0` by allocations and callees (`GrowsK`, `KeepsK A`). -/
macro "seg3_keeps_tac" : tactic => `(tactic| repeat (first | (refine keeps_alloc2 ?_) | (refine keeps_growsK ?_ (by assumption)) | (refine keeps_keepsK ?_ (by assumption)) | (with_reducible exact keeps_refl _ _)))

/-- `spaces(1000)`'s text, folded (simp would unroll `List.replicate 1000`). -/
@[irreducible] def sp1000 : JStr := List.replicate 1000 space

theorem rep1000 : List.replicate 1000 space = sp1000 := by unfold sp1000; rfl

/-- `List.take` on texts, folded (`jsimp`'s `List.take_succ` would unroll a literal count). -/
@[irreducible] def takeK (n : Nat) (l : JStr) : JStr := l.take n

theorem take_eq_takeK (n : Nat) (l : JStr) : l.take n = takeK n l := by unfold takeK; rfl

/-! ## Lists of strings -/

theorem forall2_len {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, Forall2 R l1 l2 → l1.length = l2.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [forall2_len h]

theorem forall2_jstr_get {σ : State} :
    ∀ {xs : List Value} {ts : List JStr}, Forall2 (JStrAt σ) xs ts →
      ∀ k, k < ts.length → ∃ y, xs[k]? = some (.ref y) ∧ σ.heap y = some (.str (ts.getD k []))
  | [], [], .nil, k, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _ :: _, .cons hx _, 0, _ => by
    obtain ⟨y, rfl, hy⟩ := hx
    exact ⟨y, rfl, hy⟩
  | _ :: _, _ :: _, .cons _ hr, k + 1, h => by
    obtain ⟨y, h1, h2⟩ := forall2_jstr_get hr k (by simp at h; omega)
    exact ⟨y, by simpa using h1, by simpa using h2⟩

theorem textsAt_get {σ : State} {a : Addr} {ts : List JStr} (h : TextsAt σ a ts 0) :
    ∃ xs, σ.heap a = some (.array (.cls "java.lang.String") xs) ∧ xs.length = ts.length ∧
      Forall2 (JStrAt σ) xs ts := by
  obtain ⟨xs, h1, h2⟩ := h
  refine ⟨xs, ?_, forall2_len h2, h2⟩
  simpa using h1

theorem recsAt_len {α : Type} {R : State → Value → Option α → Prop} {σ : State} {a : Addr} {ts : List α}
    (h : RecsAt R σ a ts) : ts.length < 2147483648 := by
  obtain ⟨et, xs, -, hl, hf⟩ := h
  rw [← forall2_len hf]; exact hl

/-! ## The lengths of the record texts -/

theorem zuI_length (v : Int) (n : Nat) : (zuI v n).length = n := zpadStr_length _ _

theorem zsI_length (v : Int) {n : Nat} (h : 1 ≤ n) : (zsI v n).length = n := by
  simp only [zsI, List.length_append, zpadStr_length, List.length_singleton]; omega

theorem xrefTextR_length (t : XrefR) : (xrefTextR t).length = 50 := by
  simp only [xrefTextR, List.length_append, fixStr_length, zuI_length]

theorem custTextR_length (t : CustR) : (custTextR t).length = 500 := by
  simp only [custTextR, List.length_append, fixStr_length, zuI_length]

theorem acctTextR_length (t : AcctR) : (acctTextR t).length = 300 := by
  simp only [acctTextR, List.length_append, fixStr_length, zuI_length, zsI_length _ (by decide : 1 ≤ 12)]

theorem getD_map_len {α : Type} {f : α → JStr} {l : List α} {n k : Nat} (hf : ∀ a, (f a).length = n)
    (hk : k < l.length) : ((l.map f).getD k []).length = n := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]
  exact hf _

theorem T2_len (g : RunG) {k : Nat} (hk : k < g.T2.length) : (g.T2.getD k []).length = 50 := by
  have : k < g.xrs.length := by simpa [RunG.T2] using hk
  exact getD_map_len xrefTextR_length this

theorem T3_len (g : RunG) {k : Nat} (hk : k < g.T3.length) : (g.T3.getD k []).length = 500 := by
  have : k < g.crs.length := by simpa [RunG.T3] using hk
  exact getD_map_len custTextR_length this

theorem T4_len (g : RunG) {k : Nat} (hk : k < g.T4.length) : (g.T4.getD k []).length = 300 := by
  have : k < g.ars.length := by simpa [RunG.T4] using hk
  exact getD_map_len acctTextR_length this


/-! ## The searches by their first match -/

theorem find?_some_of_first {α : Type} {p : α → Bool} (d : α) :
    ∀ {l : List α} {i : Nat}, i < l.length → (∀ k, k < i → p (l.getD k d) = false) →
      p (l.getD i d) = true → l.find? p = some (l.getD i d)
  | [], _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | a :: l, 0, _, _, hp => by
    simp only [List.getD_cons_zero] at hp ⊢
    simp only [List.find?_cons, hp]
  | a :: l, i + 1, hi, hk, hp => by
    have h0 := hk 0 (Nat.succ_pos _)
    simp only [List.getD_cons_zero] at h0
    simp only [List.getD_cons_succ] at hp ⊢
    simp only [List.find?_cons, h0]
    exact find?_some_of_first d (l := l) (by simp at hi; omega)
      (fun k hk' => by simpa using hk (k + 1) (by omega)) hp

theorem find?_none_of_all {α : Type} {p : α → Bool} (d : α) :
    ∀ {l : List α}, (∀ k, k < l.length → p (l.getD k d) = false) → l.find? p = none
  | [], _ => rfl
  | a :: l, hk => by
    have h0 := hk 0 (by simp only [List.length_cons]; omega)
    simp only [List.getD_cons_zero] at h0
    simp only [List.find?_cons, h0]
    exact find?_none_of_all d (l := l) (fun k hk' => by simpa using hk (k + 1) (by simp; omega))

theorem getD_zip {α β : Type} (da : α) (db : β) :
    ∀ {l1 : List α} {l2 : List β} {i : Nat}, i < l1.length → i < l2.length →
      (l1.zip l2).getD i (da, db) = (l1.getD i da, l2.getD i db)
  | [], _, _, h1, _ => absurd h1 (Nat.not_lt_zero _)
  | _ :: _, [], _, _, h2 => absurd h2 (Nat.not_lt_zero _)
  | _ :: _, _ :: _, 0, _, _ => rfl
  | _ :: l1, _ :: l2, i + 1, h1, h2 => by
    simpa using getD_zip da db (l1 := l1) (l2 := l2) (i := i) (by simp at h1; omega) (by simp at h2; omega)

theorem custFind_some {keys texts : List JStr} {k : JStr} {i : Nat} (hl : keys.length = texts.length)
    (hi : i < keys.length) (hne : ∀ m, m < i → keys.getD m [] ≠ k) (heq : keys.getD i [] = k) :
    custFind keys texts k = some (texts.getD i []) := by
  unfold custFind
  have hi2 : i < texts.length := by omega
  have hz : i < (keys.zip texts).length := by simp only [List.length_zip]; omega
  have hf := find?_some_of_first (p := fun p : JStr × JStr => decide (p.1 = k)) ([], []) hz
    (fun m hm => by rw [getD_zip [] [] (by omega) (by omega)]; simpa using hne m hm)
    (by rw [getD_zip [] [] hi hi2]; simpa using heq)
  rw [hf, getD_zip [] [] hi hi2]; rfl

theorem custFind_none {keys texts : List JStr} {k : JStr} (hl : keys.length = texts.length)
    (hne : ∀ m, m < keys.length → keys.getD m [] ≠ k) : custFind keys texts k = none := by
  unfold custFind
  have hf := find?_none_of_all (p := fun p : JStr × JStr => decide (p.1 = k)) ([], [])
    (l := keys.zip texts) (fun m hm => by
      simp only [List.length_zip] at hm
      rw [getD_zip [] [] (by omega) (by omega)]; simpa using hne m (by omega))
  rw [hf]; rfl

theorem acctFind_some {texts : List JStr} {k : JStr} {i : Nat} (hi : i < texts.length)
    (hne : ∀ m, m < i → sub (texts.getD m []) 0 11 ≠ k) (heq : sub (texts.getD i []) 0 11 = k) :
    acctFind texts k = some (texts.getD i []) := by
  unfold acctFind
  exact find?_some_of_first [] hi (fun m hm => by simpa using hne m hm) (by simpa using heq)

theorem acctFind_none {texts : List JStr} {k : JStr}
    (hne : ∀ m, m < texts.length → sub (texts.getD m []) 0 11 ≠ k) : acctFind texts k = none := by
  unfold acctFind
  exact find?_none_of_all [] (fun m hm => by simpa using hne m hm)

theorem drop_getD_cons {α : Type} {l : List α} {j : Nat} (d : α) (h : j < l.length) :
    l.drop j = l.getD j d :: l.drop (j + 1) := by
  rw [List.getD_eq_getElem _ _ h]; exact List.drop_eq_getElem_cons h

end EquivLean.Modernize.Cbstm03a.Java.Seg3
