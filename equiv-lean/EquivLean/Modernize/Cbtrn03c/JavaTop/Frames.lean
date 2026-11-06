import EquivLean.Modernize.Cbtrn03c.JavaTop.TopLib

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java, top layer: frame lemmas for the input files

The record objects, their strings and the arrays of the input files stay across the working-state
helpers (`KeepsNonWs`) and across allocations and callee frames (`Agree`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

/-- The heap facts a record object needs kept. -/
structure HeapKeep (σ σ' : State) : Prop where
  strs : StrMono σ σ'
  plains : ∀ x c fs, σ.heap x = some (.plain c fs) → c ≠ wsC → σ'.heap x = some (.plain c fs)
  arrays : ∀ x et xs, σ.heap x = some (.array et xs) → σ'.heap x = some (.array et xs)

theorem HeapKeep.of_keeps {σ σ' : State} (h : KeepsNonWs σ σ') : HeapKeep σ σ' :=
  ⟨h.2.1, h.2.2.1, h.2.2.2⟩

theorem HeapKeep.of_agree {σ σ' : State} (h : Agree σ σ') : HeapKeep σ σ' :=
  ⟨fun _ _ hx => heap_agree h hx, fun _ _ _ hx _ => heap_agree h hx, fun _ _ _ hx => heap_agree h hx⟩

theorem jFieldAt_keep {σ σ' : State} (hk : HeapKeep σ σ') {cls : ClassName}
    {fs : List (FieldKey × Value)} {f : Field} {v : EquivLean.Cobol.Rec.FVal}
    (h : jFieldAt σ cls fs f v) : jFieldAt σ' cls fs f v := by
  cases v with
  | num n => exact h
  | str bs =>
    obtain ⟨s, h1, x, rfl, hx⟩ := h
    exact ⟨_, h1, x, rfl, hk.strs x _ hx⟩

theorem forall2_mono {α β : Type} {R S : α → β → Prop} (hRS : ∀ a b, R a b → S a b) :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → Forall2 S xs ys
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (hRS _ _ h) (forall2_mono hRS hs)

theorem JRecAt.keep {σ σ' : State} (hk : HeapKeep σ σ') {s : Schema} {cls : ClassName}
    (hc : cls ≠ wsC) {v : Value} {vals : List EquivLean.Cobol.Rec.FVal} (h : JRecAt s cls σ v vals) :
    JRecAt s cls σ' v vals := by
  obtain ⟨x, fs, rfl, hx, hf⟩ := h
  exact ⟨x, fs, rfl, hk.plains x cls fs hx hc, forall2_mono (fun _ _ h => jFieldAt_keep hk h) hf⟩

/-- An array of records stays. -/
theorem fileAt_keep {σ σ' : State} (hk : HeapKeep σ σ') {s : Schema} {cls : ClassName}
    (hc : cls ≠ wsC) {a : Addr} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (h : ∃ et xs, σ.heap a = some (.array et xs) ∧ xs.length < 2147483648 ∧
      Forall2 (JRecAt s cls σ) xs vals) :
    ∃ et xs, σ'.heap a = some (.array et xs) ∧ xs.length < 2147483648 ∧
      Forall2 (JRecAt s cls σ') xs vals := by
  obtain ⟨et, xs, ha, hl, hf⟩ := h
  exact ⟨et, xs, hk.arrays a et xs ha, hl, forall2_mono (fun _ _ h => JRecAt.keep hk hc h) hf⟩

theorem TransactFileAt.keeps {σ σ' : State} {a : Addr} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (h : TransactFileAt σ a vals) (hk : KeepsNonWs σ σ') : TransactFileAt σ' a vals :=
  fileAt_keep (HeapKeep.of_keeps hk) (by decide) h
theorem TransactFileAt.agree {σ σ' : State} {a : Addr} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (h : TransactFileAt σ a vals) (ha : Agree σ σ') : TransactFileAt σ' a vals :=
  fileAt_keep (HeapKeep.of_agree ha) (by decide) h
theorem XrefFileAt.keeps {σ σ' : State} {a : Addr} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (h : XrefFileAt σ a vals) (hk : KeepsNonWs σ σ') : XrefFileAt σ' a vals :=
  fileAt_keep (HeapKeep.of_keeps hk) (by decide) h
theorem XrefFileAt.agree {σ σ' : State} {a : Addr} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (h : XrefFileAt σ a vals) (ha : Agree σ σ') : XrefFileAt σ' a vals :=
  fileAt_keep (HeapKeep.of_agree ha) (by decide) h
theorem TrantypeFileAt.keeps {σ σ' : State} {a : Addr} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (h : TrantypeFileAt σ a vals) (hk : KeepsNonWs σ σ') : TrantypeFileAt σ' a vals :=
  fileAt_keep (HeapKeep.of_keeps hk) (by decide) h
theorem TrantypeFileAt.agree {σ σ' : State} {a : Addr} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (h : TrantypeFileAt σ a vals) (ha : Agree σ σ') : TrantypeFileAt σ' a vals :=
  fileAt_keep (HeapKeep.of_agree ha) (by decide) h
theorem TrancatgFileAt.keeps {σ σ' : State} {a : Addr} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (h : TrancatgFileAt σ a vals) (hk : KeepsNonWs σ σ') : TrancatgFileAt σ' a vals :=
  fileAt_keep (HeapKeep.of_keeps hk) (by decide) h
theorem TrancatgFileAt.agree {σ σ' : State} {a : Addr} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (h : TrancatgFileAt σ a vals) (ha : Agree σ σ') : TrancatgFileAt σ' a vals :=
  fileAt_keep (HeapKeep.of_agree ha) (by decide) h
theorem DateParmsFileAt.keeps {σ σ' : State} {a : Addr} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (h : DateParmsFileAt σ a vals) (hk : KeepsNonWs σ σ') : DateParmsFileAt σ' a vals :=
  fileAt_keep (HeapKeep.of_keeps hk) (by decide) h
theorem DateParmsFileAt.agree {σ σ' : State} {a : Addr} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (h : DateParmsFileAt σ a vals) (ha : Agree σ σ') : DateParmsFileAt σ' a vals :=
  fileAt_keep (HeapKeep.of_agree ha) (by decide) h

attribute [jframe] TransactFileAt.keeps TransactFileAt.agree XrefFileAt.keeps XrefFileAt.agree
  TrantypeFileAt.keeps TrantypeFileAt.agree TrancatgFileAt.keeps TrancatgFileAt.agree
  DateParmsFileAt.keeps DateParmsFileAt.agree

end EquivLean.Modernize.Cbtrn03c.Java.Top
