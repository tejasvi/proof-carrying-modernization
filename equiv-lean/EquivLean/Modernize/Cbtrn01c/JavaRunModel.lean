import EquivLean.Modernize.Cbtrn01c.JavaProof

/-!
# CBTRN01C → Java: the lines of `run`, step by step

`Model.displayText` cut at the points of the read loop: the lines after `k` reads (`preL`), at the
loop head (`headL`, with the lookups of the last record once more after the end of file), before
the lookups of the current record (`befL`), and the lines of a found cross-reference (`xrefL`).
-/

open EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn01c.Java

def startL : List Nat := Model.txt "START OF EXECUTION OF PROGRAM CBTRN01C"
def endL : List Nat := Model.txt "END OF EXECUTION OF PROGRAM CBTRN01C"

/-- The lines of one transaction: its record, then what its lookups display. -/
def stepL (xs accs : List (List FVal)) (t : List FVal) : List (List Nat) :=
  Model.DalytranRecord.textS t :: Model.lookupText xs accs t

/-- The lines after the first `k` transactions. -/
def preL (trans xs accs : List (List FVal)) (k : Nat) : List (List Nat) :=
  startL :: (trans.take k).flatMap (stepL xs accs)

/-- The record area after the first `k` reads. -/
def curT (trans : List (List FVal)) (k : Nat) : List FVal := (trans.take k).getLast?.getD Model.dal0

/-- The lines at the head of the read loop after `k` reads; `e`: the end of file was met (the
lookups of the last record done once more). -/
def headL (trans xs accs : List (List FVal)) (k : Nat) (e : Bool) : List (List Nat) :=
  preL trans xs accs k ++ (if e then Model.lookupText xs accs (curT trans k) else [])

/-- The lines before the lookups of the current record. -/
def befL (trans xs accs : List (List FVal)) (k : Nat) (e : Bool) : List (List Nat) :=
  if e then preL trans xs accs k
  else preL trans xs accs (k - 1) ++ [Model.DalytranRecord.textS (curT trans k)]

/-- The card number of a record matches the cross-reference record `x`. -/
def cardMatch (t : List FVal) (x : List FVal) : Bool :=
  Model.strOf (x.getD 0 default) == Model.strOf (t.getD 10 default)

/-- The account id of the account record `a` is the one of the cross-reference record `x`. -/
def acctMatch (x : List FVal) (a : List FVal) : Bool :=
  Model.numOf (a.getD 0 default) == Model.numOf (x.getD 2 default)

/-- The lines of a cross-reference record found by the lookup. -/
def xrefL (x : List FVal) : List (List Nat) :=
  [Model.txt "SUCCESSFUL READ OF XREF",
    Model.txt "CARD NUMBER: " ++ (Model.strOf (x.getD 0 default)).map cp037Code,
    Model.txt "ACCOUNT ID : " ++ zpad 11 (Model.numOf (x.getD 2 default)).natAbs,
    Model.txt "CUSTOMER ID: " ++ zpad 9 (Model.numOf (x.getD 1 default)).natAbs]

theorem lookupText_none {xs accs : List (List FVal)} {t : List FVal}
    (h : xs.find? (cardMatch t) = none) :
    Model.lookupText xs accs t =
      [Model.txt "INVALID CARD NUMBER FOR XREF",
        Model.txt "CARD NUMBER " ++ (Model.strOf (t.getD 10 default)).map cp037Code ++
          Model.txt " COULD NOT BE VERIFIED. SKIPPING TRANSACTION ID-" ++
          (Model.strOf (t.getD 0 default)).map cp037Code] := by
  unfold Model.lookupText
  have h' : xs.find? (fun x => Model.strOf (x.getD 0 default) == Model.strOf (t.getD 10 default)) =
      none := h
  rw [h']

theorem lookupText_some_none {xs accs : List (List FVal)} {t x : List FVal}
    (h : xs.find? (cardMatch t) = some x) (ha : accs.find? (acctMatch x) = none) :
    Model.lookupText xs accs t =
      xrefL x ++ [Model.txt "INVALID ACCOUNT NUMBER FOUND",
        Model.txt "ACCOUNT " ++ zpad 11 (Model.numOf (x.getD 2 default)).natAbs ++
          Model.txt " NOT FOUND"] := by
  unfold Model.lookupText
  have h' : xs.find? (fun x => Model.strOf (x.getD 0 default) == Model.strOf (t.getD 10 default)) =
      some x := h
  have ha' : accs.find? (fun a => Model.numOf (a.getD 0 default) ==
      Model.numOf (x.getD 2 default)) = none := ha
  rw [h']
  simp only [ha', xrefL]

theorem lookupText_some_some {xs accs : List (List FVal)} {t x a : List FVal}
    (h : xs.find? (cardMatch t) = some x) (ha : accs.find? (acctMatch x) = some a) :
    Model.lookupText xs accs t = xrefL x ++ [Model.txt "SUCCESSFUL READ OF ACCOUNT FILE"] := by
  unfold Model.lookupText
  have h' : xs.find? (fun x => Model.strOf (x.getD 0 default) == Model.strOf (t.getD 10 default)) =
      some x := h
  have ha' : accs.find? (fun a => Model.numOf (a.getD 0 default) ==
      Model.numOf (x.getD 2 default)) = some a := ha
  rw [h']
  simp only [ha', xrefL]

theorem curT_succ {trans : List (List FVal)} {k : Nat} (hk : k < trans.length) :
    curT trans (k + 1) = trans[k] := by
  unfold curT
  rw [List.take_succ_eq_append_getElem hk]
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.getD_some]

theorem preL_succ {trans xs accs : List (List FVal)} {k : Nat} (hk : k < trans.length) :
    preL trans xs accs (k + 1) = preL trans xs accs k ++ stepL xs accs trans[k] := by
  unfold preL
  rw [List.take_succ_eq_append_getElem hk]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append]

theorem headL_zero (trans xs accs : List (List FVal)) : headL trans xs accs 0 false = [startL] := by
  simp [headL, preL]

/-- A record read: its line follows the lines of the loop head. -/
theorem befL_read {trans xs accs : List (List FVal)} {k : Nat} (hk : k < trans.length) :
    befL trans xs accs (k + 1) false =
      headL trans xs accs k false ++ [Model.DalytranRecord.textS trans[k]] := by
  simp [befL, headL, curT_succ hk]

/-- The end of file: no line. -/
theorem befL_eof (trans xs accs : List (List FVal)) :
    befL trans xs accs trans.length true = headL trans xs accs trans.length false := by
  simp [befL, headL]

/-- After the lookups: the lines of the loop head. -/
theorem befL_lookup {trans xs accs : List (List FVal)} {k : Nat} {e : Bool}
    (hk : e = false → 1 ≤ k) (hk2 : k ≤ trans.length) :
    befL trans xs accs k e ++ Model.lookupText xs accs (curT trans k) = headL trans xs accs k e := by
  cases e with
  | true => simp [befL, headL]
  | false =>
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := hk rfl; omega⟩
    have hj : j < trans.length := by omega
    simp only [befL, headL, Bool.false_eq_true, ↓reduceIte, List.append_nil, Nat.add_sub_cancel]
    rw [preL_succ hj, curT_succ hj]
    simp [stepL]

/-- The last lines: the end message after the loop. -/
theorem headL_final (trans xs accs : List (List FVal)) :
    headL trans xs accs trans.length true ++ [endL] = Model.displayText trans xs accs := by
  simp only [headL, preL, curT, Model.displayText, startL, endL, List.take_length, ↓reduceIte,
    List.cons_append, List.append_assoc]
  rfl

/-- `find?` after a prefix without match. -/
theorem find?_of_take {α : Type} {p : α → Bool} {l : List α} {i : Nat} (hi : i < l.length)
    (hno : ∀ x ∈ l.take i, p x = false) (hp : p l[i] = true) : l.find? p = some l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hp
      simp [List.find?, hp]
    | succ i =>
      have ha : p a = false := hno a (by simp)
      simp only [List.find?, ha]
      exact ih (by simpa using hi) (fun x hx => hno x (by simp [hx])) (by simpa using hp)

theorem find?_none_of_take {α : Type} {p : α → Bool} {l : List α}
    (hno : ∀ x ∈ l.take l.length, p x = false) : l.find? p = none := by
  rw [List.take_length] at hno
  exact List.find?_eq_none.2 fun x hx => by simp [hno x hx]

theorem take_succ_no {α : Type} {p : α → Bool} {l : List α} {i : Nat} (hi : i < l.length)
    (hno : ∀ x ∈ l.take i, p x = false) (hp : p l[i] = false) :
    ∀ x ∈ l.take (i + 1), p x = false := by
  intro x hx
  rw [List.take_succ_eq_append_getElem hi] at hx
  rcases List.mem_append.1 hx with h | h
  · exact hno x h
  · simp at h; rw [h]; exact hp

end EquivLean.Modernize.Cbtrn01c.Java
