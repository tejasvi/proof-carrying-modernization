import EquivLean.Modernize.Cbact04c.JavaRunLib

/-!
# CBACT04C → Java: record objects field by field

`JRecAt` (the generated statement's relation between a Java record object and field values) taken
apart into the facts the symbolic execution reads: for a valid record, each numeric field holds
the `long` of its value, each alphanumeric field a string holding the CP037 text of its bytes.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-! ## Valid records, field by field -/

theorem valid_num {s : Schema} {vals : List EquivLean.Cobol.Rec.FVal} (hv : s.Valid vals) {i : Nat}
    (hi : i < s.fields.length) {fmt : Cobol.NumFmt}
    (hk : (s.fields.getD i default).desc.kind = .num fmt) :
    vals.getD i default = .num (Model.numOf (vals.getD i default)) ∧
      fmt.Holds {} (Model.numOf (vals.getD i default)) := by
  have h := Forall2.getD hv i hi
  cases hval : vals.getD i default with
  | num v =>
    rw [hval] at h
    obtain ⟨fmt', hk', -, -, hh, -⟩ := h
    rw [hk] at hk'
    cases hk'
    exact ⟨rfl, hh⟩
  | str bs =>
    rw [hval] at h
    obtain ⟨⟨j, hj⟩, -⟩ := h
    rw [hk] at hj
    cases hj

theorem valid_str {s : Schema} {vals : List EquivLean.Cobol.Rec.FVal} (hv : s.Valid vals) {i : Nat}
    (hi : i < s.fields.length) {j : Bool}
    (hk : (s.fields.getD i default).desc.kind = .alnum j) :
    vals.getD i default = .str (Model.strOf (vals.getD i default)) ∧
      (Model.strOf (vals.getD i default)).length = (s.fields.getD i default).desc.len := by
  have h := Forall2.getD hv i hi
  cases hval : vals.getD i default with
  | num v =>
    rw [hval] at h
    obtain ⟨fmt', hk', -⟩ := h
    rw [hk] at hk'
    cases hk'
  | str bs =>
    rw [hval] at h
    exact ⟨rfl, h.2⟩

/-! ## Record objects, field by field -/

theorem jrec_obj {s : Schema} {cls : ClassName} {σ : State} {v : Value} {vals : List EquivLean.Cobol.Rec.FVal}
    (h : JRecAt s cls σ v vals) :
    ∃ x fs, v = .ref x ∧ σ.heap x = some (.plain cls fs) ∧
      Forall2 (fun f val => jFieldAt σ cls fs f val) s.fields vals := h

theorem jfield_num {s : Schema} {cls : ClassName} {σ : State} {fs : List (FieldKey × Value)}
    {vals : List EquivLean.Cobol.Rec.FVal} (h : Forall2 (fun f val => jFieldAt σ cls fs f val) s.fields vals)
    (hv : s.Valid vals) {i : Nat} (hi : i < s.fields.length) {fmt : Cobol.NumFmt}
    (hk : (s.fields.getD i default).desc.kind = .num fmt) :
    Fields.get fs (cls, (s.fields.getD i default).jname) =
      some (.long (BitVec.ofInt 64 (Model.numOf (vals.getD i default)))) := by
  have h1 := Forall2.getD h i hi
  have h2 := (valid_num hv hi hk).1
  rw [h2] at h1
  exact h1

theorem jfield_str {s : Schema} {cls : ClassName} {σ : State} {fs : List (FieldKey × Value)}
    {vals : List EquivLean.Cobol.Rec.FVal} (h : Forall2 (fun f val => jFieldAt σ cls fs f val) s.fields vals)
    (hv : s.Valid vals) {i : Nat} (hi : i < s.fields.length) {j : Bool}
    (hk : (s.fields.getD i default).desc.kind = .alnum j) :
    ∃ x, Fields.get fs (cls, (s.fields.getD i default).jname) = some (.ref x) ∧
      σ.heap x = some (.str (cp037Str (Model.strOf (vals.getD i default)))) := by
  have h1 := Forall2.getD h i hi
  have h2 := (valid_str hv hi hk).1
  rw [h2] at h1
  obtain ⟨sv, hs, x, rfl, hx⟩ := h1
  exact ⟨x, hs, hx⟩

end EquivLean.Modernize.Cbact04c.Java
