import EquivLean.Modernize.Cbtrn01c.JavaRunFormat

/-!
# CBTRN01C → Java: records as `formatDalytran` reads them

A transaction record object of the statement (`JRecAt DalytranRecord …` with valid field values)
is a record `formatDalytran` accepts (`DalOk`), and its line is the record text of the model
(`Model.DalytranRecord.textS`) as UTF-16 units.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn01c.Java

/-! ## Digits as UTF-16 units -/

theorem jline_append (a b : List Nat) : jline (a ++ b) = jline a ++ jline b := by
  simp [jline]

theorem jline_zpad (c m : Nat) : jline (zpad m c) = zpadJ c m := by
  induction m generalizing c with
  | zero => rfl
  | succ m ih =>
    simp only [zpad, toDigits_succ, List.map_append, List.map_singleton] at ih ⊢
    rw [zpadJ, ← ih]
    simp [jline, digitJ]

theorem jline_cp037 (bs : List UInt8) : jline (bs.map cp037Code) = cp037Str bs := by
  rw [cp037Str_eq_map]; rfl

/-! ## Field values of an object -/

theorem toInt_ofInt_of_natAbs {n : Int} (h : n.natAbs < 10 ^ 18) :
    (BitVec.ofInt 64 n).toInt = n := by
  rw [BitVec.toInt_ofInt]
  rw [Int.bmod_def]
  split <;> omega

/-- An alphanumeric field of a record object: a string holding the CP037 text. -/
theorem str_field {σ : State} {cls : ClassName} {fs : List (FieldKey × Value)} {f : Field}
    {val : EquivLean.Cobol.Rec.FVal} (hk : f.desc.kind = .alnum false) (hv : f.Valid val)
    (hj : jFieldAt σ cls fs f val) :
    ∃ bs y, val = .str bs ∧ Fields.get fs (cls, f.jname) = some (.ref y) ∧
      σ.heap y = some (.str (cp037Str bs)) := by
  cases val with
  | num n =>
    obtain ⟨fmt, hk', -⟩ := hv
    rw [hk] at hk'; cases hk'
  | str bs =>
    obtain ⟨s, hs, y, rfl, hy⟩ := hj
    exact ⟨bs, y, rfl, hs, hy⟩

/-- A numeric field of a record object: a `long` holding the value. -/
theorem num_field {σ : State} {cls : ClassName} {fs : List (FieldKey × Value)} {f : Field}
    {fmt : Cobol.NumFmt} {val : EquivLean.Cobol.Rec.FVal} (hk : f.desc.kind = .num fmt) (hv : f.Valid val)
    (hj : jFieldAt σ cls fs f val) :
    ∃ n, val = .num n ∧ Fields.get fs (cls, f.jname) = some (.long (BitVec.ofInt 64 n)) ∧
      fmt.Holds {} n ∧ 0 < fmt.digits ∧ fmt.digits ≤ 18 := by
  cases val with
  | str bs =>
    obtain ⟨⟨j, hj'⟩, -⟩ := hv
    rw [hk] at hj'; cases hj'
  | num n =>
    obtain ⟨fmt', hk', hd0, hd1, hh, -⟩ := hv
    rw [hk] at hk'; cases hk'
    exact ⟨n, rfl, hj, hh, hd0, hd1⟩

/-- A DISPLAY value of at most 18 digits is less than `10^18` in absolute value. -/
theorem natAbs_lt_of_holds {fmt : Cobol.NumFmt} {n : Int} (hu : fmt.usage = .display)
    (hh : fmt.Holds {} n) (hd : fmt.digits ≤ 18) : n.natAbs < 10 ^ 18 := by
  unfold Cobol.NumFmt.Holds at hh
  have hb : fmt.fullBinary {} = false := by
    unfold Cobol.NumFmt.fullBinary; simp [hu]
  rw [hb] at hh
  simp only [Bool.false_eq_true, ↓reduceIte] at hh
  have : 10 ^ fmt.digits ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) hd
  omega

end EquivLean.Modernize.Cbtrn01c.Java
