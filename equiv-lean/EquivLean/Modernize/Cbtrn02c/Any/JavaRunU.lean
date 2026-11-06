import EquivLean.Modernize.Cbtrn02c.Any.JavaRunH3

/-!
# CBTRN02C → Java: record objects as the helpers read them

A daily transaction object of the statement (`JRecAt DalytranRecord …` with valid field values)
has the fields `dalytranText` reads (`DtFields`), and its text is the model's record text.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-! ## Texts as UTF-16 units -/

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
  simp [jline, cp037Str, cp037Unit, cp037Code]

theorem fitJ_full (cs : JStr) (n : Nat) (h : cs.length = n) : fitJ cs n = cs := by
  subst h
  apply List.ext_getElem
  · simp [fitJ]
  · intro i h1 h2
    simp [fitJ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-! ## Field values of an object -/

theorem toInt_ofInt_of_natAbs {n : Int} (h : n.natAbs < 10 ^ 18) :
    (BitVec.ofInt 64 n).toInt = n := by
  rw [BitVec.toInt_ofInt]
  rw [Int.bmod_def]
  split <;> omega

theorem minval_lt {n : Int} (h : n.natAbs < 10 ^ 18) :
    -9223372036854775808 < (BitVec.ofInt 64 n).toInt := by
  rw [toInt_ofInt_of_natAbs h]; omega

/-- An alphanumeric field of a record object: a string holding the CP037 text. -/
theorem str_field {σ : State} {cls : ClassName} {fs : List (FieldKey × Value)} {f : Field}
    {val : EquivLean.Cobol.Rec.FVal} (hk : f.desc.kind = .alnum false) (hv : f.Valid val)
    (hj : jFieldAt σ cls fs f val) :
    ∃ bs y, val = .str bs ∧ Fields.get fs (cls, f.jname) = some (.ref y) ∧
      σ.heap y = some (.str (cp037Str bs)) ∧ bs.length = f.desc.len := by
  cases val with
  | num n =>
    obtain ⟨fmt, hk', -⟩ := hv
    rw [hk] at hk'; cases hk'
  | str bs =>
    obtain ⟨s, hs, y, rfl, hy⟩ := hj
    exact ⟨bs, y, rfl, hs, hy, hv.2⟩

/-- A numeric field of a record object: a `long` holding the value. -/
theorem num_field {σ : State} {cls : ClassName} {fs : List (FieldKey × Value)} {f : Field}
    {fmt : Cobol.NumFmt} {val : EquivLean.Cobol.Rec.FVal} (hk : f.desc.kind = .num fmt)
    (hv : f.Valid val) (hj : jFieldAt σ cls fs f val) :
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

theorem szJ_of (n : Int) (h : n.natAbs < 10 ^ 18) :
    jline (zpad 10 (n.natAbs / 10) ++ [overpunch (decide (n < 0)) (n.natAbs % 10)]) =
      szJ (BitVec.ofInt 64 n) 11 := by
  rw [szJ, toInt_ofInt_of_natAbs h, jline_append, jline_zpad]
  rfl

theorem cp037Str_length (bs : List UInt8) : (cp037Str bs).length = bs.length := by
  simp [cp037Str]

end EquivLean.Modernize.Cbtrn02c.Java
