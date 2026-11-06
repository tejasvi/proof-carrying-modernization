import EquivLean.Modernize.Cbact04c.JavaRunRec

/-!
# CBACT04C → Java: the record objects `run` reads, field by field

For a valid category record, account, cross-reference or disclosure group held by a Java
object (`JRecAt`), the fields the symbolic execution reads: numbers as `long`s of the model's
values (in the picture's range), strings as the CP037 text of the model's bytes.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

theorem natAbs_lt_iff {v : Int} {n : Nat} : v.natAbs < n ↔ -(n : Int) < v ∧ v < n := by
  rcases Int.natAbs_eq v with h | h <;> constructor <;> intro h' <;> omega

theorem holds_display {fmt : Cobol.NumFmt} (hu : fmt.usage = .display) {v : Int}
    (h : fmt.Holds {} v) : v.natAbs < 10 ^ fmt.digits ∧ (fmt.signed = false → 0 ≤ v) := by
  unfold Cobol.NumFmt.Holds Cobol.NumFmt.fullBinary at h
  simp only [hu] at h
  exact h

/-- The `FILLER` of a category record. -/
def tFill (t : List EquivLean.Cobol.Rec.FVal) : List UInt8 := Model.strOf (t.getD 4 default)

/-- What `run` reads of a category record object. -/
def TcbFacts (σ : State) (y : Addr) (t : List EquivLean.Cobol.Rec.FVal) : Prop :=
  ∃ fs tyA fiA, σ.heap y = some (.plain "Cbact04c$TranCatBalRecord" fs) ∧
    Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatAcctId") =
      some (.long (BitVec.ofInt 64 (Model.tAcct t))) ∧
    Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatTypeCd") = some (.ref tyA) ∧
    σ.heap tyA = some (.str (cp037Str (Model.tType t))) ∧
    Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatCd") =
      some (.long (BitVec.ofInt 64 (Model.tCat t))) ∧
    Fields.get fs ("Cbact04c$TranCatBalRecord", "tranCatBal") =
      some (.long (BitVec.ofInt 64 (Model.tBal t))) ∧
    Fields.get fs ("Cbact04c$TranCatBalRecord", "filler1") = some (.ref fiA) ∧
    σ.heap fiA = some (.str (cp037Str (tFill t))) ∧
    0 ≤ Model.tAcct t ∧ Model.tAcct t < 100000000000 ∧ 0 ≤ Model.tCat t ∧
    Model.tCat t < 10000 ∧ -100000000000 < Model.tBal t ∧ Model.tBal t < 100000000000 ∧
    (Model.tType t).length = 2 ∧ (tFill t).length = 22

theorem tcb_facts {σ : State} {y : Addr} {t : List EquivLean.Cobol.Rec.FVal}
    (h : JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ (.ref y) t)
    (hv : TranCatBalRecord.Valid t) : TcbFacts σ y t := by
  obtain ⟨x, fs, hx, hheap, hf⟩ := jrec_obj h
  cases hx
  have n0 := jfield_num hf hv (i := 0) (by decide) (fmt := {digits := 11}) (by decide)
  have n2 := jfield_num hf hv (i := 2) (by decide) (fmt := {digits := 4}) (by decide)
  have n3 := jfield_num hf hv (i := 3) (by decide) (fmt := {digits := 11, scale := 2, signed := true})
    (by decide)
  obtain ⟨tyA, s1, s1h⟩ := jfield_str hf hv (i := 1) (by decide) (j := false) (by decide)
  obtain ⟨fiA, s4, s4h⟩ := jfield_str hf hv (i := 4) (by decide) (j := false) (by decide)
  have r0 := holds_display rfl (valid_num hv (i := 0) (by decide) (fmt := {digits := 11})
    (by decide)).2
  have r2 := holds_display rfl (valid_num hv (i := 2) (by decide) (fmt := {digits := 4})
    (by decide)).2
  have r3 := holds_display rfl (valid_num hv (i := 3) (by decide)
    (fmt := {digits := 11, scale := 2, signed := true}) (by decide)).2
  have l1 := (valid_str hv (i := 1) (by decide) (j := false) (by decide)).2
  have l4 := (valid_str hv (i := 4) (by decide) (j := false) (by decide)).2
  simp only [Nat.reducePow] at r0 r2 r3
  have a0 := Int.natAbs_eq (Model.numOf (t.getD 0 default))
  have a2 := Int.natAbs_eq (Model.numOf (t.getD 2 default))
  have a3 := Int.natAbs_eq (Model.numOf (t.getD 3 default))
  have q0 := r0.2 trivial
  have q2 := r2.2 trivial
  refine ⟨fs, tyA, fiA, hheap, n0, s1, s1h, n2, n3, s4, s4h, ?_, ?_, ?_, ?_, ?_, ?_, l1, l4⟩ <;>
    simp only [Model.tAcct, Model.tCat, Model.tBal] <;> omega

end EquivLean.Modernize.Cbact04c.Java
