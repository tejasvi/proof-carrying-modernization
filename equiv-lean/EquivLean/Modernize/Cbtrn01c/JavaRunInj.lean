import EquivLean.Modernize.Cbtrn01c.JavaRunState

/-!
# CBTRN01C → Java: comparisons

CP037 strings are equal exactly when their bytes are (`cp037Str_inj`), and the `long`s of two
DISPLAY values exactly when the values are: the comparisons of the searches are the model's
`cardMatch` and `acctMatch`.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

theorem cp037Char_toNat_lt (b : UInt8) : (Cobol.Codepage.cp037Char b).toNat < 256 := by
  have h := (Cobol.Codepage.cp037_check b.toNat b.toNat_lt).2.2.1
  unfold Cobol.Codepage.cp037Char
  rw [Cobol.Codepage.Char.toNat_ofNat_lt256 _ h]
  exact h

theorem cp037Unit_inj {a b : UInt8} (h : cp037Unit a = cp037Unit b) : a = b := by
  unfold cp037Unit at h
  have ha := cp037Char_toNat_lt a
  have hb := cp037Char_toNat_lt b
  have h2 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  have e1 := Cobol.Codepage.cp037Byte_cp037Char a
  have e2 := Cobol.Codepage.cp037Byte_cp037Char b
  unfold Cobol.Codepage.cp037Byte at e1 e2
  rw [h2] at e1
  rw [e1] at e2
  exact Option.some.inj e2

theorem cp037Str_inj : ∀ {a b : List UInt8}, cp037Str a = cp037Str b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [cp037Str] at h
  | _ :: _, [], h => by simp [cp037Str] at h
  | x :: xs, y :: ys, h => by
    simp only [cp037Str, List.map_cons, List.cons.injEq] at h
    rw [cp037Unit_inj h.1, cp037Str_inj (a := xs) (b := ys) h.2]

theorem cardMatch_iff (t x : List EquivLean.Cobol.Rec.FVal) :
    cardMatch t x = true ↔
      cp037Str (Model.strOf (t.getD 10 default)) = cp037Str (Model.strOf (x.getD 0 default)) := by
  unfold cardMatch
  rw [beq_iff_eq]
  constructor
  · intro h; rw [h]
  · intro h; exact (cp037Str_inj h).symm

theorem ofInt_inj {u w : Int} (hu : u.natAbs < 10 ^ 18) (hw : w.natAbs < 10 ^ 18)
    (h : BitVec.ofInt 64 u = BitVec.ofInt 64 w) : u = w := by
  have := congrArg BitVec.toInt h
  rwa [toInt_ofInt_of_natAbs hu, toInt_ofInt_of_natAbs hw] at this

theorem acctMatch_iff (x a : List EquivLean.Cobol.Rec.FVal)
    (hu : (Model.numOf (a.getD 0 default)).natAbs < 10 ^ 18)
    (hw : (Model.numOf (x.getD 2 default)).natAbs < 10 ^ 18) :
    acctMatch x a = true ↔
      BitVec.ofInt 64 (Model.numOf (a.getD 0 default)) =
        BitVec.ofInt 64 (Model.numOf (x.getD 2 default)) := by
  unfold acctMatch
  rw [beq_iff_eq]
  constructor
  · intro h; rw [h]
  · intro h; exact ofInt_inj hu hw h

end EquivLean.Modernize.Cbtrn01c.Java
