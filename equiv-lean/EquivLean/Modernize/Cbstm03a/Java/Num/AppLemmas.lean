import EquivLean.Modernize.Cbstm03a.Java.Iface1

/-! # `app`'s texts: `indexOf` bounds, `appStr` cases -/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

theorem indexOf_go_bounds (pat : JStr) :
    ∀ (s : JStr) (i : Nat), -1 ≤ JStr.indexOf.go pat s i ∧ JStr.indexOf.go pat s i ≤ i + s.length
  | [], i => by
    unfold JStr.indexOf.go
    split <;> omega
  | c :: rest, i => by
    have ih := indexOf_go_bounds pat rest (i + 1)
    unfold JStr.indexOf.go
    simp only [List.length_cons]
    split <;> omega

theorem indexOf_ge (s t : JStr) : -1 ≤ JStr.indexOf s t := (indexOf_go_bounds t s 0).1

theorem indexOf_le (s t : JStr) : JStr.indexOf s t ≤ s.length := by
  have := (indexOf_go_bounds t s 0).2
  unfold JStr.indexOf
  omega

theorem indexOf_le_eq (s t : JStr) : (JStr.indexOf s t ≤ (s.length : Int)) = True := eq_true (indexOf_le s t)

theorem indexOf_bmod (s t : JStr) (h : s.length < 2147483648) :
    (JStr.indexOf s t).bmod 4294967296 = JStr.indexOf s t := by
  have h1 := indexOf_ge s t
  have h2 := indexOf_le s t
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem indexOf_emod (s t : JStr) (h : s.length < 2147483648) (h0 : 0 ≤ JStr.indexOf s t) :
    JStr.indexOf s t % 4294967296 = JStr.indexOf s t := by
  have h2 := indexOf_le s t
  exact Int.emod_eq_of_lt h0 (by omega)

theorem room_eq (L C : Nat) (hL : L < C) (hC : C < 4294967296) : (4294967296 - L + C) % 4294967296 = C - L := by
  omega

end EquivLean.Modernize.Cbstm03a.Java
