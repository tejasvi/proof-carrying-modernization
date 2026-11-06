import EquivLean.Modernize.Cbstm03b.Java.Base

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03b.Java

/-- At the loop head (statement 8): positions `i+1 …` of the array hold the digits written so far, and the rest
of the number is `l`. Locals: `l6` 1, `i0` 4, `$r0` 6. -/
def zeroPadInv : Invariants := [(8, fun args σ0 fr σ => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
  ∃ arr i l xs, fr.get 4 = some (.int i) ∧ fr.get 1 = some (.long l) ∧ fr.get 6 = some (.ref arr) ∧
    σ.heap arr = some (.array (.prim .char) xs) ∧ xs.length = n.toInt.toNat ∧
    0 ≤ l.toInt ∧ -1 ≤ i.toInt ∧ i.toInt < n.toInt ∧
    zpadStr v.toNat n.toInt.toNat =
      zpadStr l.toNat (i.toInt + 1).toNat ++ Native.charsOf (xs.drop (i.toInt + 1).toNat) ∧
    σ0.next ≤ arr ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem zeroPad_vc : MethodVC Gen.prog (fun _ => none) 0 zeroPadRef zeroPadSpec zeroPadInv 80 := by
  jverify [ite_nat_ne, zeroPadSpec, zeroPadInv, Grows, zpadStr, digitChar, sdiv10_toNat_of_nonneg, sdiv10_nonneg,
    digit_char, drop_set_self]

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.zeroPad_vc
