import EquivLean.Modernize.Cbstm03a.Java.Num.EbcLemmas

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr argText space fixStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java

attribute [local irreducible] ebcIdx ebcGo cp037Table

theorem toInt_ofNat32 (L : Nat) (h : L < 2147483648) : (BitVec.ofNat 32 L).toInt = L := by
  have := BitVec.toInt_eq_toNat_cond (BitVec.ofNat 32 L)
  simp only [BitVec.toNat_ofNat, Nat.reducePow] at this
  split at this <;> omega

/-- The loop's facts: both texts, the longer length `n` (local `$i0` 3), the index `i` (local 4), the scan so far;
the state is unchanged. Locals: `a` 7, `b` 8. -/
def ebcLoop (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (atChars : Bool) : Prop :=
  ∀ av bv, args = [av, bv] →
  ∃ (xa xb : Addr) (sa sb : JStr) (i n : I32), av = .ref xa ∧ bv = .ref xb ∧
    σ.heap xa = some (.str sa) ∧ σ.heap xb = some (.str sb) ∧ sa.length < 2147483648 ∧ sb.length < 2147483648 ∧
    fr.get 7 = some (.ref xa) ∧ fr.get 8 = some (.ref xb) ∧ fr.get 4 = some (.int i) ∧ fr.get 3 = some (.int n) ∧
    n.toInt = ((max sa.length sb.length : Nat) : Int) ∧ 0 ≤ i.toInt ∧
    (if atChars then i.toInt < n.toInt ∧
        fr.get 0 = some (.int (BitVec.setWidth 32 (sa.getD i.toInt.toNat space))) ∧
        fr.get 1 = some (.int (BitVec.setWidth 32 (sb.getD i.toInt.toNat space)))
      else i.toInt ≤ n.toInt) ∧
    ebcCmp sa sb = ebcScan ((fixStr sa (max sa.length sb.length)).drop i.toInt.toNat)
      ((fixStr sb (max sa.length sb.length)).drop i.toInt.toNat) ∧
    σ = σ0 ∧ CP037At σ0

/-- Cut points: the loop head (statement 12) and the comparison of the two characters (statement 23;
`$c5` local 0, `$c6` local 1). -/
def ebcCompareInv : Invariants :=
  [(12, fun args σ0 fr σ => ebcLoop args σ0 fr σ false), (23, fun args σ0 fr σ => ebcLoop args σ0 fr σ true)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
theorem ebcCompare_vc : MethodVC Gen.prog ebcCompareCallees.env 0 ebcCompareRef ebcCompareSpec ebcCompareInv 60 := by
  jverify [ebcCompareSpec, ebcCompareInv, ebcLoop, ebcCompareCallees, ebcSig, ebcSpec, StrNN, argText, strOf,
    toInt_ofNat32, List.getD_eq_default, space_setWidth, setWidth32_inj, setWidth32_toNat, ebc_ofNat_inj, ebc_toInt,
    ebcCmp_self, ebcCmp_ne, fixStr_drop, ebcScan, scan_end, CP037At]


end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.ebcCompare_vc
