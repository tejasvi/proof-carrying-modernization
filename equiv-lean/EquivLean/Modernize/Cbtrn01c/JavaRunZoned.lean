import EquivLean.Modernize.Cbtrn01c.JavaRunHelpers

/-!
# CBTRN01C → Java: `signedZoned`

`signedZoned(v, n)`: the leading `n - 1` digits of `|v|`, zero-padded, then the last digit
overpunched with the sign (`{`, `A`…`I` for `+0`…`+9`, `}`, `J`…`R` for `-0`…`-9`), against the
contract of `digits`.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

def digitsSig : MethodSig :=
  ⟨"Cbtrn01c", .cls "java.lang.String", "digits", [.prim .long, .prim .int]⟩

theorem digits_sat : Sat Gen.prog digitsRef digitsSpec := digits_vc.sat

set_option maxHeartbeats 0 in
theorem digits_ok : ContractOK Gen.prog digitsSig digitsSpec := by
  jcontract_ok [digits_sat]

/-- What `signedZoned(v, n)` returns. -/
def szJ (v : I64) (n : Nat) : JStr :=
  zpadJ (v.toInt.natAbs / 10) (n - 1) ++ [overJ (decide (v.toInt < 0)) (v.toInt.natAbs % 10)]

abbrev signedZonedRef : MethodRef := Gen.Cbtrn01c.«signedZoned(long,int)».ref

def szCallees : Contracts := [(digitsSig, digitsSpec)]

def signedZonedSpec : Spec := Spec.of
  (fun args σ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧
     -9223372036854775808 < v.toInt ∧ 1 ≤ n.toInt ∧ n.toInt < 2147483647 ∧
     σ.initOf "Cbtrn01c" = .done)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (szJ v n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn01c" = σ.initOf "Cbtrn01c")

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem signedZoned_vc :
    MethodVC Gen.prog szCallees.env 0 signedZonedRef signedZonedSpec [] 60 := by
  jverify [signedZonedSpec, szCallees, digitsSig, digitsSpec, Grows, szJ, overJ,
    EquivLean.Cobol.Rec.overpunch, digitJ, zpadJ_length, zpadJ_getElem?_pred, zpadJ_take_pred,
    i32_toNat_sub_one, i32_toNat_eq, digit_sub48, ofNat32_digit_eq_zero, cmp_zero_nonneg_iff,
    valueOfArg_char, idx_pred, evalDynamic, concatRecipe, Native.valueOfArg, Native.valueOfObj,
    Native.primStr, JType.isRef, jstrLitT, Native.valueOfObjN, Native.nObjStr, over_pos_char,
    over_neg_char]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn01c.Java
