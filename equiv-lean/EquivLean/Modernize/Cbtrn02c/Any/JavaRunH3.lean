import EquivLean.Modernize.Cbtrn02c.Any.JavaRunH2

/-!
# CBTRN02C → Java: `zonedSigned`

`zonedSigned(v, n)`: the leading `n - 1` digits of `|v|`, zero-padded, then the last digit
overpunched with the sign (`{`, `A`…`I` for `+0`…`+9`, `}`, `J`…`R` for `-0`…`-9`), against the
contract of `padNum`.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

def padNumSig : MethodSig :=
  ⟨"Cbtrn02c", .cls "java.lang.String", "padNum", [.prim .long, .prim .int]⟩

theorem padNum_sat : Sat Gen.prog padNumRef padNumSpec := padNum_vc.sat

set_option maxHeartbeats 0 in
theorem padNum_ok : ContractOK Gen.prog padNumSig padNumSpec := by
  jcontract_ok [padNum_sat]

/-- What `zonedSigned(v, n)` returns. -/
def szJ (v : I64) (n : Nat) : JStr :=
  zpadJ (v.toInt.natAbs / 10) (n - 1) ++ [overJ (decide (v.toInt < 0)) (v.toInt.natAbs % 10)]

abbrev zonedSignedRef : MethodRef := Gen.Cbtrn02c.«zonedSigned(long,int)».ref

def szCallees : Contracts := [(padNumSig, padNumSpec)]

def zonedSignedSpec : Spec := Spec.of
  (fun args σ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧
     -9223372036854775808 < v.toInt ∧ 1 ≤ n.toInt ∧ n.toInt < 2147483647 ∧
     σ.initOf "Cbtrn02c" = .done)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (szJ v n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem zonedSigned_vc :
    MethodVC Gen.prog szCallees.env 0 zonedSignedRef zonedSignedSpec [] 60 := by
  jverify [zonedSignedSpec, szCallees, padNumSig, padNumSpec, Grows, szJ, overJ,
    EquivLean.Cobol.Rec.overpunch, digitJ, zpadJ_length, zpadJ_getElem?_pred, zpadJ_take_pred,
    i32_toNat_sub_one, i32_toNat_eq, digit_sub48, cmp_zero_nonneg_iff,
    valueOfArg_char, idx_pred, jstrLitT, jchar_rt, jchar_rt', Native.valueOfArg, JType.isRef,
    valueOfObj_eq, valueOfObjN_ref, idx_sub48, over_pos_lit, over_neg_lit]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip


end EquivLean.Modernize.Cbtrn02c.Java
