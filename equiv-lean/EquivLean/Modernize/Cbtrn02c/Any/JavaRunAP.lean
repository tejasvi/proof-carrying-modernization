import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM3s
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunAR
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunO

/-!
# CBTRN02C → Java: the account record after a posting

`acct_post_rec`: the account object holding `a`, with its fields set by `updateAccount`
(`acctPostFs`), holds the model's posted account `Model.postAcct a amt`.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem acctBal_fmt : CardDemo.Cbtrn02c.ACCT_CURR_BAL.fmt.signed = true ∧
    CardDemo.Cbtrn02c.ACCT_CURR_BAL.fmt.usage = .display ∧
    CardDemo.Cbtrn02c.ACCT_CURR_BAL.fmt.digits = 12 := by decide
theorem acctCc_fmt : CardDemo.Cbtrn02c.ACCT_CURR_CYC_CREDIT.fmt.signed = true ∧
    CardDemo.Cbtrn02c.ACCT_CURR_CYC_CREDIT.fmt.usage = .display ∧
    CardDemo.Cbtrn02c.ACCT_CURR_CYC_CREDIT.fmt.digits = 12 := by decide
theorem acctCd_fmt : CardDemo.Cbtrn02c.ACCT_CURR_CYC_DEBIT.fmt.signed = true ∧
    CardDemo.Cbtrn02c.ACCT_CURR_CYC_DEBIT.fmt.usage = .display ∧
    CardDemo.Cbtrn02c.ACCT_CURR_CYC_DEBIT.fmt.digits = 12 := by decide

/-- `(a + b) % 10^12` on the `long`s of two small values is the COBOL `ADD` into a 12-digit item. -/
theorem balJ_ofInt (x y : Int) (hx : x.natAbs < 1000000000000000000) (hy : y.natAbs < 1000000000000000000)
    {f : Cobol.NumFmt} (hf : f.signed = true ∧ f.usage = .display ∧ f.digits = 12) :
    balJ (BitVec.ofInt 64 x) (BitVec.ofInt 64 y) = BitVec.ofInt 64 (Cobol.Sem.fitNum {} f (x + y)).2 := by
  unfold balJ
  rw [fitNum_signed_display hf.1 hf.2.1, hf.2.2]
  have := srem_add_ofInt x y 1000000000000 (by decide) (by decide) hx hy
  simpa using this

theorem lng'_of {σ : State} {w : Addr} {fs : List (FieldKey × Value)} {k : FieldKey} {v : I64}
    (hw : σ.heap w = some (.plain "Cbtrn02c$AccountRecord" fs)) (hk : Fields.get fs k = some (.long v)) :
    lng' σ w k = v := by
  simp [lng', fld', fieldsOf, hw, hk]

set_option maxRecDepth 8000 in
/-- The account object `y` with the fields of `acctWs` after `updateAccount` holds the model's
posted account. -/
theorem acct_post_rec {σ σ' : State} {w y : Addr} {fsy : List (FieldKey × Value)} {a : List EquivLean.Cobol.Rec.FVal}
    {amt : Int} (hr : JRecAt AccountRecord "Cbtrn02c$AccountRecord" σ (.ref w) a)
    (hv : AccountRecord.Valid a) (hy : σ'.heap y = some (.plain "Cbtrn02c$AccountRecord" fsy))
    (hs : SameFields acKeys fsy (acctPostFs (fieldsOf σ w) (lng' σ w acBalKey) (lng' σ w acCcKey)
      (lng' σ w acCdKey) (BitVec.ofInt 64 amt)))
    (hamt : amt.natAbs < 100000000000) (hstr : ∀ v t, JStrAt σ v t → JStrAt σ' v t) :
    JRecAt AccountRecord "Cbtrn02c$AccountRecord" σ' (.ref y) (Model.postAcct a amt) := by
  obtain ⟨hobj, n0, b1, n2, n3, n4, b5, b6, b7, n8, n9, b10, b11, b12, rfl, a0, a2, a3, a4, a8,
    a9⟩ := acctobj_of_rec hr hv
  obtain ⟨x, fs, s1, s5, s6, s7, s10, s11, s12, hxe, hx, g0, g1, t1, g2, g3, g4, g5, t5, g6, t6, g7,
    t7, g8, g9, g10, t10, g11, t11, g12, t12⟩ := hobj
  cases hxe
  rw [fieldsOf_of hx, lng'_of hx g2, lng'_of hx g8, lng'_of hx g9] at hs
  have hamt' : (BitVec.ofInt 64 amt).toInt = amt := toInt_ofInt64 (by omega)
  have eb := balJ_ofInt n2 amt (by omega) (by omega) acctBal_fmt
  have ec := balJ_ofInt n8 amt (by omega) (by omega) acctCc_fmt
  have ed := balJ_ofInt n9 amt (by omega) (by omega) acctCd_fmt
  have get : ∀ k ∈ acKeys, Fields.get fsy k = _ := hs
  refine ⟨y, fsy, rfl, hy, ?_⟩
  simp only [nAt, bAt] at g0 g2 g3 g4 g8 g9 t1 t5 t6 t7 t10 t11 t12
  by_cases hs0 : 0 ≤ amt
  · have hsa : 0 ≤ (BitVec.ofInt 64 amt).toInt := by rw [hamt']; exact hs0
    simp only [acctPostFs, hsa, ↓reduceIte] at get
    simp only [Model.postAcct, Model.aBal, Model.aCC, Model.aCD, Model.numOf, List.getD_cons_succ,
      List.getD_cons_zero, List.set_cons_succ, List.set_cons_zero, hs0, ↓reduceIte]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
      (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))))))))))
    all_goals first
      | (show Fields.get fsy _ = _
         rw [get _ (by simp [acKeys])]
         simp (config := { decide := true }) only [Fields.get_set, ↓reduceIte, nAt, bAt, eb, ec, g0, g3, g4, g9,
           Model.strOf, Model.numOf, List.getD_cons_zero, List.getD_cons_succ])
      | (refine ⟨_, ?_, hstr _ _ ⟨_, rfl, by assumption⟩⟩
         rw [get _ (by simp [acKeys])]
         simp (config := { decide := true }) only [Fields.get_set, ↓reduceIte, g1, g5, g6, g7, g10,
           g11, g12])
  · have hsa : ¬ 0 ≤ (BitVec.ofInt 64 amt).toInt := by rw [hamt']; exact hs0
    simp only [acctPostFs, hsa, ↓reduceIte] at get
    simp only [Model.postAcct, Model.aBal, Model.aCC, Model.aCD, Model.numOf, List.getD_cons_succ,
      List.getD_cons_zero, List.set_cons_succ, List.set_cons_zero, hs0, ↓reduceIte]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
      (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))))))))))
    all_goals first
      | (show Fields.get fsy _ = _
         rw [get _ (by simp [acKeys])]
         simp (config := { decide := true }) only [Fields.get_set, ↓reduceIte, nAt, bAt, eb, ed, g0, g3, g4, g8,
           Model.strOf, Model.numOf, List.getD_cons_zero, List.getD_cons_succ])
      | (refine ⟨_, ?_, hstr _ _ ⟨_, rfl, by assumption⟩⟩
         rw [get _ (by simp [acKeys])]
         simp (config := { decide := true }) only [Fields.get_set, ↓reduceIte, g1, g5, g6, g7, g10,
           g11, g12])

end EquivLean.Modernize.Cbtrn02c.Java
