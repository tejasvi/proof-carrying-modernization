import EquivLean.Modernize.Cbstm03a.Java.Run6.Lem
import EquivLean.Modernize.Cbstm03a.Java.RunTerm

/-!
# CBSTM03A → Java `run`, statement 179: the variant on the thin paths

From the transactions loop, `runVar` decreases: back to statement 179 with `trJmp + 1` (`(cnt + 2 − trJmp)` one
less, `crJmp`, `crCnt`, `cnt` and `xrefSt[0]` unchanged), or out to the cards loop with `crJmp + 1` once
`trJmp = cnt + 1` (`var179_exit`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg6

theorem locL_long {fr : Frame} {i : Nat} {v : I64} (h : fr.get i = some (.long v)) : locL fr i = v.toInt := by
  unfold locL; rw [h]

theorem locL_eq {fr fr' : Frame} {i : Nat} (h : fr'.get i = fr.get i) : locL fr' i = locL fr i := by
  unfold locL; rw [h]

theorem arr0_eq {σ σ' : State} {fr fr' : Frame} {st2 : Addr} (h2 : fr.get 2 = some (.ref st2))
    (h2' : fr'.get 2 = fr.get 2) (hst : σ'.heap st2 = σ.heap st2) : arr0 σ' fr' 2 = arr0 σ fr 2 := by
  unfold arr0; rw [h2', h2]; simp only [hst]

/-- Back to statement 179 with `trJmp + 1`. -/
theorem var179_body {args : List Value} {σ0 σ σ' : State} {fr fr' : Frame} {st2 : Addr} {cnt trJmp : I64}
    (h2 : fr.get 2 = some (.ref st2)) (hst : σ'.heap st2 = σ.heap st2)
    (hf : ∀ i, i ∉ LoopLocals → fr'.get i = fr.get i) (hf17 : fr'.get 17 = fr.get 17)
    (hf19 : fr'.get 19 = fr.get 19) (hf22 : fr'.get 22 = some (.long (trJmp + 1#64)))
    (h19 : fr.get 19 = some (.long cnt)) (h22 : fr.get 22 = some (.long trJmp))
    (ht0 : 0 ≤ trJmp.toInt) (ht2 : trJmp.toInt < 10000) (hle : trJmp.toInt ≤ cnt.toInt) :
    runVar 179 args σ0 fr' σ' < runVar 179 args σ0 fr σ := by
  have e2 := arr0_eq h2 (fr_eq hf 2) hst
  have e18 := locL_eq (fr_eq hf 18)
  have e17 := locL_eq hf17
  have e19 := locL_eq hf19
  have e22' : locL fr' 22 = trJmp.toInt + 1 := by rw [locL_long hf22, i64_toInt_add_one ht0 ht2]
  have e22 : locL fr 22 = trJmp.toInt := locL_long h22
  have e19v : locL fr 19 = cnt.toInt := locL_long h19
  simp only [runVar]
  rw [e2, e18, e17, e19, e22', e22, e19v]
  omega

/-- Out to the cards loop (statement 168) with `crJmp + 1`, after the last transaction (`trJmp = cnt + 1`). -/
theorem var179_exit {args : List Value} {σ0 σ : State} {fr fr' : Frame} {crJmp crCnt cnt trJmp : I64}
    (hf : ∀ i, i ∉ LoopLocals → fr'.get i = fr.get i) (hf17 : fr'.get 17 = some (.long (crJmp + 1#64)))
    (h17 : fr.get 17 = some (.long crJmp)) (h18 : fr.get 18 = some (.long crCnt))
    (h19 : fr.get 19 = some (.long cnt)) (h22 : fr.get 22 = some (.long trJmp))
    (hc0 : 0 ≤ crJmp.toInt) (hc1 : crJmp.toInt < 10000) (hc2 : crJmp.toInt ≤ crCnt.toInt)
    (hgt : cnt.toInt < trJmp.toInt) (ht2 : trJmp.toInt ≤ cnt.toInt + 1) :
    runVar 168 args σ0 fr' σ < runVar 179 args σ0 fr σ := by
  have e2 : arr0 σ fr' 2 = arr0 σ fr 2 := by unfold arr0; rw [fr_eq hf 2]
  have e18 : locL fr' 18 = crCnt.toInt := by rw [locL_eq (fr_eq hf 18), locL_long h18]
  have e17' : locL fr' 17 = crJmp.toInt + 1 := by rw [locL_long hf17, i64_toInt_add_one hc0 hc1]
  simp only [runVar]
  rw [e2, e18, e17', locL_long h17, locL_long h18, locL_long h19, locL_long h22]
  have e : crCnt.toInt + 1 - (crJmp.toInt + 1) = crCnt.toInt - crJmp.toInt := by omega
  rw [e]
  omega

end EquivLean.Modernize.Cbstm03a.Java.Seg6
