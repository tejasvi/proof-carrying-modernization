import EquivLean.Modernize.Cbstm03a.Java.Run5.Thin168

/-!
# CBSTM03A → Java `run`, thin VC: the paths from statement 168 to the next (virtual) cut points

`s168t`, `s173t`: the paths of `s168`, `s173` with the thin handler (callee postconditions assumed) and the cut
points asserting the variant: at 168 (the next card number) the cards loop's measure one card smaller, at 179 the
transactions loop's below it, at the virtual cut points `MidT`, `TailT 0`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_trans)
open EquivLean.Modernize.Cbstm03a.Java

namespace EquivLean.Modernize.Cbstm03a.Java.Seg5

section Paths

attribute [-simp] List.reduceReplicate

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- From the cards loop's head to the tail or to the cut after `memRead` (thin). -/
theorem s168t (g : RunG) (args : List Value) (σ0 : State) (hpre : RunPre g args σ0) (fr : Frame) (σ : State)
    (hI : inv168 g args σ0 fr σ) (v : Nat) (hv : runVar 168 args σ0 fr σ ≤ v) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA ((173, MidT g args σ0 v) :: CLt g args σ0 v 0)
      (fun _ => True) 14 168 fr σ := by
  obtain ⟨res, ld, ls, lh, L, oc, j, crJmp, total, n, pF, hX, hj, hmodel, hc32, h17, h21, htot, hc1, hn, hpF⟩ := hI
  have h18 := xctx_cr hX
  have h7 := xctx_get7 hX
  obtain ⟨mem, trct, h16, -, hS, -, -⟩ := xctx_load hX
  have hinitC : σ.initOf "Cbstm03a" = .done := by
    rw [State.initOf_eq_of_inits (xctx_base hX).2.1]; exact hpre.2.2.2.2.2.1.1
  obtain ⟨hcr0, hcr1, -⟩ := xctx_ldBounded hX
  have hK := Kept.intro (And.intro hpre (And.intro hX (And.intro hj (And.intro hmodel (And.intro hc32
    (And.intro h21 (And.intro htot (And.intro hn (And.intro hpF (And.intro hS hv))))))))))
  clear hX hmodel hc32 hpF hS hpre h21 htot hn hv
  jvc [runCallees, runInv, CLt, tailCutsT, TI, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, ite_nat_ne, grows_split, StrOk]
  all_goals first
    | (obtain ⟨-, hX, hj, hmodel, -, h21, htot, -, hpF, -, hv⟩ := Kept.elim hK
       exact t168_exit hX hj hmodel h21 htot hpF hinitC
        (fun k a0 a4 a17 a19 a22 a26 a32 a33 => by
          simp [Frame.get_setLocal, a0, a4, a17, a19, a22, a26, a32, a33])
        (by assumption) (by assumption) hv)
    | (obtain ⟨hpre, hX, hj, hmodel, hc32, h21, htot, hn, hpF, hS, hv⟩ := Kept.elim hK
       obtain ⟨x, hrv, hxh, hgk, hi, hs⟩ := memRead_inst (by assumption) hS
       subst hrv
       exact t168_mid hpre hX hj hmodel hc32 h17 h21 htot hc1 hn hpF (by omega) hinitC
        (fun k a0 a4 a17 a19 a22 a26 a32 a33 => by
          simp [Frame.get_setLocal, a0, a4, a17, a19, a22, a26, a32, a33])
        (by simp [Frame.get_setLocal]) (by simp [Frame.get_setLocal]) (by simp [Frame.get_setLocal])
        hxh (growsK_elim hgk) hi hs hv)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- From the cut after `memRead`: the tail, the next card number, or the transactions loop (thin). -/
theorem s173t (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (fr : Frame) (σ : State)
    (hJ : MidT g args σ0 v fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA (CLt g args σ0 v 0) (fun _ => True)
      10 173 fr σ := by
  obtain ⟨⟨res, ld, ls, lh, L, oc, j, crJmp, total, n, pF, xm, xc, trct, acp, hK0, h33, hxm, h32, hxc, h17, h24,
    htr, hvs, h7, hinitC, hcpS, hcpH⟩, hv⟩ := hJ
  have h18 := xctx_cr (Kept.elim hK0).1
  obtain ⟨hcr0, hcr1, -⟩ := xctx_ldBounded (Kept.elim hK0).1
  generalize hM : memRd L.m (cardOffJ crJmp).toInt 16 = M at hxm
  generalize hcard : sub (fixStr (g.T2.getD j []) 1000) 0 16 = card at hxc
  have hML : M.length = 16 := by rw [← hM]; exact memRd_length _ _ _
  have hcl : card.length = 16 := by rw [← hcard]; simp [sub]
  have hK := Kept.intro (And.intro (Kept.elim hK0) (And.intro hM (And.intro hcard hv)))
  clear hK0 hM hcard hv
  jvc [runCallees, runInv, CLt, tailCutsT, TI, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, ite_nat_ne, grows_split, StrOk, StrNN, CP037At]
  -- (dispatched by case: a variant goal tried with the tail's closer runs into `runVar`'s numerals)
  case normal.isTrue =>
    obtain ⟨⟨hX, hj, hmodel, -, h21, htot, -, hle, hn, hpF⟩, hM, hcard, hv⟩ := Kept.elim hK
    exact t173_exit hX hj hmodel h21 htot hle hn hpF hM hcard hxm hxc (by assumption) hinitC
      (fun k a0 a4 a17 a19 a22 a26 a32 a33 => by
        simp [Frame.get_setLocal, a0, a4, a17, a19, a22, a26, a32, a33]) hv
  case normal.isFalse.isFalse =>
    obtain ⟨⟨-, -, -, -, -, -, hc1, hle, -, -⟩, -, -, hv⟩ := Kept.elim hK
    exact t173_skip
      (fun k a0 a4 a17 a19 a22 a26 a32 a33 => by
        simp [Frame.get_setLocal, a0, a4, a17, a19, a22, a26, a32, a33])
      h17 h18 (get_setLocal_same _ _ _) hle hcr1 hc1 hv
  case normal.isFalse.isTrue.normal =>
    obtain ⟨hrv, rfl⟩ := getTrct_inst (by assumption) htr
    subst hrv
    obtain ⟨⟨hX, -, -, -, -, -, -, hle, -, -⟩, -, -, hv⟩ := Kept.elim hK
    obtain ⟨cnt, hcnt, hc0, hc9⟩ := trctGet_bounded crJmp (xctx_ldBounded hX).2.2.2.2
    exact t173_match
      (fun k a0 a4 a17 a19 a22 a26 a32 a33 => by
        simp [Frame.get_setLocal, a0, a4, a17, a19, a22, a26, a32, a33])
      (by simp [Frame.get_setLocal]) h17 h18 (by simp [Frame.get_setLocal, hcnt]) (get_setLocal_same _ _ _)
      hle hc0 hc9 hv

end Paths

end EquivLean.Modernize.Cbstm03a.Java.Seg5
