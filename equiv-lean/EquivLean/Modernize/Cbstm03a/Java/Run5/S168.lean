import EquivLean.Modernize.Cbstm03a.Java.Run5.T168

/-!
# CBSTM03A → Java `run`: the paths from statement 168 to the next (virtual) cut points

`s168`: the cards loop's head; card number `crJmp` past `crCnt` → the tail (196); otherwise the card's text read by
`memRead` → the virtual cut point 173. `s173`: `ebcCompare` and `equals` of the card's text with the record's card
number: after it in EBCDIC order → the tail; another card → 168 with the next card number; this card → `getTrct`,
the transactions loop (179).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_trans)
open EquivLean.Modernize.Cbstm03a.Java

namespace EquivLean.Modernize.Cbstm03a.Java.Seg5

section Paths

attribute [-simp] List.reduceReplicate

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- From the cards loop's head to the tail or to the cut after `memRead`. -/
theorem s168 (g : RunG) (args : List Value) (σ0 : State) (hpre : RunPre g args σ0) (fr : Frame) (σ : State)
    (hI : inv168 g args σ0 fr σ) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA ((173, MidJ g σ0) :: CL g args σ0 0)
      ((runSpecG g).post args σ0) 14 168 fr σ := by
  obtain ⟨res, ld, ls, lh, L, oc, j, crJmp, total, n, pF, hX, hj, hmodel, hc32, h17, h21, htot, hc1, hn, hpF⟩ := hI
  have h18 := xctx_cr hX
  have h7 := xctx_get7 hX
  obtain ⟨mem, trct, h16, -, hS, -, -⟩ := xctx_load hX
  have hinitC : σ.initOf "Cbstm03a" = .done := by
    rw [State.initOf_eq_of_inits (xctx_base hX).2.1]; exact hpre.2.2.2.2.2.1.1
  obtain ⟨hcr0, hcr1, -⟩ := xctx_ldBounded hX
  have hK := Kept.intro (And.intro hpre (And.intro hX (And.intro hj (And.intro hmodel (And.intro hc32
    (And.intro h21 (And.intro htot (And.intro hn (And.intro hpF hS)))))))))
  clear hX hmodel hc32 hpF hS hpre h21 htot hn
  jvc [runCallees, runInv, runSpecG, CL, tailCuts, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, ite_nat_ne, grows_split, StrOk]
  all_goals first
    | (obtain ⟨-, -, -, -, -, -, -, -, -, hS⟩ := Kept.elim hK
       exact ⟨_, hS⟩)
    | (obtain ⟨-, hX, hj, hmodel, -, h21, htot, -, hpF, -⟩ := Kept.elim hK
       exact s168_exit hX hj hmodel h21 htot hpF hinitC
        (fun k a0 a4 a17 a19 a22 a26 a32 a33 => by
          simp [Frame.get_setLocal, a0, a4, a17, a19, a22, a26, a32, a33])
        (by assumption) (by assumption))
    | (rename_i v σ' hA
       obtain ⟨hpre, hX, hj, hmodel, hc32, h21, htot, hn, hpF, hS⟩ := Kept.elim hK
       obtain ⟨x, hv, -, hxh, hgk, -, -, hi, hs⟩ := hA _ _ _ _ rfl rfl rfl hS
       subst hv
       exact s168_mid hpre hX hj hmodel hc32 h17 h21 htot hc1 hn hpF (by omega) hinitC
        (fun k a0 a4 a17 a19 a22 a26 a32 a33 => by
          simp [Frame.get_setLocal, a0, a4, a17, a19, a22, a26, a32, a33])
        (by simp [Frame.get_setLocal]) (by simp [Frame.get_setLocal]) (by simp [Frame.get_setLocal])
        hxh (growsK_elim hgk) hi hs)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- From the cut after `memRead`: the tail, the next card number, or the transactions loop. -/
theorem s173 (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (hJ : MidJ g σ0 fr σ) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA (CL g args σ0 0) ((runSpecG g).post args σ0)
      10 173 fr σ := by
  obtain ⟨res, ld, ls, lh, L, oc, j, crJmp, total, n, pF, xm, xc, trct, acp, hK0, h33, hxm, h32, hxc, h17, h24,
    htr, hvs, h7, hinitC, hcpS, hcpH⟩ := hJ
  generalize hM : memRd L.m (cardOffJ crJmp).toInt 16 = M at hxm
  generalize hcard : sub (fixStr (g.T2.getD j []) 1000) 0 16 = card at hxc
  have hML : M.length = 16 := by rw [← hM]; exact memRd_length _ _ _
  have hcl : card.length = 16 := by rw [← hcard]; simp [sub]
  have hK := Kept.intro (And.intro (Kept.elim hK0) (And.intro hM hcard))
  clear hK0 hM hcard
  jvc [runCallees, runInv, runSpecG, CL, tailCuts, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, ite_nat_ne, grows_split, StrOk, StrNN, CP037At]
  all_goals first
    | (obtain ⟨⟨hX, hj, hmodel, -, h21, htot, -, hle, hn, hpF⟩, hM, hcard⟩ := Kept.elim hK
       exact mid_exit hX hj hmodel h21 htot hle hn hpF hM hcard hxm hxc (by assumption) hinitC
        (fun k a0 a4 a17 a19 a22 a26 a32 a33 => by
          simp [Frame.get_setLocal, a0, a4, a17, a19, a22, a26, a32, a33]))
    | (obtain ⟨⟨hX, hj, hmodel, hc32, h21, htot, hc1, hle, hn, hpF⟩, hM, hcard⟩ := Kept.elim hK
       exact mid_skip hX hj hmodel hc32 h21 htot hc1 hle hn hpF hM hcard hxm hxc (by assumption) (by assumption)
        (fun k a0 a4 a17 a19 a22 a26 a32 a33 => by
          simp [Frame.get_setLocal, a0, a4, a17, a19, a22, a26, a32, a33])
        (get_setLocal_same _ _ _) (by simp [Frame.get_setLocal]))
    | (rename_i v σ' hA
       dsimp only at hA
       obtain ⟨hv, rfl⟩ := hA _ _ _ rfl rfl htr
       subst hv
       obtain ⟨⟨hX, hj, hmodel, hc32, h21, htot, hc1, hle, hn, hpF⟩, hM, hcard⟩ := Kept.elim hK
       exact mid_match hX hj hmodel hc32 h17 h21 htot hc1 hle hn hpF hM hcard hxm hxc (by assumption) rfl
        (fun k a0 a4 a17 a19 a22 a26 a32 a33 => by
          simp [Frame.get_setLocal, a0, a4, a17, a19, a22, a26, a32, a33])
        (by simp [Frame.get_setLocal]) (by simp [Frame.get_setLocal]) (by simp [Frame.get_setLocal])
        (get_setLocal_same _ _ _))

end Paths

end EquivLean.Modernize.Cbstm03a.Java.Seg5
