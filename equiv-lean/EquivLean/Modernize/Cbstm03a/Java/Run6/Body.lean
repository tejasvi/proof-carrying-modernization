import EquivLean.Modernize.Cbstm03a.Java.Run6.WT
import EquivLean.Modernize.Cbstm03a.Java.Run6.BodyClose

/-!
# CBSTM03A → Java `run`, statement 179: the loop body

`trJmp ≤ cnt`: statements 179–193 (`tranOff`, `memRead` of the transaction id and of its rest, `substring` and
`decodeZoned` of the amount, `writeTrans`, `total + amt`, `trunc11`, `trJmp + 1`), back to statement 179 with
`inv179` for `trJmp + 1` (`inv179_of_body`). The symbolic run (`c179_body_run`) sees the table memory and the
`Result` object folded (`SlotsK`, `ResOk`) and `writeTrans`' contract as `writeTransSpecR`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space GrowsK grows_split
  growsK_elim grows_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg6

attribute [-jsimp] List.take_succ JLong.cmp_eq

/-- The total plus an amount of at most 11 digits: no overflow. -/
theorem toInt_add_ofInt {t : I64} {z : Int} (h1 : -100000000000 < t.toInt) (h2 : t.toInt < 100000000000)
    (h3 : -100000000000 < z) (h4 : z < 100000000000) : (t + BitVec.ofInt 64 z).toInt = t.toInt + z := by
  rw [BitVec.toInt_add, i64_ofInt_toInt_small (by omega) (by omega)]
  exact bmod64_self (by omega) (by omega)

/-- The `(int)` of `trJmp cmp cnt` is not positive for `trJmp ≤ cnt`. -/
theorem cmp_le {a b : I64} (h : a.toInt ≤ b.toInt) : (JLong.cmp a b).toInt ≤ 0 := by
  rw [JLong.cmp_eq]
  split
  · decide
  · split
    · decide
    · rename_i h1 h2
      exact absurd (BitVec.toInt_inj.1 (by omega)) h2

theorem tranOff16o_toInt {cr tr : I64} (h1 : 1 ≤ cr.toInt) (h2 : cr.toInt < 10000) (h3 : 1 ≤ tr.toInt)
    (h4 : tr.toInt < 10000) :
    (tranOffJ cr tr + 16).toInt = (cr.toInt - 1) * 3356 + 16 + (tr.toInt - 1) * 334 + 16 := by
  have e3 : (16 : I64).toInt = 16 := by decide
  unfold tranOffJ
  rw [BitVec.toInt_add, tranOff_toInt h1 h2 h3 h4, e3]
  exact bmod64_self' (by omega) (by omega)

theorem tranOffJ_toInt {cr tr : I64} (h1 : 1 ≤ cr.toInt) (h2 : cr.toInt < 10000) (h3 : 1 ≤ tr.toInt)
    (h4 : tr.toInt < 10000) :
    (tranOffJ cr tr).toInt = (cr.toInt - 1) * 3356 + 16 + (tr.toInt - 1) * 334 := by
  unfold tranOffJ; exact tranOff_toInt h1 h2 h3 h4

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
set_option jimple.modelContracts true in
/-- The symbolic run of the loop body: the facts it needs, and what closes the invariant (`hK`). -/
theorem c179_body_run (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (res mem : Addr) (m : Nat → JChar) (crJmp cnt trJmp total : I64)
    (h7 : fr.get 7 = some (.ref res)) (h16 : fr.get 16 = some (.ref mem))
    (h17 : fr.get 17 = some (.long crJmp)) (h19 : fr.get 19 = some (.long cnt))
    (h21 : fr.get 21 = some (.long total)) (h22 : fr.get 22 = some (.long trJmp))
    (hcmp : (JLong.cmp trJmp cnt).toInt ≤ 0)
    (hc1 : 1 ≤ crJmp.toInt) (hc2 : crJmp.toInt < 10000) (ht1 : 1 ≤ trJmp.toInt) (ht2 : trJmp.toInt < 10000)
    (hT1 : -100000000000 < total.toInt) (hT2 : total.toInt < 100000000000)
    (hinit : σ.initOf "Cbstm03a" = .done)
    (hS : SlotsK σ mem m) (hS1 : ∀ σ1, GrowsK σ σ1 → SlotsK σ1 mem m)
    (hRo2 : ∀ σ1 σ2, GrowsK σ σ1 → GrowsK σ1 σ2 → ResOk σ2 res)
    (hz1 : -100000000000 < zonedVal (List.drop 116 (List.take 127
      (memRd m ((crJmp.toInt - 1) * 3356 + 16 + (trJmp.toInt - 1) * 334 + 16) 318))))
    (hz2 : zonedVal (List.drop 116 (List.take 127
      (memRd m ((crJmp.toInt - 1) * 3356 + 16 + (trJmp.toInt - 1) * 334 + 16) 318))) < 100000000000)
    (hK : Kp (∀ (σ1 σ2 σ4 : State) (o : Obj) (fr' : Frame) (tid trest : JStr) (amt : I64),
      GrowsK σ σ1 → GrowsK σ1 σ2 → WTPost (σ2.alloc o).2 σ4 res tid trest amt →
      σ4.inits = σ.inits → σ4.statics = σ.statics →
      (∀ i, i ∉ LoopLocals → fr'.get i = fr.get i) → fr'.get 17 = fr.get 17 → fr'.get 19 = fr.get 19 →
      fr'.get 21 = some (.long (BitVec.ofInt 64 (trunc11Z (total.toInt + zonedVal (sub trest 116 127))))) →
      fr'.get 22 = some (.long (trJmp + 1#64)) →
      tid = memRd m ((crJmp.toInt - 1) * 3356 + 16 + (trJmp.toInt - 1) * 334) 16 →
      trest = memRd m ((crJmp.toInt - 1) * 3356 + 16 + (trJmp.toInt - 1) * 334 + 16) 318 →
      amt = BitVec.ofInt 64 (zonedVal (sub trest 116 127)) →
      inv179 g args σ0 fr' σ4)) :
    runWP g args σ0 179 fr σ := by
  unfold runWP
  jvc [runCallees, runInv, tranOffSpec, memReadSpec, decodeZonedSpec, writeTransSpec_eq, writeTransSpecR,
    trunc11Spec, grows_split, slots_k, StrNN, JStrAt, argText, memRd_length, tranOff_lb, tranOff16_lb,
    resOk_alloc]
  all_goals
    apply (Kp.elim hK)
    all_goals first
      | (with_reducible assumption)
      | (intro i hi
         simp only [LoopLocals, List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
         obtain ⟨a0, -, -, a20, a21, a22, a26, a33, a34, a36⟩ := hi
         simp [Frame.get_setLocal, a0, a20, a21, a22, a26, a33, a34, a36])
      | (simp [Frame.get_setLocal, sub]; done)
      | (with_reducible rfl)

/-- **The loop body**: transaction `trJmp ≤ cnt` of card number `crJmp`, back to statement 179. -/
theorem c179_body (g : RunG) (args : List Value) (σ0 : State) (hpre : RunPre g args σ0) (fr : Frame) (σ : State)
    (res ld ls lh : Addr) (L : LdSt) (oc : JOut) (j : Nat) (crJmp total : I64) (n : Nat) (pF : JOut × I64)
    (cnt trJmp : I64) (acc0 : JOut × I64)
    (hX : XCtx g σ0 fr σ res ld ls lh oc L (j + 1)) (hj : j < g.T2.length)
    (hM : xrefAll g.K3 g.T3 g.T4 L (tailOf pF.1 pF.2) (g.T2.drop (j + 1)) = g.F)
    (h32 : StrLoc σ fr 32 (sub (fixStr (g.T2.getD j []) 1000) 0 16))
    (h17 : fr.get 17 = some (.long crJmp)) (h21 : fr.get 21 = some (.long total)) (hT : TotOk total)
    (hc1 : 1 ≤ crJmp.toInt) (hc2 : crJmp.toInt ≤ L.cr.toInt) (hcn : crJmp.toInt + n = L.cr.toInt + 1)
    (h19 : fr.get 19 = some (.long cnt)) (hcnt : trctGet L.trct crJmp = .long cnt)
    (h22 : fr.get 22 = some (.long trJmp)) (ht1 : 1 ≤ trJmp.toInt) (_ht2 : trJmp.toInt ≤ cnt.toInt + 1)
    (hacc : (oc, total) = transOf L.m crJmp (trJmp.toInt.toNat - 1) acc0)
    (hcards : cardsFrom L.m L.trct L.cr (sub (fixStr (g.T2.getD j []) 1000) 0 16) (n - 1) (crJmp + 1)
      (transOf L.m crJmp cnt.toInt.toNat acc0) = pF)
    (hle : trJmp.toInt ≤ cnt.toInt) :
    runWP g args σ0 179 fr σ := by
  have hLB := xctx_bounded hX
  have hcb := cnt_bounds hLB hcnt
  have hcr := hLB.2.1
  have hR := xctx_res hX
  obtain ⟨mem, h16, hS⟩ : ∃ mem, fr.get 16 = some (.ref mem) ∧ SlotsAt σ mem L.m := by
    obtain ⟨-, -, -, -, -, mem, -, -, -, -, ⟨d16, -, hsl, -, -⟩, -⟩ := hX
    exact ⟨mem, d16, hsl⟩
  have h7 : fr.get 7 = some (.ref res) := by
    obtain ⟨-, -, -, -, -, -, -, -, ⟨-, -, -, -, b7, -⟩, -⟩ := hX
    exact b7
  have hinit : σ.initOf "Cbstm03a" = .done := by
    obtain ⟨-, -, -, -, -, -, -, -, ⟨-, -, -, -, -, -, -, -, -, -, -, hi0, -⟩, -⟩ := hX
    obtain ⟨-, -, -, -, -, ⟨hcp, -⟩, -⟩ := hpre
    rw [State.initOf_eq_of_inits hi0]; exact hcp
  have hc2' : crJmp.toInt < 10000 := by omega
  have ht2' : trJmp.toInt < 10000 := by omega
  obtain ⟨hT1, hT2⟩ := hT
  have hzl : ∀ off : Int, (List.drop 116 (List.take 127 (memRd L.m off 318))).length = 11 := by
    intro off; simp [memRd_length]
  have hz := zonedVal_bound (List.drop 116 (List.take 127
    (memRd L.m ((crJmp.toInt - 1) * 3356 + 16 + (trJmp.toInt - 1) * 334 + 16) 318)))
  rw [hzl] at hz
  have e11 : ((10 ^ 11 : Nat) : Int) = 100000000000 := by norm_num
  rw [e11] at hz
  have hK : Kp (∀ (σ1 σ2 σ4 : State) (o : Obj) (fr' : Frame) (tid trest : JStr) (amt : I64),
      GrowsK σ σ1 → GrowsK σ1 σ2 → WTPost (σ2.alloc o).2 σ4 res tid trest amt →
      σ4.inits = σ.inits → σ4.statics = σ.statics →
      (∀ i, i ∉ LoopLocals → fr'.get i = fr.get i) → fr'.get 17 = fr.get 17 → fr'.get 19 = fr.get 19 →
      fr'.get 21 = some (.long (BitVec.ofInt 64 (trunc11Z (total.toInt + zonedVal (sub trest 116 127))))) →
      fr'.get 22 = some (.long (trJmp + 1#64)) →
      tid = memRd L.m ((crJmp.toInt - 1) * 3356 + 16 + (trJmp.toInt - 1) * 334) 16 →
      trest = memRd L.m ((crJmp.toInt - 1) * 3356 + 16 + (trJmp.toInt - 1) * 334 + 16) 318 →
      amt = BitVec.ofInt 64 (zonedVal (sub trest 116 127)) →
      inv179 g args σ0 fr' σ4) := by
    apply Kp.intro
    intro σ1 σ2 σ4 o fr' tid trest amt g1 g2 hwt hini hsta hf hf17 hf19 hf21 hf22 htid htrest hamt
    have hG3 : Grows σ (σ2.alloc o).2 :=
      grows_trans (growsK_elim g1) (grows_trans (growsK_elim g2) (grows_alloc σ2 o))
    have hR3 := resAtL_grows hR hG3
    obtain ⟨hR4, hk34⟩ := wtPost_elim hwt hR3
    have hk : KeepsRes res ld ls lh σ σ4 := keepsRes_trans (keepsRes_of_grows hG3) hk34
    have hsub : sub trest 116 127 = List.drop 116 (List.take 127
        (memRd L.m ((crJmp.toInt - 1) * 3356 + 16 + (trJmp.toInt - 1) * 334 + 16) 318)) := by
      rw [htrest]; rfl
    have hadd : (total + amt).toInt = total.toInt + zonedVal (sub trest 116 127) := by
      rw [hamt, hsub]
      exact toInt_add_ofInt hT1 hT2 hz.1 hz.2
    refine inv179_of_body hX hj hM h32 h17 hc1 hc2 hcn h19 hcnt ht1 hacc hcards hle σ4 fr' tid trest amt hk hR4
      hini hsta hf hf17 hf19 ?_ hf22 ?_ ?_ hamt
    · rw [hf21, hadd]
    · rw [htid, tranOffJ_toInt hc1 hc2' ht1 ht2']
    · rw [htrest, tranOff16o_toInt hc1 hc2' ht1 ht2']
  have hRo2 : ∀ σ1 σ2, GrowsK σ σ1 → GrowsK σ1 σ2 → ResOk σ2 res :=
    fun σ1 σ2 g1 g2 => resOk_growsK (resOk_growsK (resOk_intro hR) g1) g2
  have hSk : SlotsK σ mem L.m := (slots_k σ mem L.m).1 hS
  exact c179_body_run g args σ0 fr σ res mem L.m crJmp cnt trJmp total h7 h16 h17 h19 h21 h22 (cmp_le hle)
    hc1 hc2' ht1 ht2' hT1 hT2 hinit hSk (fun σ1 hg => slotsK_growsK hSk hg) hRo2 hz.1 hz.2 hK

end EquivLean.Modernize.Cbstm03a.Java.Seg6

#print axioms EquivLean.Modernize.Cbstm03a.Java.Seg6.c179_body
