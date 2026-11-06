import EquivLean.Modernize.Cbstm03a.Java.Run6.WT
import EquivLean.Modernize.Cbstm03a.Java.Run6.ThinLem

/-!
# CBSTM03A → Java `run`, statement 179, thin: the loop body

`trJmp ≤ cnt`: statements 179–193 with the callee postconditions assumed, back to statement 179; the variant
decreases (`var179_body`): `xrefSt` is an `int[]`, kept by the callees' `Grows` and by `writeTrans`, which changes
only the `Result` object and its lists.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space GrowsK grows_split
  growsK_elim grows_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg6

attribute [-jsimp] List.take_succ JLong.cmp_eq

/-- The `(int)` of `trJmp cmp cnt` is not positive for `trJmp ≤ cnt` (as `cmp_le` of `CbARun6.Body`). -/
theorem cmp_le' {a b : I64} (h : a.toInt ≤ b.toInt) : (JLong.cmp a b).toInt ≤ 0 := by
  rw [JLong.cmp_eq]
  split
  · decide
  · split
    · decide
    · rename_i h1 h2
      exact absurd (BitVec.toInt_inj.1 (by omega)) h2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
set_option jimple.modelContracts true in
/-- The thin symbolic run of the loop body: the facts it needs, and the variant at its end (`hK`). -/
theorem t179_body_run (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (res mem : Addr) (m : Nat → JChar) (crJmp cnt trJmp total : I64) (v : Nat)
    (h7 : fr.get 7 = some (.ref res)) (h16 : fr.get 16 = some (.ref mem))
    (h17 : fr.get 17 = some (.long crJmp)) (h19 : fr.get 19 = some (.long cnt))
    (h21 : fr.get 21 = some (.long total)) (h22 : fr.get 22 = some (.long trJmp))
    (hcmp : (JLong.cmp trJmp cnt).toInt ≤ 0)
    (hc1 : 1 ≤ crJmp.toInt) (hc2 : crJmp.toInt < 10000) (ht1 : 1 ≤ trJmp.toInt) (ht2 : trJmp.toInt < 10000)
    (hinit : σ.initOf "Cbstm03a" = .done)
    (hS : SlotsK σ mem m) (hS1 : ∀ σ1, GrowsK σ σ1 → SlotsK σ1 mem m)
    (hRo2 : ∀ σ1 σ2, GrowsK σ σ1 → GrowsK σ1 σ2 → ResOk σ2 res)
    (hK : Kp (∀ (σ1 σ2 σ4 : State) (o : Obj) (fr' : Frame) (tid trest : JStr) (amt : I64),
      GrowsK σ σ1 → GrowsK σ1 σ2 → WTPost (σ2.alloc o).2 σ4 res tid trest amt →
      (∀ i, i ∉ LoopLocals → fr'.get i = fr.get i) → fr'.get 17 = fr.get 17 → fr'.get 19 = fr.get 19 →
      fr'.get 22 = some (.long (trJmp + 1#64)) → runVar 179 args σ0 fr' σ4 < v)) :
    runThinWP g args σ0 179 fr σ v := by
  unfold runThinWP
  jvc [runCallees, runInv, tranOffSpec, memReadSpec, decodeZonedSpec, writeTransSpec_eq, writeTransSpecR,
    trunc11Spec, grows_split, slots_k, argText, memRd_length, resOk_alloc]
  all_goals
    apply (Kp.elim hK)
    all_goals first
      | (with_reducible assumption)
      | (intro i hi
         simp only [LoopLocals, List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
         obtain ⟨a0, -, -, a20, a21, a22, a26, a33, a34, a36⟩ := hi
         simp [Frame.get_setLocal, a0, a20, a21, a22, a26, a33, a34, a36])
      | (simp [Frame.get_setLocal]; done)
      | (with_reducible rfl)

/-- **The thin loop body**: transaction `trJmp ≤ cnt` of card number `crJmp`, the variant decreases. -/
theorem t179_body (g : RunG) (args : List Value) (σ0 : State) (hpre : RunPre g args σ0) (fr : Frame) (σ : State)
    (res ld ls lh : Addr) (L : LdSt) (oc : JOut) (j : Nat) (crJmp total : I64) (cnt trJmp : I64)
    (hX : XCtx g σ0 fr σ res ld ls lh oc L (j + 1))
    (h17 : fr.get 17 = some (.long crJmp)) (h21 : fr.get 21 = some (.long total))
    (hc1 : 1 ≤ crJmp.toInt) (hc2 : crJmp.toInt ≤ L.cr.toInt)
    (h19 : fr.get 19 = some (.long cnt)) (hcnt : trctGet L.trct crJmp = .long cnt)
    (h22 : fr.get 22 = some (.long trJmp)) (ht1 : 1 ≤ trJmp.toInt) (hle : trJmp.toInt ≤ cnt.toInt) :
    runThinWP g args σ0 179 fr σ (runVar 179 args σ0 fr σ) := by
  have hLB := xctx_bounded hX
  have hcb := cnt_bounds hLB hcnt
  have hcr := hLB.2.1
  have hR := xctx_res hX
  obtain ⟨mem, h16, hS⟩ : ∃ mem, fr.get 16 = some (.ref mem) ∧ SlotsAt σ mem L.m := by
    obtain ⟨-, -, -, -, -, mem, -, -, -, -, ⟨d16, -, hsl, -, -⟩, -⟩ := hX
    exact ⟨mem, d16, hsl⟩
  obtain ⟨st2, h2, hst2⟩ : ∃ st2, fr.get 2 = some (.ref st2) ∧
      σ.heap st2 = some (.array (.prim .int) [.int (BitVec.ofNat 32 (j + 1)), .int 0]) := by
    obtain ⟨-, -, -, -, -, -, -, st2, -, -, -, e2, est2, -⟩ := hX
    exact ⟨st2, e2, est2⟩
  have h7 : fr.get 7 = some (.ref res) := by
    obtain ⟨-, -, -, -, -, -, -, -, ⟨-, -, -, -, b7, -⟩, -⟩ := hX
    exact b7
  have hinit : σ.initOf "Cbstm03a" = .done := by
    obtain ⟨-, -, -, -, -, -, -, -, ⟨-, -, -, -, -, -, -, -, -, -, -, hi0, -⟩, -⟩ := hX
    obtain ⟨-, -, -, -, -, ⟨hcp, -⟩, -⟩ := hpre
    rw [State.initOf_eq_of_inits hi0]; exact hcp
  have hc2' : crJmp.toInt < 10000 := by omega
  have ht2' : trJmp.toInt < 10000 := by omega
  have hK : Kp (∀ (σ1 σ2 σ4 : State) (o : Obj) (fr' : Frame) (tid trest : JStr) (amt : I64),
      GrowsK σ σ1 → GrowsK σ1 σ2 → WTPost (σ2.alloc o).2 σ4 res tid trest amt →
      (∀ i, i ∉ LoopLocals → fr'.get i = fr.get i) → fr'.get 17 = fr.get 17 → fr'.get 19 = fr.get 19 →
      fr'.get 22 = some (.long (trJmp + 1#64)) → runVar 179 args σ0 fr' σ4 < runVar 179 args σ0 fr σ) := by
    apply Kp.intro
    intro σ1 σ2 σ4 o fr' tid trest amt g1 g2 hwt hf hf17 hf19 hf22
    have hG3 : Grows σ (σ2.alloc o).2 :=
      grows_trans (growsK_elim g1) (grows_trans (growsK_elim g2) (grows_alloc σ2 o))
    have hR3 := resAtL_grows hR hG3
    obtain ⟨-, hk34⟩ := wtPost_elim hwt hR3
    have hk : KeepsRes res ld ls lh σ σ4 := keepsRes_trans (keepsRes_of_grows hG3) hk34
    have hst : σ4.heap st2 = σ.heap st2 := by rw [arr_keepsRes hk hR hst2, hst2]
    exact var179_body h2 hst hf hf17 hf19 hf22 h19 h22 (by omega) ht2' hle
  have hRo2 : ∀ σ1 σ2, GrowsK σ σ1 → GrowsK σ1 σ2 → ResOk σ2 res :=
    fun σ1 σ2 g1 g2 => resOk_growsK (resOk_growsK (resOk_intro hR) g1) g2
  have hSk : SlotsK σ mem L.m := (slots_k σ mem L.m).1 hS
  exact t179_body_run g args σ0 fr σ res mem L.m crJmp cnt trJmp total _ h7 h16 h17 h19 h21 h22 (cmp_le' hle)
    hc1 hc2' ht1 ht2' hinit hSk (fun σ1 hg => slotsK_growsK hSk hg) hRo2 hK

end EquivLean.Modernize.Cbstm03a.Java.Seg6

#print axioms EquivLean.Modernize.Cbstm03a.Java.Seg6.t179_body
