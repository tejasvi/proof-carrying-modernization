import EquivLean.Modernize.Cbstm03a.Java.Run6.BodyDefs

/-!
# CBSTM03A → Java `run`, statement 179: the loop body closes the invariant

After the body (transaction `trJmp` written by `writeTrans`, the total updated), the invariant `inv179` holds
again with `trJmp + 1` and the outputs of `transOf … trJmp` (`transOf_succ`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space GrowsK grows_split
  growsK_elim)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg6

theorem ofNat_toInt_toNat {t : I64} (h : 0 ≤ t.toInt) : BitVec.ofNat 64 t.toInt.toNat = t := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  have h2 := t.isLt
  have h1 := BitVec.toInt_eq_toNat_cond t
  have e : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  rw [e] at h1 h2 ⊢
  split at h1
  · rw [h1, Int.toNat_natCast]; exact Nat.mod_eq_of_lt h2
  · omega

theorem inv179_of_body {g : RunG} {args : List Value} {σ0 : State} {fr : Frame} {σ : State}
    {res ld ls lh : Addr} {L : LdSt} {oc : JOut} {j : Nat} {crJmp total : I64} {n : Nat} {pF : JOut × I64}
    {cnt trJmp : I64} {acc0 : JOut × I64}
    (hX : XCtx g σ0 fr σ res ld ls lh oc L (j + 1)) (hj : j < g.T2.length)
    (hM : xrefAll g.K3 g.T3 g.T4 L (tailOf pF.1 pF.2) (g.T2.drop (j + 1)) = g.F)
    (h32 : StrLoc σ fr 32 (sub (fixStr (g.T2.getD j []) 1000) 0 16))
    (h17 : fr.get 17 = some (.long crJmp))
    (hc1 : 1 ≤ crJmp.toInt) (hc2 : crJmp.toInt ≤ L.cr.toInt) (hcn : crJmp.toInt + n = L.cr.toInt + 1)
    (h19 : fr.get 19 = some (.long cnt)) (hcnt : trctGet L.trct crJmp = .long cnt)
    (ht1 : 1 ≤ trJmp.toInt)
    (hacc : (oc, total) = transOf L.m crJmp (trJmp.toInt.toNat - 1) acc0)
    (hcards : cardsFrom L.m L.trct L.cr (sub (fixStr (g.T2.getD j []) 1000) 0 16) (n - 1) (crJmp + 1)
      (transOf L.m crJmp cnt.toInt.toNat acc0) = pF)
    (hle : trJmp.toInt ≤ cnt.toInt)
    (σ' : State) (fr' : Frame) (tid trest : JStr) (amt : I64)
    (hk : KeepsRes res ld ls lh σ σ')
    (hR' : ResAtL σ' res ld ls lh oc.disp (oc.stmt ++ (jWriteTrans tid trest amt.toInt).1)
      (oc.html ++ (jWriteTrans tid trest amt.toInt).2) oc.ab)
    (hi : σ'.inits = σ.inits) (hs : σ'.statics = σ.statics)
    (hf : ∀ i, i ∉ LoopLocals → fr'.get i = fr.get i)
    (hf17 : fr'.get 17 = fr.get 17) (hf19 : fr'.get 19 = fr.get 19)
    (hf21 : fr'.get 21 = some (.long (BitVec.ofInt 64 (trunc11Z (total + amt).toInt))))
    (hf22 : fr'.get 22 = some (.long (trJmp + 1#64)))
    (htid : tid = memRd L.m (tranOffJ crJmp trJmp).toInt 16)
    (htrest : trest = memRd L.m (tranOffJ crJmp trJmp + 16).toInt 318)
    (hamt : amt = BitVec.ofInt 64 (zonedVal (sub trest 116 127))) :
    inv179 g args σ0 fr' σ' := by
  have hLB := xctx_bounded hX
  have hcb := cnt_bounds hLB hcnt
  have ht' : (trJmp + 1#64).toInt = trJmp.toInt + 1 := i64_toInt_add_one (by omega) (by omega)
  refine ⟨res, ld, ls, lh, L, oc.add (jWriteTrans tid trest amt.toInt), j, crJmp,
    BitVec.ofInt 64 (trunc11Z (total + amt).toInt), n, pF, cnt, trJmp + 1#64, acc0,
    xctx_step hX hk hR' hi hs hf, hj, hM, strLoc_keepsRes hk (xctx_res hX) h32 (fr_eq hf 32),
    hf17.trans h17, hf21, totOk_trunc11 _, hc1, hc2, hcn, hf19.trans h19, hcnt, hf22, by omega, by omega,
    ?_, hcards⟩
  have hk1 : (trJmp + 1#64).toInt.toNat - 1 = (trJmp.toInt.toNat - 1) + 1 := by omega
  have hofn : (BitVec.ofNat 64 (trJmp.toInt.toNat - 1 + 1) : I64) = trJmp := by
    rw [show trJmp.toInt.toNat - 1 + 1 = trJmp.toInt.toNat by omega]; exact ofNat_toInt_toNat (by omega)
  rw [hk1, transOf_succ, ← hacc, hofn]
  subst htid htrest hamt
  rfl

end EquivLean.Modernize.Cbstm03a.Java.Seg6
