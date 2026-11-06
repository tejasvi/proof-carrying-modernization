import EquivLean.Modernize.Cbstm03a.Java.RunPure
import EquivLean.Modernize.Cbstm03b.Java.TrnxFin

/-!
# CBSTM03A → Java `run`, the transactions loop (statement 179): shared lemmas

`Kp` keeps facts away from `jvc`. The frames of the loop body: every object of the cut state but the `Result`
object and its lists is unchanged (`KeepsRes`, from the callees' `Grows` and `writeTrans`' frame), so the
cross-reference context `XCtx` carries over with the new outputs (`xctx_step`). The exit to the cards loop
(`inv168_of_exit`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space GrowsK grows_split
  growsK_elim grows_refl grows_trans forall2_imp)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg6

/-- A fact kept folded across the symbolic executor. -/
@[irreducible] def Kp (p : Prop) : Prop := p

theorem Kp.intro {p : Prop} (h : p) : Kp p := by unfold Kp; exact h
theorem Kp.elim {p : Prop} (h : Kp p) : p := by unfold Kp at h; exact h

/-! ## Frames -/

theorem keepsRes_refl (res ld ls lh : Addr) (σ : State) : KeepsRes res ld ls lh σ σ :=
  ⟨Nat.le_refl _, fun _ _ _ _ _ _ => rfl⟩

theorem keepsRes_of_grows {res ld ls lh : Addr} {σ σ' : State} (h : Grows σ σ') :
    KeepsRes res ld ls lh σ σ' := ⟨h.1, fun y hy _ _ _ _ => h.2 y hy⟩

theorem keepsRes_trans {res ld ls lh : Addr} {σ1 σ2 σ3 : State} (h1 : KeepsRes res ld ls lh σ1 σ2)
    (h2 : KeepsRes res ld ls lh σ2 σ3) : KeepsRes res ld ls lh σ1 σ3 :=
  ⟨Nat.le_trans h1.1 h2.1, fun y hy a b c d => by
    rw [h2.2 y (Nat.lt_of_lt_of_le hy h1.1) a b c d, h1.2 y hy a b c d]⟩

/-- An object of the cut state that is neither a plain object nor a list: kept by `KeepsRes`. -/
theorem heap_keepsRes {res ld ls lh : Addr} {σ σ' : State} {d s t : List JStr} {ab : Bool}
    (hk : KeepsRes res ld ls lh σ σ') (hR : ResAtL σ res ld ls lh d s t ab) {y : Addr} {o : Obj}
    (hy : σ.heap y = some o) (hp : ∀ c fs, o ≠ .plain c fs) (hl : ∀ k xs m, o ≠ .list k xs m) :
    σ'.heap y = some o := by
  obtain ⟨fs, hr, -, -, -, -, -, -, -, ⟨xd, md, hd, -⟩, ⟨xs', ms, hls, -⟩, ⟨xh, mh, hlh, -⟩⟩ := hR
  have n1 : y ≠ res := by
    intro e; rw [e, hr] at hy; exact hp _ _ (Option.some.inj hy).symm
  have n2 : y ≠ ld := by
    intro e; rw [e, hd] at hy; exact hl _ _ _ (Option.some.inj hy).symm
  have n3 : y ≠ ls := by
    intro e; rw [e, hls] at hy; exact hl _ _ _ (Option.some.inj hy).symm
  have n4 : y ≠ lh := by
    intro e; rw [e, hlh] at hy; exact hl _ _ _ (Option.some.inj hy).symm
  rw [hk.2 y (State.lt_next_of_heap hy) n1 n2 n3 n4, hy]

theorem str_keepsRes {res ld ls lh : Addr} {σ σ' : State} {d s t : List JStr} {ab : Bool}
    (hk : KeepsRes res ld ls lh σ σ') (hR : ResAtL σ res ld ls lh d s t ab) {y : Addr} {z : JStr}
    (hy : σ.heap y = some (.str z)) : σ'.heap y = some (.str z) :=
  heap_keepsRes hk hR hy (fun _ _ e => by cases e) (fun _ _ _ e => by cases e)

theorem arr_keepsRes {res ld ls lh : Addr} {σ σ' : State} {d s t : List JStr} {ab : Bool}
    (hk : KeepsRes res ld ls lh σ σ') (hR : ResAtL σ res ld ls lh d s t ab) {y : Addr} {et : JType}
    {vs : List Value} (hy : σ.heap y = some (.array et vs)) : σ'.heap y = some (.array et vs) :=
  heap_keepsRes hk hR hy (fun _ _ e => by cases e) (fun _ _ _ e => by cases e)

theorem jstrAt_keepsRes {res ld ls lh : Addr} {σ σ' : State} {d s t : List JStr} {ab : Bool}
    (hk : KeepsRes res ld ls lh σ σ') (hR : ResAtL σ res ld ls lh d s t ab) {v : Value} {z : JStr}
    (h : JStrAt σ v z) : JStrAt σ' v z := by
  obtain ⟨x, rfl, hx⟩ := h
  exact ⟨x, rfl, str_keepsRes hk hR hx⟩

theorem textsAt_keepsRes {res ld ls lh : Addr} {σ σ' : State} {d s t : List JStr} {ab : Bool}
    (hk : KeepsRes res ld ls lh σ σ') (hR : ResAtL σ res ld ls lh d s t ab) {a : Addr} {ts : List JStr}
    {n : Nat} (h : TextsAt σ a ts n) : TextsAt σ' a ts n := by
  obtain ⟨xs, hx, hf⟩ := h
  exact ⟨xs, arr_keepsRes hk hR hx, forall2_imp (fun _ _ h => jstrAt_keepsRes hk hR h) hf⟩

theorem slotsAt_keepsRes {res ld ls lh : Addr} {σ σ' : State} {d s t : List JStr} {ab : Bool}
    (hk : KeepsRes res ld ls lh σ σ') (hR : ResAtL σ res ld ls lh d s t ab) {a : Addr} {m : Nat → JChar}
    (h : SlotsAt σ a m) : SlotsAt σ' a m := by
  obtain ⟨vs, h1, h2, h3⟩ := h
  refine ⟨vs, arr_keepsRes hk hR h1, h2, fun i hi => ?_⟩
  rcases h3 i hi with h | ⟨x, t, e1, e2, e3, e4⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, t, e1, str_keepsRes hk hR e2, e3, e4⟩

theorem strLoc_keepsRes {res ld ls lh : Addr} {σ σ' : State} {d s t : List JStr} {ab : Bool}
    (hk : KeepsRes res ld ls lh σ σ') (hR : ResAtL σ res ld ls lh d s t ab) {fr fr' : Frame} {i : Nat}
    {z : JStr} (h : StrLoc σ fr i z) (hf : fr'.get i = fr.get i) : StrLoc σ' fr' i z := by
  obtain ⟨x, h1, h2⟩ := h
  exact ⟨x, hf.trans h1, str_keepsRes hk hR h2⟩

theorem grows_keepsRes {σ0 σ σ' : State} {res ld ls lh : Addr} (hg : Grows σ0 σ)
    (hk : KeepsRes res ld ls lh σ σ') (h1 : σ0.next ≤ res) (h2 : σ0.next ≤ ld) (h3 : σ0.next ≤ ls)
    (h4 : σ0.next ≤ lh) : Grows σ0 σ' :=
  ⟨Nat.le_trans hg.1 hk.1, fun x hx => by
    rw [hk.2 x (Nat.lt_of_lt_of_le hx hg.1) (Nat.ne_of_lt (Nat.lt_of_lt_of_le hx h1))
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le hx h2)) (Nat.ne_of_lt (Nat.lt_of_lt_of_le hx h3))
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le hx h4)), hg.2 x hx]⟩

/-- The locals the transactions loop writes: `$b12`, `crJmp`, `cnt`, `amt`, `i#79`, `trJmp`, `i#78`, `cn`,
`xrefCustId`, `trest`. -/
def LoopLocals : List Nat := [0, 17, 19, 20, 21, 22, 26, 33, 34, 36]

theorem fr_eq {fr fr' : Frame} (hf : ∀ i, i ∉ LoopLocals → fr'.get i = fr.get i) (i : Nat)
    (h : i ∉ LoopLocals := by decide) : fr'.get i = fr.get i := hf i h

/-- The cross-reference context after a path that keeps every object but the `Result` object and its lists
(holding `oc'` now) and writes only the loop's locals. -/
theorem xctx_step {g : RunG} {σ0 : State} {fr fr' : Frame} {σ σ' : State} {res ld ls lh : Addr}
    {oc oc' : JOut} {L : LdSt} {j : Nat} (hX : XCtx g σ0 fr σ res ld ls lh oc L j)
    (hk : KeepsRes res ld ls lh σ σ') (hR' : ResAtL σ' res ld ls lh oc'.disp oc'.stmt oc'.html oc'.ab)
    (hi : σ'.inits = σ.inits) (hs : σ'.statics = σ.statics)
    (hf : ∀ i, i ∉ LoopLocals → fr'.get i = fr.get i) :
    XCtx g σ0 fr' σ' res ld ls lh oc' L j := by
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, hB, hT, hLd, h2, hst2, o1, o2, o3, h5, h3, h18, hLB⟩ := hX
  obtain ⟨b10, b23, b9, b6, b7, hR, r0, l0, s0, h0, hg, hi0, hs0⟩ := hB
  obtain ⟨c11, c12, c13, c14, c15, ⟨n3, c27, hn3⟩, ⟨n4, c28, hn4⟩, x1, x2, x3k, x3, x4, q0, q1, q2, q3, q4⟩ := hT
  obtain ⟨d16, d24, hsl, htr, htl⟩ := hLd
  refine ⟨t1, t2, t3k, t3, t4, mem, trct, st2,
    ⟨(fr_eq hf 10).trans b10, (fr_eq hf 23).trans b23, (fr_eq hf 9).trans b9, (fr_eq hf 6).trans b6,
      (fr_eq hf 7).trans b7, hR', r0, l0, s0, h0, grows_keepsRes hg hk r0 l0 s0 h0, hi.trans hi0,
      hs.trans hs0⟩,
    ⟨(fr_eq hf 11).trans c11, (fr_eq hf 12).trans c12, (fr_eq hf 13).trans c13, (fr_eq hf 14).trans c14,
      (fr_eq hf 15).trans c15, ⟨n3, (fr_eq hf 27).trans c27, hn3⟩, ⟨n4, (fr_eq hf 28).trans c28, hn4⟩,
      textsAt_keepsRes hk hR x1, textsAt_keepsRes hk hR x2, textsAt_keepsRes hk hR x3k,
      textsAt_keepsRes hk hR x3, textsAt_keepsRes hk hR x4, q0, q1, q2, q3, q4⟩,
    ⟨(fr_eq hf 16).trans d16, (fr_eq hf 24).trans d24, slotsAt_keepsRes hk hR hsl, arr_keepsRes hk hR htr,
      htl⟩,
    (fr_eq hf 2).trans h2, arr_keepsRes hk hR hst2, o1, o2, o3, (fr_eq hf 5).trans h5, (fr_eq hf 3).trans h3,
    (fr_eq hf 18).trans h18, hLB⟩

/-! ## Numbers -/

theorem i64_toInt_add_one {x : I64} (h0 : 0 ≤ x.toInt) (h1 : x.toInt < 10000) :
    (x + 1#64).toInt = x.toInt + 1 := i64_toInt_add_one_small h0 h1

/-- The count of card number `crJmp` is in `0 … 9999`. -/
theorem cnt_bounds {L : LdSt} {crJmp cnt : I64} (hb : LdBounded L) (h : trctGet L.trct crJmp = .long cnt) :
    0 ≤ cnt.toInt ∧ cnt.toInt < 10000 := by
  obtain ⟨c, hc, h0, h1⟩ := trctGet_bounded crJmp hb.2.2.2.2
  rw [h] at hc
  cases hc
  exact ⟨h0, h1⟩

theorem xctx_bounded {g : RunG} {σ0 : State} {fr : Frame} {σ : State} {res ld ls lh : Addr} {oc : JOut}
    {L : LdSt} {j : Nat} (hX : XCtx g σ0 fr σ res ld ls lh oc L j) : LdBounded L := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hLB⟩ := hX
  exact hLB

theorem xctx_res {g : RunG} {σ0 : State} {fr : Frame} {σ : State} {res ld ls lh : Addr} {oc : JOut}
    {L : LdSt} {j : Nat} (hX : XCtx g σ0 fr σ res ld ls lh oc L j) :
    ResAtL σ res ld ls lh oc.disp oc.stmt oc.html oc.ab := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨-, -, -, -, -, hR, -⟩, -⟩ := hX
  exact hR

/-! ## The exit: back to the cards loop -/

theorem inv168_of_exit {g : RunG} {args : List Value} {σ0 : State} {fr : Frame} {σ : State}
    {res ld ls lh : Addr} {L : LdSt} {oc : JOut} {j : Nat} {crJmp total : I64} {n : Nat} {pF : JOut × I64}
    {cnt trJmp : I64} {acc0 : JOut × I64}
    (hX : XCtx g σ0 fr σ res ld ls lh oc L (j + 1)) (hj : j < g.T2.length)
    (hM : xrefAll g.K3 g.T3 g.T4 L (tailOf pF.1 pF.2) (g.T2.drop (j + 1)) = g.F)
    (h32 : StrLoc σ fr 32 (sub (fixStr (g.T2.getD j []) 1000) 0 16))
    (h21 : fr.get 21 = some (.long total)) (hT : TotOk total)
    (hc1 : 1 ≤ crJmp.toInt) (hc2 : crJmp.toInt ≤ L.cr.toInt) (hcn : crJmp.toInt + n = L.cr.toInt + 1)
    (hcnt : trctGet L.trct crJmp = .long cnt) (ht2 : trJmp.toInt ≤ cnt.toInt + 1)
    (hacc : (oc, total) = transOf L.m crJmp (trJmp.toInt.toNat - 1) acc0)
    (hcards : cardsFrom L.m L.trct L.cr (sub (fixStr (g.T2.getD j []) 1000) 0 16) (n - 1) (crJmp + 1)
      (transOf L.m crJmp cnt.toInt.toNat acc0) = pF)
    (hgt : cnt.toInt < trJmp.toInt)
    (fr' : Frame) (hf17 : fr'.get 17 = some (.long (crJmp + 1#64)))
    (hf : ∀ i, i ∉ LoopLocals → fr'.get i = fr.get i) (hf21 : fr'.get 21 = fr.get 21) :
    inv168 g args σ0 fr' σ := by
  have hLB := xctx_bounded hX
  have hcb := cnt_bounds hLB hcnt
  have hcr := hLB.2.1
  have hidx : trJmp.toInt.toNat - 1 = cnt.toInt.toNat := by omega
  rw [hidx] at hacc
  rw [← hacc] at hcards
  have hc' : (crJmp + 1#64).toInt = crJmp.toInt + 1 := i64_toInt_add_one (by omega) (by omega)
  refine ⟨res, ld, ls, lh, L, oc, j, crJmp + 1#64, total, n - 1, pF,
    xctx_step hX (keepsRes_refl res ld ls lh σ) (xctx_res hX) rfl rfl hf, hj, hM, ?_, hf17, hf21.trans h21,
    hT, ?_, ?_, hcards⟩
  · obtain ⟨x, e1, e2⟩ := h32
    exact ⟨x, (fr_eq hf 32).trans e1, e2⟩
  · omega
  · have : ((n - 1 : Nat) : Int) = (n : Int) - 1 := by omega
    omega

end EquivLean.Modernize.Cbstm03a.Java.Seg6
