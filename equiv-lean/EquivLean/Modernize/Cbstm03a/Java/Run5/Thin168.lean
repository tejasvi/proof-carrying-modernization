import EquivLean.Modernize.Cbstm03a.Java.RunTerm
import EquivLean.Modernize.Cbstm03a.Java.Run5.T168
import EquivLean.Modernize.Cbstm03a.Java.Run5.CutT

/-!
# CBSTM03A → Java, `run`'s thin VC from statement 168: virtual cut points with the variant

The thin paths from 168 use the virtual cut points of the partial-correctness proof (173 after `memRead`, 196 …
213 in the statement's tail), each asserting the partial-correctness facts there (`MidJ`, `TailJ k`) and a bound
of the variant: at 173, `runVar 168` (the cards loop's measure, unchanged) at most the start's; in the tail,
`runVar 117` (the next record's) below it. The closers: the partial-correctness closers, and the variant facts
(`xrefSt[0]`, `crCnt`, `crJmp`, `cnt`, `trJmp` read through the frame).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_trans grows_refl heap_grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg5

/-- The thin VC's cut points of `run`: the variant below `v`. -/
abbrev TI (g : RunG) (args : List Value) (σ0 : State) (v : Nat) : Cuts :=
  (runInv g).map fun q => (q.1, fun fr' σ' => runVar q.1 args σ0 fr' σ' < v)

/-- At the tail's virtual cut points: `TailJ k`, and the next record's variant below `v`. -/
def TailT (g : RunG) (args : List Value) (σ0 : State) (v k : Nat) (fr : Frame) (σ : State) : Prop :=
  TailJ g σ0 k fr σ ∧ runVar 117 args σ0 fr σ < v

/-- At the virtual cut point after `memRead`: `MidJ`, and the cards loop's variant at most `v`. -/
def MidT (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (fr : Frame) (σ : State) : Prop :=
  MidJ g σ0 fr σ ∧ runVar 168 args σ0 fr σ ≤ v

/-- The tail's virtual cut points in the thin VC. -/
def tailCutsT (g : RunG) (args : List Value) (σ0 : State) (v : Nat) : Cuts :=
  [(196, TailT g args σ0 v 0), (199, TailT g args σ0 v 1), (202, TailT g args σ0 v 2), (206, TailT g args σ0 v 3),
   (207, TailT g args σ0 v 4), (208, TailT g args σ0 v 5), (209, TailT g args σ0 v 6), (210, TailT g args σ0 v 7),
   (211, TailT g args σ0 v 8), (212, TailT g args σ0 v 9), (213, TailT g args σ0 v 10)]

/-- The cut list of a thin segment: the tail's virtual cut points from the `k`-th on, then `run`'s. -/
abbrev CLt (g : RunG) (args : List Value) (σ0 : State) (v k : Nat) : Cuts :=
  (tailCutsT g args σ0 v).drop k ++ TI g args σ0 v

/-! ## The variant through the frame -/

theorem locL_of {fr : Frame} {i : Nat} {x : I64} (h : fr.get i = some (.long x)) : locL fr i = x.toInt := by
  simp [locL, h]

theorem arr0_eq {σ σ' : State} {fr fr' : Frame} (h2 : fr'.get 2 = fr.get 2)
    (hst : ∀ a, fr.get 2 = some (.ref a) → σ'.heap a = σ.heap a) : arr0 σ' fr' 2 = arr0 σ fr 2 := by
  unfold arr0
  rw [h2]
  cases h : fr.get 2 with
  | none => rfl
  | some w =>
    cases w with
    | ref a => simp only [hst a h]
    | _ => rfl

/-- `xrefSt` (local 2) is an `int[]` the paths keep. -/
theorem hst_of_x {g : RunG} {σ0 σ σ' : State} {fr : Frame} {res ld ls lh : Addr} {o : JOut} {L : LdSt} {j' : Nat}
    (hX : XCtx g σ0 fr σ res ld ls lh o L j') (hsa : SAMono σ σ') :
    ∀ a, fr.get 2 = some (.ref a) → σ'.heap a = σ.heap a := by
  obtain ⟨_, _, _, _, _, _, _, st2, _, _, _, h2, hst2, _⟩ := hX
  intro a ha
  rw [h2] at ha
  cases ha
  rw [heap_arr_sa hsa hst2, hst2]

theorem runVar117_eq {args : List Value} {σ0 σ σ' : State} {fr fr' : Frame} (h2 : fr'.get 2 = fr.get 2)
    (hst : ∀ a, fr.get 2 = some (.ref a) → σ'.heap a = σ.heap a) :
    runVar 117 args σ0 fr' σ' = runVar 117 args σ0 fr σ := by
  simp only [runVar, arr0_eq h2 hst]

theorem runVar117_lt_168 {args : List Value} {σ0 σ σ' : State} {fr fr' : Frame} (h2 : fr'.get 2 = fr.get 2)
    (hst : ∀ a, fr.get 2 = some (.ref a) → σ'.heap a = σ.heap a) :
    runVar 117 args σ0 fr' σ' < runVar 168 args σ0 fr σ := by
  simp only [runVar, arr0_eq h2 hst]
  exact Nat.lt_succ_of_le (Nat.le_add_right _ _)

theorem runVar168_eq {args : List Value} {σ0 σ σ' : State} {fr fr' : Frame} (h2 : fr'.get 2 = fr.get 2)
    (h17 : fr'.get 17 = fr.get 17) (h18 : fr'.get 18 = fr.get 18)
    (hst : ∀ a, fr.get 2 = some (.ref a) → σ'.heap a = σ.heap a) :
    runVar 168 args σ0 fr' σ' = runVar 168 args σ0 fr σ := by
  simp only [runVar, arr0_eq h2 hst, locL, h17, h18]

/-- The next card number: the cards loop's variant one card smaller. -/
theorem runVar168_skip {args : List Value} {σ0 σ σ' : State} {fr fr' : Frame} {crJmp cr : I64}
    (h2 : fr'.get 2 = fr.get 2) (h18 : fr'.get 18 = fr.get 18)
    (hst : ∀ a, fr.get 2 = some (.ref a) → σ'.heap a = σ.heap a)
    (h17 : fr.get 17 = some (.long crJmp)) (h18' : fr.get 18 = some (.long cr))
    (h17' : fr'.get 17 = some (.long (crJmp + 1))) (e1 : (crJmp + 1).toInt = crJmp.toInt + 1)
    (hle : crJmp.toInt ≤ cr.toInt) :
    runVar 168 args σ0 fr' σ' < runVar 168 args σ0 fr σ := by
  simp only [runVar, arr0_eq h2 hst, locL_of h17, locL_of (h18.trans h18'), locL_of h18', locL_of h17', e1, vK]
  generalize ((vN : Int) - arr0 σ fr 2).toNat * vM = B
  omega

/-- This card: the transactions loop's variant below the cards loop's (`cnt < 10000 < K − 1`). -/
theorem runVar179_match {args : List Value} {σ0 σ σ' : State} {fr fr' : Frame} {crJmp cr cnt : I64}
    (h2 : fr'.get 2 = fr.get 2) (h18 : fr'.get 18 = fr.get 18) (h17e : fr'.get 17 = fr.get 17)
    (hst : ∀ a, fr.get 2 = some (.ref a) → σ'.heap a = σ.heap a)
    (h17 : fr.get 17 = some (.long crJmp)) (h18' : fr.get 18 = some (.long cr))
    (h19 : fr'.get 19 = some (.long cnt)) (h22 : fr'.get 22 = some (.long 1))
    (hle : crJmp.toInt ≤ cr.toInt) (hc0 : 0 ≤ cnt.toInt) (hc9 : cnt.toInt < 10000) :
    runVar 179 args σ0 fr' σ' < runVar 168 args σ0 fr σ := by
  have e1 : (1 : I64).toInt = 1 := i64_one_toInt
  simp only [runVar, arr0_eq h2 hst, locL_of (h17e.trans h17), locL_of (h18.trans h18'), locL_of h18',
    locL_of h17, locL_of h19, locL_of h22, e1, vK]
  generalize ((vN : Int) - arr0 σ fr 2).toNat * vM = B
  omega

/-! ## Postconditions found by their shape (`by assumption` for the first argument) -/

theorem memRead_inst {mem : Addr} {crJmp : I64} {σ σ' : State} {v : Option Value} {m : Nat → JChar}
    (hA : ∀ (a : Addr) (off : I64) (n : I32) (m' : Nat → JChar), mem = a → (crJmp - 1) * 3356 = off → 16 = n →
      SlotsAt σ a m' → ∃ x, v = some (.ref x) ∧ σ.next ≤ x ∧
        σ'.heap x = some (.str (memRd m' off.toInt n.toInt.toNat)) ∧ GrowsK σ σ' ∧ σ.next ≤ σ'.next ∧
        (∀ y, y < σ.next → σ'.heap y = σ.heap y) ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)
    (hS : SlotsAt σ mem m) :
    ∃ x, v = some (.ref x) ∧ σ'.heap x = some (.str (memRd m (cardOffJ crJmp).toInt 16)) ∧ GrowsK σ σ' ∧
      σ'.inits = σ.inits ∧ σ'.statics = σ.statics := by
  obtain ⟨x, h1, -, h3, h4, -, -, h7, h8⟩ := hA mem _ _ m rfl rfl rfl hS
  exact ⟨x, h1, h3, h4, h7, h8⟩

theorem getTrct_inst {trct : Addr} {crJmp : I64} {σ σ' : State} {v : Option Value} {vs : List Value}
    (hA : ∀ (a : Addr) (cr : I64) (vs' : List Value), trct = a → crJmp = cr →
      σ.heap a = some (.array (.prim .long) vs') → v = some (trctGet vs' cr) ∧ σ' = σ)
    (htr : σ.heap trct = some (.array (.prim .long) vs)) : v = some (trctGet vs crJmp) ∧ σ' = σ :=
  hA trct crJmp vs rfl rfl htr

/-! ## The closers of the thin segments -/

theorem t168_exit {g : RunG} {args : List Value} {σ0 σ : State} {fr fr' : Frame} {res ld ls lh : Addr} {L : LdSt}
    {oc : JOut} {j : Nat} {crJmp total : I64} {n : Nat} {pF : JOut × I64} {v : Nat}
    (hX : XCtx g σ0 fr σ res ld ls lh oc L (j + 1)) (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L (tailOf pF.1 pF.2) (g.T2.drop (j + 1)) = g.F)
    (h21 : fr.get 21 = some (.long total)) (htot : TotOk total)
    (hpF : cardsFrom L.m L.trct L.cr (sub (fixStr (g.T2.getD j []) 1000) 0 16) n crJmp (oc, total) = pF)
    (hinit : σ.initOf "Cbstm03a" = .done) (hfr : FrT fr fr')
    (hc1 : ¬ crJmp.toInt < L.cr.toInt) (hc2 : ¬ crJmp = L.cr) (hv : runVar 168 args σ0 fr σ ≤ v) :
    TailT g args σ0 v 0 fr' σ :=
  ⟨s168_exit hX hj hmodel h21 htot hpF hinit hfr hc1 hc2,
    Nat.lt_of_lt_of_le (runVar117_lt_168 (hfr.get 2) (fun _ _ => rfl)) hv⟩

theorem t168_mid {g : RunG} {args : List Value} {σ0 σ σ' : State} {fr fr' : Frame} {res ld ls lh : Addr}
    {L : LdSt} {oc : JOut} {j : Nat} {crJmp total : I64} {n : Nat} {pF : JOut × I64} {x : Addr} {v : Nat}
    (hpre : RunPre g args σ0)
    (hX : XCtx g σ0 fr σ res ld ls lh oc L (j + 1)) (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L (tailOf pF.1 pF.2) (g.T2.drop (j + 1)) = g.F)
    (hc32 : StrLoc σ fr 32 (sub (fixStr (g.T2.getD j []) 1000) 0 16))
    (h17 : fr.get 17 = some (.long crJmp)) (h21 : fr.get 21 = some (.long total)) (htot : TotOk total)
    (hc1 : 1 ≤ crJmp.toInt) (hn : crJmp.toInt + n = L.cr.toInt + 1)
    (hpF : cardsFrom L.m L.trct L.cr (sub (fixStr (g.T2.getD j []) 1000) 0 16) n crJmp (oc, total) = pF)
    (hle : crJmp.toInt ≤ L.cr.toInt) (hinit : σ.initOf "Cbstm03a" = .done)
    (hfr : FrT fr fr') (e17 : fr'.get 17 = fr.get 17) (e32 : fr'.get 32 = fr.get 32)
    (e33 : fr'.get 33 = some (.ref x))
    (hxh : σ'.heap x = some (.str (memRd L.m (cardOffJ crJmp).toInt 16))) (hg : Grows σ σ')
    (hi : σ'.inits = σ.inits) (hs : σ'.statics = σ.statics) (hv : runVar 168 args σ0 fr σ ≤ v) :
    MidT g args σ0 v fr' σ' :=
  ⟨s168_mid hpre hX hj hmodel hc32 h17 h21 htot hc1 hn hpF hle hinit hfr e17 e32 e33 hxh hg hi hs,
    Nat.le_trans (Nat.le_of_eq (runVar168_eq (hfr.get 2) e17 (hfr.get 18) (hst_of_x hX (saMono_of_grows hg))))
      hv⟩

theorem t173_exit {g : RunG} {args : List Value} {σ0 σ : State} {fr fr' : Frame} {res ld ls lh : Addr}
    {L : LdSt} {oc : JOut} {j : Nat} {crJmp total : I64} {n : Nat} {pF : JOut × I64} {xm xc : Addr} {M card : JStr}
    {v : Nat}
    (hX : XCtx g σ0 fr σ res ld ls lh oc L (j + 1)) (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L (tailOf pF.1 pF.2) (g.T2.drop (j + 1)) = g.F)
    (h21 : fr.get 21 = some (.long total)) (htot : TotOk total) (hle : crJmp.toInt ≤ L.cr.toInt)
    (hn : crJmp.toInt + n = L.cr.toInt + 1)
    (hpF : cardsFrom L.m L.trct L.cr (sub (fixStr (g.T2.getD j []) 1000) 0 16) n crJmp (oc, total) = pF)
    (hM : memRd L.m (cardOffJ crJmp).toInt 16 = M) (hcard : sub (fixStr (g.T2.getD j []) 1000) 0 16 = card)
    (hxm : σ.heap xm = some (.str M)) (hxc : σ.heap xc = some (.str card))
    (hcond : 0 < (ebcCmp (argText σ (.ref xm)) (argText σ (.ref xc))).bmod 4294967296)
    (hinit : σ.initOf "Cbstm03a" = .done) (hfr : FrT fr fr') (hv : runVar 168 args σ0 fr σ ≤ v) :
    TailT g args σ0 v 0 fr' σ :=
  ⟨mid_exit hX hj hmodel h21 htot hle hn hpF hM hcard hxm hxc hcond hinit hfr,
    Nat.lt_of_lt_of_le (runVar117_lt_168 (hfr.get 2) (fun _ _ => rfl)) hv⟩

theorem t173_skip {args : List Value} {σ0 σ : State} {fr fr' : Frame} {crJmp cr : I64} {v : Nat}
    (hfr : FrT fr fr') (h17 : fr.get 17 = some (.long crJmp)) (h18 : fr.get 18 = some (.long cr))
    (h17' : fr'.get 17 = some (.long (crJmp + 1))) (hle : crJmp.toInt ≤ cr.toInt) (hcr : cr.toInt < 10000)
    (hc1 : 1 ≤ crJmp.toInt) (hv : runVar 168 args σ0 fr σ ≤ v) :
    runVar 168 args σ0 fr' σ < v :=
  Nat.lt_of_lt_of_le (runVar168_skip (hfr.get 2) (hfr.get 18) (fun _ _ => rfl) h17 h18 h17'
    (i64_toInt_add_one_small (by omega) (by omega)) hle) hv

theorem t173_match {args : List Value} {σ0 σ : State} {fr fr' : Frame} {crJmp cr cnt : I64} {v : Nat}
    (hfr : FrT fr fr') (e17 : fr'.get 17 = fr.get 17) (h17 : fr.get 17 = some (.long crJmp))
    (h18 : fr.get 18 = some (.long cr)) (h19 : fr'.get 19 = some (.long cnt)) (h22 : fr'.get 22 = some (.long 1))
    (hle : crJmp.toInt ≤ cr.toInt) (hc0 : 0 ≤ cnt.toInt) (hc9 : cnt.toInt < 10000)
    (hv : runVar 168 args σ0 fr σ ≤ v) :
    runVar 179 args σ0 fr' σ < v :=
  Nat.lt_of_lt_of_le (runVar179_match (hfr.get 2) (hfr.get 18) e17 (fun _ _ => rfl) h17 h18 h19 h22 hle hc0 hc9)
    hv

/-- The variant at the tail's cut points: the next record's, unchanged along the tail. -/
theorem tail_var {g : RunG} {args : List Value} {σ0 σ σ' : State} {fr fr' : Frame} {res ld ls lh : Addr} {o : JOut}
    {L : LdSt} {j' : Nat} {v : Nat} (hX : XCtx g σ0 fr σ res ld ls lh o L j') (hfr : FrT fr fr')
    (hsa : SAMono σ σ') (hv : runVar 117 args σ0 fr σ < v) : runVar 117 args σ0 fr' σ' < v := by
  rw [runVar117_eq (hfr.get 2) (hst_of_x hX hsa)]
  exact hv

/-- From the cut after `k` lines of the tail to the cut after `k + 1`, in the thin VC. -/
theorem tailT_step {g : RunG} {args : List Value} {σ0 σ σc σ' : State} {fr fr' : Frame} {res ld ls lh : Addr}
    {L : LdSt} {oc : JOut} {j : Nat} {total : I64} {k v : Nat}
    (hX : XCtx g σ0 fr σ res ld ls lh (tailK oc total k) L (j + 1)) (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L (tailOf oc total) (g.T2.drop (j + 1)) = g.F)
    (h7 : fr.get 7 = some (.ref res)) (hinit : σ.initOf "Cbstm03a" = .done) (htot : TotOk total)
    (hfr : FrT fr fr') (hg : Grows σ σc) (hk : KeepsRes res ld ls lh σc σ')
    (hR : ResAtL σ' res ld ls lh (tailK oc total (k + 1)).disp (tailK oc total (k + 1)).stmt
      (tailK oc total (k + 1)).html (tailK oc total (k + 1)).ab)
    (hi : σ'.inits = σ.inits) (hs : σ'.statics = σ.statics)
    (h32 : k + 1 = 1 → StrLoc σ' fr' 32 (fmtZStr total.toInt)) (hv : runVar 117 args σ0 fr σ < v) :
    TailT g args σ0 v (k + 1) fr' σ' :=
  ⟨tail_step hX hj hmodel h7 hinit htot hfr (keepsRes_trans (keepsRes_of_grows hg) hk) hR hi hs h32,
    tail_var hX hfr (saMono_trans (saMono_of_grows hg) (saMono_of_keepsRes (resAtL_grows (xctx_resAtL hX) hg) hk))
      hv⟩

/-- The tail's last call, back at the cross-reference loop's head: the next record's variant below `v`. -/
theorem tailT_last {g : RunG} {args : List Value} {σ0 σ σc σ' : State} {fr fr' : Frame} {res ld ls lh : Addr}
    {o : JOut} {L : LdSt} {j' : Nat} {v : Nat} (hX : XCtx g σ0 fr σ res ld ls lh o L j') (hfr : FrT fr fr')
    (hg : Grows σ σc) (hk : KeepsRes res ld ls lh σc σ') (hv : runVar 117 args σ0 fr σ < v) :
    runVar 117 args σ0 fr' σ' < v :=
  tail_var hX hfr (saMono_trans (saMono_of_grows hg) (saMono_of_keepsRes (resAtL_grows (xctx_resAtL hX) hg) hk)) hv

end EquivLean.Modernize.Cbstm03a.Java.Seg5
