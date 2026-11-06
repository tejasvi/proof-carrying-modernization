import EquivLean.Modernize.Cbstm03a.Java.Run5.Tail

/-!
# CBSTM03A → Java, `run`'s segment 168: the closers

The virtual cut point after `memRead` (statement 173, `MidJ`), and the lemmas that close each segment's goals: a
callee's precondition about the `Result` object at the call's state, its postcondition instantiated by hand
(`stmt_post`, `html_post`), the next cut point's assertion (`tail_step`, `tail_last`, `s168_exit`, `s168_mid`,
`mid_exit`, `mid_skip`, `mid_match`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_trans grows_refl heap_grows zpadStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg5

/-! ## The cut point after `memRead` -/

/-- Statement 173 (after `cn = memRead(i#28, cardOff(crJmp), 16)`, card number `crJmp` not past `crCnt`): the
cards loop's state of `inv168`, the card's text read in `cn`. -/
def MidJ (g : RunG) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (res ld ls lh : Addr) (L : LdSt) (oc : JOut) (j : Nat) (crJmp total : I64) (n : Nat) (pF : JOut × I64)
    (xm xc trct acp : Addr),
    Kept (XCtx g σ0 fr σ res ld ls lh oc L (j + 1) ∧ j < g.T2.length ∧
      xrefAll g.K3 g.T3 g.T4 L (tailOf pF.1 pF.2) (g.T2.drop (j + 1)) = g.F ∧
      StrLoc σ fr 32 (sub (fixStr (g.T2.getD j []) 1000) 0 16) ∧ fr.get 21 = some (.long total) ∧
      TotOk total ∧ 1 ≤ crJmp.toInt ∧ crJmp.toInt ≤ L.cr.toInt ∧ crJmp.toInt + n = L.cr.toInt + 1 ∧
      cardsFrom L.m L.trct L.cr (sub (fixStr (g.T2.getD j []) 1000) 0 16) n crJmp (oc, total) = pF) ∧
    fr.get 33 = some (.ref xm) ∧ σ.heap xm = some (.str (memRd L.m (cardOffJ crJmp).toInt 16)) ∧
    fr.get 32 = some (.ref xc) ∧ σ.heap xc = some (.str (sub (fixStr (g.T2.getD j []) 1000) 0 16)) ∧
    fr.get 17 = some (.long crJmp) ∧ fr.get 24 = some (.ref trct) ∧
    σ.heap trct = some (.array (.prim .long) L.trct) ∧ L.trct.length = 51 ∧
    fr.get 7 = some (.ref res) ∧ σ.initOf "Cbstm03a" = .done ∧
    σ.static ("Cbstm03a", "CP037") = some (.ref acp) ∧ σ.heap acp = some (.array (.prim .int) cp037Arr)

/-! ## Small facts -/

theorem argText_ref {σ : State} {x : Addr} {s : JStr} (h : σ.heap x = some (.str s)) :
    argText σ (.ref x) = s := by
  simp only [argText, strOf, h, Option.getD_some]

theorem argText_alloc_self (σ : State) (s : JStr) : argText (σ.alloc (.str s)).2 (.ref σ.next) = s := by
  simp [argText, strOf, State.heap_alloc]

theorem ebcScan_range (a b : JStr) : -1 ≤ ebcScan a b ∧ ebcScan a b ≤ 1 := by
  induction a generalizing b with
  | nil => change -1 ≤ (0 : Int) ∧ (0 : Int) ≤ 1; omega
  | cons ca xs ih =>
    cases b with
    | nil => change -1 ≤ (0 : Int) ∧ (0 : Int) ≤ 1; omega
    | cons cb ys =>
      simp only [ebcScan]
      split
      · split <;> omega
      · exact ih ys

theorem ebcCmp_bmod (a b : JStr) : (ebcCmp a b).bmod 4294967296 = ebcCmp a b := by
  have h : -1 ≤ ebcCmp a b ∧ ebcCmp a b ≤ 1 := by
    unfold ebcCmp
    split
    · omega
    · exact ebcScan_range _ _
  exact bmod32_of_bounds (by omega) (by omega)

/-- `Grows σ σ'` for a state built from `σ` by allocations and callees (`GrowsK`). -/
macro "grows_tac" : tactic => `(tactic| repeat (first
  | (with_reducible exact grows_refl _)
  | (refine grows_trans ?_ (growsK_elim (by assumption)))
  | (refine grows_trans ?_ (grows_alloc _ _))))

theorem xctx_get7 {g : RunG} {σ0 σ : State} {fr : Frame} {res ld ls lh : Addr} {o : JOut} {L : LdSt} {j' : Nat}
    (h : XCtx g σ0 fr σ res ld ls lh o L j') : fr.get 7 = some (.ref res) := by
  obtain ⟨_, _, _, _, _, _, _, _, ⟨_, _, _, _, h7, _⟩, _⟩ := h
  exact h7

theorem xctx_base {g : RunG} {σ0 σ : State} {fr : Frame} {res ld ls lh : Addr} {o : JOut} {L : LdSt} {j' : Nat}
    (h : XCtx g σ0 fr σ res ld ls lh o L j') : Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics := by
  obtain ⟨_, _, _, _, _, _, _, _, ⟨_, _, _, _, _, _, _, _, _, _, hg, hi, hs⟩, _⟩ := h
  exact ⟨hg, hi, hs⟩

theorem xctx_load {g : RunG} {σ0 σ : State} {fr : Frame} {res ld ls lh : Addr} {o : JOut} {L : LdSt} {j' : Nat}
    (h : XCtx g σ0 fr σ res ld ls lh o L j') : ∃ mem trct, LoadAt σ fr mem trct L := by
  obtain ⟨_, _, _, _, _, mem, trct, _, _, _, hL, _⟩ := h
  exact ⟨mem, trct, hL⟩

theorem xctx_cr {g : RunG} {σ0 σ : State} {fr : Frame} {res ld ls lh : Addr} {o : JOut} {L : LdSt} {j' : Nat}
    (h : XCtx g σ0 fr σ res ld ls lh o L j') : fr.get 18 = some (.long L.cr) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h18, _⟩ := h
  exact h18

/-- The `CP037` table of the entry state, in a state the run reached. -/
theorem cp037_at {g : RunG} {args : List Value} {σ0 σ : State} (hpre : RunPre g args σ0) (hg : Grows σ0 σ)
    (hs : σ.statics = σ0.statics) :
    ∃ acp, σ.static ("Cbstm03a", "CP037") = some (.ref acp) ∧ σ.heap acp = some (.array (.prim .int) cp037Arr) := by
  obtain ⟨-, -, -, -, -, ⟨-, acp, h1, h2⟩, -⟩ := hpre
  exact ⟨acp, (State.static_eq_of_statics hs _).trans h1, heap_grows hg h2⟩

/-! ## The calls on the `Result` object -/

theorem stmt_post {σc σ' σs : State} {res ld ls lh : Addr} {d st ht : List JStr} {ab : Bool} {v : Option Value}
    {line : JStr}
    (hA : ∀ (res_1 ld ls lh : Addr) (disp st ht : List JStr),
      (res = res_1 → ResAtL σc res_1 ld ls lh disp st ht false →
        v = none ∧ ResAtL σ' res_1 ld ls lh disp (st ++ [sl line]) ht false ∧ KeepsRes res_1 ld ls lh σc σ' ∧
          σ'.inits = σs.inits ∧ σ'.statics = σs.statics) ∧
      (res = res_1 → ResAtL σc res_1 ld ls lh disp st ht true →
        v = none ∧ ResAtL σ' res_1 ld ls lh disp (st ++ [sl line]) ht true ∧ KeepsRes res_1 ld ls lh σc σ' ∧
          σ'.inits = σs.inits ∧ σ'.statics = σs.statics))
    (hR : ResAtL σc res ld ls lh d st ht ab) :
    ResAtL σ' res ld ls lh d (st ++ [sl line]) ht ab ∧ KeepsRes res ld ls lh σc σ' ∧
      σ'.inits = σs.inits ∧ σ'.statics = σs.statics := by
  have h := hA res ld ls lh d st ht
  cases ab
  · exact (h.1 rfl hR).2
  · exact (h.2 rfl hR).2

theorem html_post {σc σ' σs : State} {res ld ls lh : Addr} {d st ht : List JStr} {ab : Bool} {v : Option Value}
    {line : JStr}
    (hA : ∀ (res_1 ld ls lh : Addr) (disp st ht : List JStr),
      (res = res_1 → ResAtL σc res_1 ld ls lh disp st ht false →
        v = none ∧ ResAtL σ' res_1 ld ls lh disp st (ht ++ [hl line]) false ∧ KeepsRes res_1 ld ls lh σc σ' ∧
          σ'.inits = σs.inits ∧ σ'.statics = σs.statics) ∧
      (res = res_1 → ResAtL σc res_1 ld ls lh disp st ht true →
        v = none ∧ ResAtL σ' res_1 ld ls lh disp st (ht ++ [hl line]) true ∧ KeepsRes res_1 ld ls lh σc σ' ∧
          σ'.inits = σs.inits ∧ σ'.statics = σs.statics))
    (hR : ResAtL σc res ld ls lh d st ht ab) :
    ResAtL σ' res ld ls lh d st (ht ++ [hl line]) ab ∧ KeepsRes res ld ls lh σc σ' ∧
      σ'.inits = σs.inits ∧ σ'.statics = σs.statics := by
  have h := hA res ld ls lh d st ht
  cases ab
  · exact (h.1 rfl hR).2
  · exact (h.2 rfl hR).2

/-- The `Result` after a `stmt` whose argument is the string at `w` (a callee's result). -/
theorem stmt_line {σ' σc : State} {res ld ls lh w : Addr} {d st ht : List JStr} {ab : Bool} {s : JStr} {o : JOut}
    (hR : ResAtL σ' res ld ls lh d (st ++ [sl (argText σc (.ref w))]) ht ab) (hw : σc.heap w = some (.str s))
    (he : (⟨d, st ++ [sl s], ht, ab⟩ : JOut) = o) : ResAtL σ' res ld ls lh o.disp o.stmt o.html o.ab := by
  rw [argText_ref hw] at hR
  subst he
  exact hR

/-- The `Result` after a `stmt` whose argument is the string a concatenation just built. -/
theorem stmt_line2 {σ' σ1 : State} {res ld ls lh : Addr} {d st ht : List JStr} {ab : Bool} {a : Obj} {s : JStr}
    {o : JOut}
    (hR : ResAtL σ' res ld ls lh d (st ++ [sl (argText ((σ1.alloc a).2.alloc (.str s)).2 (.ref (σ1.next + 1)))])
      ht ab)
    (he : (⟨d, st ++ [sl s], ht, ab⟩ : JOut) = o) : ResAtL σ' res ld ls lh o.disp o.stmt o.html o.ab := by
  rw [argText_alloc2_snd] at hR
  subst he
  exact hR

/-- The `Result` after an `html` with a literal argument. -/
theorem html_line {σ' σ : State} {res ld ls lh : Addr} {d st ht : List JStr} {ab : Bool} {s : JStr} {o : JOut}
    (hR : ResAtL σ' res ld ls lh d st (ht ++ [hl (argText (σ.alloc (.str s)).2 (.ref σ.next))]) ab)
    (he : (⟨d, st, ht ++ [hl s], ab⟩ : JOut) = o) : ResAtL σ' res ld ls lh o.disp o.stmt o.html o.ab := by
  rw [argText_alloc_self] at hR
  subst he
  exact hR

/-- A string a callee of the segment returned, still there after the segment's call on the `Result`. -/
theorem strLoc_after {σa σc σ' : State} {fr : Frame} {res ld ls lh x : Addr} {d st ht : List JStr} {ab : Bool}
    {s : JStr} (hx : σa.heap x = some (.str s)) (hfr : fr.get 32 = some (.ref x)) (hg : Grows σa σc)
    (hRc : ResAtL σc res ld ls lh d st ht ab) (hk : KeepsRes res ld ls lh σc σ') : StrLoc σ' fr 32 s :=
  ⟨x, hfr, heap_str_sa (saMono_of_keepsRes hRc hk) (heap_grows hg hx)⟩

theorem lead0_le : ∀ s : JStr, lead0 s ≤ s.length
  | [] => Nat.le_refl _
  | c :: s => by
    have := lead0_le s
    unfold lead0
    split <;> simp <;> omega

theorem fmtZStr_length (v : Int) : (fmtZStr v).length = 13 := by
  have h := lead0_le (zpadStr (v.natAbs / 100) 9)
  rw [zpadStr_length] at h
  have e1 : (JStr.ofString ".").length = 1 := rfl
  have e2 : (signStr v).length = 1 := by unfold signStr; split <;> rfl
  simp only [fmtZStr, List.length_append, List.length_replicate, List.length_drop, zpadStr_length, e1, e2]
  omega

/-! ## The tail's cut points -/

/-- From the cut after `k` lines of the tail to the cut after `k + 1`. -/
theorem tail_step {g : RunG} {σ0 σ σ' : State} {fr fr' : Frame} {res ld ls lh : Addr} {L : LdSt} {oc : JOut}
    {j : Nat} {total : I64} {k : Nat}
    (hX : XCtx g σ0 fr σ res ld ls lh (tailK oc total k) L (j + 1)) (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L (tailOf oc total) (g.T2.drop (j + 1)) = g.F)
    (h7 : fr.get 7 = some (.ref res)) (hinit : σ.initOf "Cbstm03a" = .done) (htot : TotOk total)
    (hfr : FrT fr fr') (hk : KeepsRes res ld ls lh σ σ')
    (hR : ResAtL σ' res ld ls lh (tailK oc total (k + 1)).disp (tailK oc total (k + 1)).stmt
      (tailK oc total (k + 1)).html (tailK oc total (k + 1)).ab)
    (hi : σ'.inits = σ.inits) (hs : σ'.statics = σ.statics)
    (h32 : k + 1 = 1 → StrLoc σ' fr' 32 (fmtZStr total.toInt)) :
    TailJ g σ0 (k + 1) fr' σ' :=
  ⟨res, ld, ls, lh, L, oc, j, total, Kept.intro ⟨xctx_frameT hX hfr hk hR hi hs, hj, hmodel⟩,
    (hfr.get 7).trans h7, by rw [State.initOf_eq_of_inits hi]; exact hinit, htot,
    fun h => absurd h (Nat.succ_ne_zero k), h32⟩

/-- From the cut after the tail's last line but one to the cross-reference loop's head. -/
theorem tail_last {g : RunG} {args : List Value} {σ0 σ σ' : State} {fr fr' : Frame} {res ld ls lh : Addr}
    {L : LdSt} {oc : JOut} {j : Nat} {total : I64}
    (hX : XCtx g σ0 fr σ res ld ls lh (tailK oc total 10) L (j + 1)) (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L (tailOf oc total) (g.T2.drop (j + 1)) = g.F)
    (hfr : FrT fr fr') (hk : KeepsRes res ld ls lh σ σ')
    (hR : ResAtL σ' res ld ls lh (tailOf oc total).disp (tailOf oc total).stmt (tailOf oc total).html
      (tailOf oc total).ab)
    (hi : σ'.inits = σ.inits) (hs : σ'.statics = σ.statics) :
    inv117 g args σ0 fr' σ' :=
  ⟨res, ld, ls, lh, L, tailOf oc total, j + 1, xctx_frameT hX hfr hk hR hi hs, hj, hmodel⟩

/-! ## The paths from 168 -/

theorem toInt_lt_of_not {a b : I64} (h1 : ¬ a.toInt < b.toInt) (h2 : ¬ a = b) : b.toInt < a.toInt := by
  have h3 : ¬ a.toInt = b.toInt := fun e => h2 (BitVec.toInt_inj.mp e)
  omega

/-- Card number `crJmp` past `crCnt`: the tail, with the outputs unchanged. -/
theorem s168_exit {g : RunG} {σ0 σ : State} {fr fr' : Frame} {res ld ls lh : Addr} {L : LdSt} {oc : JOut}
    {j : Nat} {crJmp total : I64} {n : Nat} {pF : JOut × I64}
    (hX : XCtx g σ0 fr σ res ld ls lh oc L (j + 1)) (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L (tailOf pF.1 pF.2) (g.T2.drop (j + 1)) = g.F)
    (h21 : fr.get 21 = some (.long total)) (htot : TotOk total)
    (hpF : cardsFrom L.m L.trct L.cr (sub (fixStr (g.T2.getD j []) 1000) 0 16) n crJmp (oc, total) = pF)
    (hinit : σ.initOf "Cbstm03a" = .done) (hfr : FrT fr fr')
    (hc1 : ¬ crJmp.toInt < L.cr.toInt) (hc2 : ¬ crJmp = L.cr) :
    TailJ g σ0 0 fr' σ := by
  have e : pF = (oc, total) := by rw [← hpF, cardsFrom_past (toInt_lt_of_not hc1 hc2)]
  subst e
  exact ⟨res, ld, ls, lh, L, oc, j, total,
    Kept.intro ⟨xctx_frameT hX hfr (keepsRes_of_grows (grows_refl σ)) (xctx_resAtL hX) rfl rfl, hj, hmodel⟩,
    (hfr.get 7).trans (xctx_get7 hX), hinit, htot, fun _ => (hfr.get 21).trans h21,
    fun h => absurd h (by decide)⟩

/-- Card number `crJmp` not past `crCnt`: its text read, at the cut after `memRead`. -/
theorem s168_mid {g : RunG} {args : List Value} {σ0 σ σ' : State} {fr fr' : Frame} {res ld ls lh : Addr}
    {L : LdSt} {oc : JOut} {j : Nat} {crJmp total : I64} {n : Nat} {pF : JOut × I64} {x : Addr}
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
    (hi : σ'.inits = σ.inits) (hs : σ'.statics = σ.statics) :
    MidJ g σ0 fr' σ' := by
  have hsa := saMono_of_grows hg
  obtain ⟨hg0, hi0, hs0⟩ := xctx_base hX
  obtain ⟨acp, hc1', hc2'⟩ := cp037_at hpre (grows_trans hg0 hg) (hs.trans hs0)
  obtain ⟨mem, trct, -, h24, -, htr, hl51⟩ := xctx_load hX
  obtain ⟨xc, hxc1, hxc2⟩ := hc32
  exact ⟨res, ld, ls, lh, L, oc, j, crJmp, total, n, pF, x, xc, trct, acp,
    Kept.intro ⟨xctx_frameT hX hfr (keepsRes_of_grows hg) (resAtL_grows (xctx_resAtL hX) hg) hi hs, hj, hmodel,
      ⟨xc, e32.trans hxc1, heap_str_sa hsa hxc2⟩, (hfr.get 21).trans h21, htot, hc1, hle, hn, hpF⟩,
    e33, hxh, e32.trans hxc1, heap_str_sa hsa hxc2, e17.trans h17, (hfr.get 24).trans h24, heap_arr_sa hsa htr,
    hl51, (hfr.get 7).trans (xctx_get7 hX), by rw [State.initOf_eq_of_inits hi]; exact hinit, hc1', hc2'⟩

/-! ## The paths from 173 -/

/-- The card's text after `card` in EBCDIC order: the tail, with the outputs unchanged. -/
theorem mid_exit {g : RunG} {σ0 σ : State} {fr fr' : Frame} {res ld ls lh : Addr} {L : LdSt} {oc : JOut}
    {j : Nat} {crJmp total : I64} {n : Nat} {pF : JOut × I64} {xm xc : Addr} {M card : JStr}
    (hX : XCtx g σ0 fr σ res ld ls lh oc L (j + 1)) (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L (tailOf pF.1 pF.2) (g.T2.drop (j + 1)) = g.F)
    (h21 : fr.get 21 = some (.long total)) (htot : TotOk total) (hle : crJmp.toInt ≤ L.cr.toInt)
    (hn : crJmp.toInt + n = L.cr.toInt + 1)
    (hpF : cardsFrom L.m L.trct L.cr (sub (fixStr (g.T2.getD j []) 1000) 0 16) n crJmp (oc, total) = pF)
    (hM : memRd L.m (cardOffJ crJmp).toInt 16 = M) (hcard : sub (fixStr (g.T2.getD j []) 1000) 0 16 = card)
    (hxm : σ.heap xm = some (.str M)) (hxc : σ.heap xc = some (.str card))
    (hcond : 0 < (ebcCmp (argText σ (.ref xm)) (argText σ (.ref xc))).bmod 4294967296)
    (hinit : σ.initOf "Cbstm03a" = .done) (hfr : FrT fr fr') :
    TailJ g σ0 0 fr' σ := by
  rw [argText_ref hxm, argText_ref hxc, ebcCmp_bmod, ← hM, ← hcard] at hcond
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have e : pF = (oc, total) := by rw [← hpF, cardsFrom_break (by omega) hcond]
  subst e
  exact ⟨res, ld, ls, lh, L, oc, j, total,
    Kept.intro ⟨xctx_frameT hX hfr (keepsRes_of_grows (grows_refl σ)) (xctx_resAtL hX) rfl rfl, hj, hmodel⟩,
    (hfr.get 7).trans (xctx_get7 hX), hinit, htot, fun _ => (hfr.get 21).trans h21,
    fun h => absurd h (by decide)⟩

/-- Another card: the next card number. -/
theorem mid_skip {g : RunG} {args : List Value} {σ0 σ : State} {fr fr' : Frame} {res ld ls lh : Addr} {L : LdSt}
    {oc : JOut} {j : Nat} {crJmp total : I64} {n : Nat} {pF : JOut × I64} {xm xc : Addr} {M card : JStr}
    (hX : XCtx g σ0 fr σ res ld ls lh oc L (j + 1)) (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L (tailOf pF.1 pF.2) (g.T2.drop (j + 1)) = g.F)
    (hc32 : StrLoc σ fr 32 (sub (fixStr (g.T2.getD j []) 1000) 0 16))
    (h21 : fr.get 21 = some (.long total)) (htot : TotOk total) (hc1 : 1 ≤ crJmp.toInt)
    (hle : crJmp.toInt ≤ L.cr.toInt) (hn : crJmp.toInt + n = L.cr.toInt + 1)
    (hpF : cardsFrom L.m L.trct L.cr (sub (fixStr (g.T2.getD j []) 1000) 0 16) n crJmp (oc, total) = pF)
    (hM : memRd L.m (cardOffJ crJmp).toInt 16 = M) (hcard : sub (fixStr (g.T2.getD j []) 1000) 0 16 = card)
    (hxm : σ.heap xm = some (.str M)) (hxc : σ.heap xc = some (.str card))
    (hcond : ¬ 0 < (ebcCmp (argText σ (.ref xm)) (argText σ (.ref xc))).bmod 4294967296) (hne : ¬ M = card)
    (hfr : FrT fr fr') (e17 : fr'.get 17 = some (.long (crJmp + 1))) (e32 : fr'.get 32 = fr.get 32) :
    inv168 g args σ0 fr' σ := by
  rw [argText_ref hxm, argText_ref hxc, ebcCmp_bmod, ← hM, ← hcard] at hcond
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hcr0, hcr1, -⟩ := xctx_ldBounded hX
  have e1 : (crJmp + 1).toInt = crJmp.toInt + 1 := i64_toInt_add_one_small (by omega) (by omega)
  have hne' : sub (fixStr (g.T2.getD j []) 1000) 0 16 ≠ memRd L.m (cardOffJ crJmp).toInt 16 := by
    rw [hM, hcard]; exact fun h => hne h.symm
  rw [cardsFrom_skip (by omega) hcond hne'] at hpF
  obtain ⟨xc', hx1, hx2⟩ := hc32
  exact ⟨res, ld, ls, lh, L, oc, j, crJmp + 1, total, n', pF,
    xctx_frameT hX hfr (keepsRes_of_grows (grows_refl σ)) (xctx_resAtL hX) rfl rfl, hj, hmodel,
    ⟨xc', e32.trans hx1, hx2⟩, e17, (hfr.get 21).trans h21, htot, by omega, by omega, hpF⟩

/-- This card: its transactions from the first. -/
theorem mid_match {g : RunG} {args : List Value} {σ0 σ : State} {fr fr' : Frame} {res ld ls lh : Addr}
    {L : LdSt} {oc : JOut} {j : Nat} {crJmp total : I64} {n : Nat} {pF : JOut × I64} {xm xc : Addr}
    {card : JStr} {v : Value}
    (hX : XCtx g σ0 fr σ res ld ls lh oc L (j + 1)) (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L (tailOf pF.1 pF.2) (g.T2.drop (j + 1)) = g.F)
    (hc32 : StrLoc σ fr 32 (sub (fixStr (g.T2.getD j []) 1000) 0 16))
    (h17 : fr.get 17 = some (.long crJmp)) (h21 : fr.get 21 = some (.long total)) (htot : TotOk total)
    (hc1 : 1 ≤ crJmp.toInt) (hle : crJmp.toInt ≤ L.cr.toInt) (hn : crJmp.toInt + n = L.cr.toInt + 1)
    (hpF : cardsFrom L.m L.trct L.cr (sub (fixStr (g.T2.getD j []) 1000) 0 16) n crJmp (oc, total) = pF)
    (hM : memRd L.m (cardOffJ crJmp).toInt 16 = card)
    (hcard : sub (fixStr (g.T2.getD j []) 1000) 0 16 = card)
    (hxm : σ.heap xm = some (.str card)) (hxc : σ.heap xc = some (.str card))
    (hcond : ¬ 0 < (ebcCmp (argText σ (.ref xm)) (argText σ (.ref xc))).bmod 4294967296)
    (hv : v = trctGet L.trct crJmp)
    (hfr : FrT fr fr') (e17 : fr'.get 17 = fr.get 17) (e32 : fr'.get 32 = fr.get 32)
    (e19 : fr'.get 19 = some v) (e22 : fr'.get 22 = some (.long 1)) :
    inv179 g args σ0 fr' σ := by
  rw [argText_ref hxm, argText_ref hxc, ebcCmp_bmod] at hcond
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hLB := xctx_ldBounded hX
  obtain ⟨cnt, hcnt, hc0, hc9⟩ := trctGet_bounded crJmp hLB.2.2.2.2
  have h3 : sub (fixStr (g.T2.getD j []) 1000) 0 16 = memRd L.m (cardOffJ crJmp).toInt 16 := by
    rw [hM, hcard]
  have h2 : ¬ 0 < ebcCmp (memRd L.m (cardOffJ crJmp).toInt 16) (sub (fixStr (g.T2.getD j []) 1000) 0 16) := by
    rw [hM, hcard]; exact hcond
  rw [cardsFrom_match (by omega) h2 h3 hcnt] at hpF
  obtain ⟨xc', hx1, hx2⟩ := hc32
  have e1 : (1 : I64).toInt = 1 := i64_one_toInt
  refine ⟨res, ld, ls, lh, L, oc, j, crJmp, total, n' + 1, pF, cnt, 1, (oc, total),
    xctx_frameT hX hfr (keepsRes_of_grows (grows_refl σ)) (xctx_resAtL hX) rfl rfl, hj, hmodel,
    ⟨xc', e32.trans hx1, hx2⟩, e17.trans h17, (hfr.get 21).trans h21, htot, hc1, hle, hn,
    by rw [e19, hv, hcnt], hcnt, e22, by omega, by omega, ?_, by simpa using hpF⟩
  rw [e1]
  rfl

end EquivLean.Modernize.Cbstm03a.Java.Seg5
