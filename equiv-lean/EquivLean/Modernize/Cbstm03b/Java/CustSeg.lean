import EquivLean.Modernize.Cbstm03b.Java.CustMac

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.CustP

-- The loop invariant at statement 49 or 53, against the precondition's facts: the objects of the entry heap that
-- the loop reads, in the current heap.
set_option hygiene false in
macro "cust_loop_facts" : tactic => `(tactic| (
  obtain rfl : b = opReadK := hop.symm.trans hopK
  rw [hopen'] at hopen
  have hstσ : σ.heap st = some (.plain "Cbstm03b$State" fs) := by rw [hfr st hlt_st hsx]; exact hst
  have hqσ : σ.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq) := by rw [hfr q hlt_q hqx]; exact hq
  have hoσ : σ.heap o1 = some (.plain "Cbstm03b$CustFile" fs1) := by rw [hfr o1 hlt_o1 hox]; exact ho1
  have hlσ : σ.heap l = some (.array et xs) := by rw [hfr l hlt_l (Ne.symm hxl')]; exact hl
  have hi1 : σ.initOf "Cbstm03b" = .done := by rw [State.initOf_eq_of_inits hinits]; exact i1
  have hi8 : σ.initOf "Cbstm03b$FdCustfileRec" = .done := by rw [State.initOf_eq_of_inits hinits]; exact i8
  have hlt_stσ := State.lt_next_of_heap hstσ
  have hlt_qσ := State.lt_next_of_heap hqσ
  have hlt_oσ := State.lt_next_of_heap hoσ
  have hlt_xσ := State.lt_next_of_heap hxrσ
  have hlt_k9 := State.lt_next_of_heap hk9
  have hk9s : k9 ≠ st := ne_of_heap hk9 hstσ (by intro h; cases h)
  have hk9q : k9 ≠ q := ne_of_heap hk9 hqσ (by intro h; cases h)
  have hk9o : k9 ≠ o1 := ne_of_heap hk9 hoσ (by intro h; cases h)
  have hk9x : k9 ≠ xr := ne_of_heap hk9 hxrσ (by intro h; cases h)
  have hkσ : Keeps (A4 st q o1 xr) σ0 σ := keeps_of_frame hn hfr
  have hkept2 := Kept.intro (And.intro hkσ (And.intro hnm (And.intro hfr (And.intro hn (And.intro hop
    (And.intro hopen' (And.intro hxrσ (And.intro hk9 (And.intro hinits (And.intro hf0 (And.intro hf1
    (And.intro hf3 (And.intro hf6 (And.intro hf8 hxsl))))))))))))))
  clear hkσ hnm hfr hA' ha hE))

set_option hygiene false in
macro "cust_loop_kept" : tactic => `(tactic|
  obtain ⟨hkσ, hnm, hfr, hn', hopK', hopen'', hxrσ', hk9', hinits', hf0', hf1', hf3', hf6', hf8', hxsl'⟩ :=
    Kept.elim hkept2)

-- A frame lookup: the locals written since the cut point, then the cut point's.
macro "cfr" : tactic => `(tactic| first | assumption | ((simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte]) <;> first | assumption | rfl | decide))

attribute [local irreducible] EquivLean.Cobol.Rec.JRecAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 20000000 in
set_option jimple.modelContracts true in
theorem cust_seg49 (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddCust oe st q opv oeM s a).pre args σ0) (fr : Frame) (σ : State)
    (hInv : Inv49 st q s a args σ0 fr σ) :
    custWP oe st q opv oeM s a args σ0 49 fr σ := by
  cust_destruct
  unfold Inv49 at hInv
  obtain ⟨fs', c, xr', k9, fsX', i, hst', hc', hxr', hxrh', hf0, hf1, hf3, hf6, hf8, hn, hfr, hxrσ, hk9, hinits,
    hi, hnm, hopK, hopen'⟩ := hInv
  rw [hst] at hst'
  cases hst'
  rw [g1] at hc'
  cases hc'
  rw [k1] at hxr'
  cases hxr'
  rw [hxr] at hxrh'
  cases hxrh'
  cust_loop_facts
  have hkept5 := Kept.intro hi
  rcases Nat.lt_or_ge i xs.length with hlt | hge
  · have hkept6 := Kept.intro hlt
    simp only [custWP_def]
    jvc [ite_nat_ne, custInvG, custCalleesF, Contracts.env, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
    all_goals cust_loop_kept
    all_goals have hlt' := Kept.elim hkept6
    unfold Inv53
    exact ⟨fs, o1, xr, k9, fsx, fs1, l, i, hst, g1, k1, hxr, ho1, hrecs, by cfr, by cfr, by cfr, by cfr, by cfr,
      by cfr, hn', hfr, hxrσ', hk9', hinits', hxsl' ▸ hlt', hnm, hopK', hopen''⟩
  · have hil : i = s.cust.recs.length := by
      have := Kept.elim hkept5
      omega
    have hf : s.cust.recs.findIdx? (fun x => Model.strOf (x.getD 0 default) == key9 a) = none := by
      obtain ⟨-, hnm, -⟩ := Kept.elim hkept2
      rw [hil] at hnm
      exact findIdx_none hnm
    simp only [custWP_def, procSpecG, Spec.of, callC_read23 hdd hop hopen' hf]
    jvc [ite_nat_ne, custInvG, custCalleesF, Contracts.env, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
    all_goals cust_loop_kept
    all_goals cust_kept
    · refine finC_ex hS hst (by keeps4_tac) (away4 hst hq ho1 hxr (by decide)) ?_
      chsimp
      refine ⟨_, rfl, fun k h1 h2 => get_set_other h1,
        ⟨_, (get_set_other (by decide)).trans g1, fileC_same m1 ho1 (by keeps4_tac)
          (away4 (cs := []) hst hq ho1 hxr (by decide)) (rec4 hst hq ho1 (nr_of_sep hsep hst g1 k1))
          (by chsimp; exact hfr o1 hlt_o1 hox)⟩,
        ⟨_, (get_set_other (by decide)).trans k1, ?_⟩,
        ⟨_, get_set_same, _, rfl, ?_⟩⟩
      · rw [hcr]
        simp only [List.set_cons_zero]
        exact custRecAt_mk (fs := Fields.set fsx ("Cbstm03b$FdCustfileRec", "fdCustId") (.ref k9))
          (by chsimp; exact hxrσ') get_set_same ⟨k9, rfl, by chsimp; exact hk9'⟩
          ((get_set_other (by decide)).trans gcd)
          (jstrAt_keeps (by keeps4_tac) (away4 (cs := []) hst hq ho1 hxr (by decide)) jcd)
      · rw [status_text]
        chsimp
        cstatus_close
    · refine sepC hS hsep hst (by keeps4_tac) (away4 hst hq ho1 hxr (by decide)) (by chsimp; try rfl)
        (by cfields_close) (by cfields_close) (fun x y hx hy => ?_)
      simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte] at hx hy
      rw [k1] at hx
      rw [g1] at hy
      cases hx
      cases hy
      exact notRecOf_tr ho1 (by chsimp; rw [hfr o1 hlt_o1 hox]; exact ho1) rfl hrecs
        (by chsimp; exact hfr l hlt_l (Ne.symm hxl')) (nr_of_sep hsep hst g1 k1)
    · refine area_rc hA hVa hq (by keeps4_tac) (away4 (cs := []) hst hq ho1 hxr (by decide)) (by chsimp; try rfl)
        (fun k h => get_set_other h) get_set_same ⟨_, rfl, ?_⟩
      rw [stBytes_text]
      chsimp
      cstatus_close

end EquivLean.Modernize.Cbstm03b.Java.CustP
