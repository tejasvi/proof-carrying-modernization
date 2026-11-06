import EquivLean.Modernize.Cbstm03b.Java.CustSeg

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.CustP

theorem ofNat_succ32 (i : Nat) : BitVec.ofNat 32 i + 1#32 = BitVec.ofNat 32 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

-- The heap after the last statements, which update only the State object and the area.
macro "keepsB_tac" : tactic => `(tactic| repeat (first | exact keeps_refl _ _ | (refine keeps_setObj' ?_ (by simp)) | (refine keeps_alloc' ?_) | (refine keeps_grows' ?_ (growsK_elim (by assumption)))))

attribute [local irreducible] EquivLean.Cobol.Rec.JRecAt fixStr CardDemo.Cbstm03b.intoBuf
  EquivLean.Cobol.Rec.Schema.encode

set_option maxRecDepth 8000 in
set_option maxHeartbeats 20000000 in
set_option jimple.modelContracts true in
set_option jimple.hypHeapFacts true in
theorem cust_seg80 (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddCust oe st q opv oeM s a).pre args σ0) (fr : Frame) (σ : State)
    (hInv : Inv80 st q s a args σ0 fr σ) :
    custWP oe st q opv oeM s a args σ0 80 fr σ := by
  cust_destruct
  unfold Inv80 at hInv
  obtain ⟨fs', fs1', fsq', fsr, c, xr', rx, xn, x00, xid, xdat, i, rid, rdat, hst', hc', hxr', hoc', hqc', hrx, grid,
    grdat, hxid, hxdat, hrxx, hridl, hrdatl, hgetD, hi, hfind, hopK, hopen', hf0, hf3, hf5, hf9, hx00, hxn, hxnσ, hfr,
    hstσ, hcσ, hxnobj, hx00σ, hinits⟩ := hInv
  rw [hst] at hst'
  cases hst'
  rw [g1] at hc'
  cases hc'
  rw [k1] at hxr'
  cases hxr'
  rw [ho1] at hoc'
  cases hoc'
  rw [hq] at hqc'
  cases hqc'
  obtain rfl : b = opReadK := hop.symm.trans hopK
  have hrxo : rx ≠ o1 := ne_of_cls hrx ho1 (by decide)
  have hrxs : rx ≠ st := ne_of_cls hrx hst (by decide)
  have hqσ : σ.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq) := by rw [hfr q hlt_q hqx hqo hsq.symm]; exact hq
  have hrxσ : σ.heap rx = some (.plain "Cbstm03b$FdCustfileRec" fsr) := by
    rw [hfr rx (State.lt_next_of_heap hrx) hrxx hrxo hrxs]; exact hrx
  have hidσ : σ.heap xid = some (.str (cp037Str rid)) := by
    rw [hfr xid (State.lt_next_of_heap hxid) (ne_of_heap hxid hxr (by intro h; cases h))
      (ne_of_heap hxid ho1 (by intro h; cases h)) (ne_of_heap hxid hst (by intro h; cases h))]
    exact hxid
  have hdatσ : σ.heap xdat = some (.str (cp037Str rdat)) := by
    rw [hfr xdat (State.lt_next_of_heap hxdat) (ne_of_heap hxdat hxr (by intro h; cases h))
      (ne_of_heap hxdat ho1 (by intro h; cases h)) (ne_of_heap hxdat hst (by intro h; cases h))]
    exact hxdat
  have hi1 : σ.initOf "Cbstm03b" = .done := by rw [State.initOf_eq_of_inits hinits]; exact i1
  have hfx1 : fixStr (cp037Str rid) 9 = cp037Str rid := fixStr_eq_self (by rw [cp037Str_length]; exact hridl)
  have hfx2 : fixStr (cp037Str rdat) 491 = cp037Str rdat :=
    fixStr_eq_self (by rw [cp037Str_length]; exact hrdatl)
  have hidl : (cp037Str rid).length < 2147483648 := by rw [cp037Str_length]; omega
  have hdatl : (cp037Str rdat).length < 2147483648 := by rw [cp037Str_length]; omega
  have hcatl : (cp037Str rid ++ cp037Str rdat).length < 2147483648 := by
    rw [List.length_append, cp037Str_length, cp037Str_length]; omega
  have hkσ : Keeps (A4 st q o1 xr) σ0 σ :=
    ⟨Nat.le_of_lt (Nat.lt_trans (Nat.lt_of_le_of_lt hx00 hxn) hxnσ), fun y hy hA =>
      hfr y hy (fun e => hA (Or.inr (Or.inr (Or.inr e)))) (fun e => hA (Or.inr (Or.inr (Or.inl e))))
        (fun e => hA (Or.inl e))⟩
  have hkept2 := Kept.intro (And.intro hkσ (And.intro hfr (And.intro hstσ (And.intro hcσ (And.intro hxnobj
    (And.intro hx00σ (And.intro hgetD (And.intro hi (And.intro hidσ (And.intro hdatσ (And.intro hx00
    (And.intro hxn (And.intro hridl hrdatl)))))))))))))
  have hid_q : xid ≠ q := ne_of_heap hxid hq (by intro h; cases h)
  have hid_s : xid ≠ st := ne_of_heap hxid hst (by intro h; cases h)
  have hdat_q : xdat ≠ q := ne_of_heap hxdat hq (by intro h; cases h)
  have hdat_s : xdat ≠ st := ne_of_heap hxdat hst (by intro h; cases h)
  have hlt_id := State.lt_next_of_heap hidσ
  have hlt_dat := State.lt_next_of_heap hdatσ
  have hn0 : σ0.next ≤ σ.next := Nat.le_of_lt (Nat.lt_trans (Nat.lt_of_le_of_lt hx00 hxn) hxnσ)
  clear hA' ha hE
  simp only [custWP_def, procSpecG, Spec.of, callC_read00 hdd hop hopen' hfind]
  jvc [ite_nat_ne, custInvG, custCalleesF, Contracts.env, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
  · exact Or.inr ⟨xid, _, rfl, hidσ, hidl⟩
  · exact Or.inr ⟨xdat, _, rfl, by rw [(growsK_elim ‹GrowsK σ _›).2 xdat hlt_dat]; exact hdatσ, hdatl⟩
  · exact Or.inr ⟨_, _, rfl, by chsimp; try rfl, by simp only [List.length_append, fixStr_length]; decide⟩
  all_goals obtain ⟨hkσ, -⟩ := Kept.elim hkept2
  all_goals cust_kept
  all_goals (have hri : s.cust.recs[i] = [.str rid, .str rdat] := (by rw [← hgetD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]))
  all_goals (have hwq : w ≠ q := (by rcases ‹_ ≤ w ∨ _ = w› with h | h <;> jdisch))
  all_goals (have hws : w ≠ st := (by rcases ‹_ ≤ w ∨ _ = w› with h | h <;> jdisch))
  all_goals (have hxn_s : xn ≠ st := Nat.ne_of_gt (Nat.lt_of_lt_of_le hlt_st (Nat.le_of_lt (Nat.lt_of_le_of_lt hx00 hxn))))
  all_goals (have hxn_q : xn ≠ q := Nat.ne_of_gt (Nat.lt_of_lt_of_le hlt_q (Nat.le_of_lt (Nat.lt_of_le_of_lt hx00 hxn))))
  all_goals (have hx00_s : x00 ≠ st := Nat.ne_of_gt (Nat.lt_of_lt_of_le hlt_st hx00))
  all_goals (have hx00_q : x00 ≠ q := Nat.ne_of_gt (Nat.lt_of_lt_of_le hlt_q hx00))
  all_goals (have hlσ : σ.heap l = some (.array et xs) := (by rw [hfr l hlt_l hxl'.symm hol'.symm hsl.symm]; exact hl))
  all_goals (have hdat2 : ∀ σb, GrowsK σ σb → σb.heap xdat = some (.str (cp037Str rdat)) := fun σb hg => ((growsK_elim hg).2 xdat hlt_dat).trans hdatσ)
  · refine finC_ex hS hst (by keeps4_tac) (away4 hst hq ho1 hxr (by decide)) ?_
    chsimp
    refine ⟨_, rfl, fun k h1 h2 => by rw [get_set_other h1, get_set_other h2], ⟨_, by cfields_close, ?_⟩,
      ⟨_, by cfields_close, ?_⟩, ⟨_, get_set_same, _, rfl, ?_⟩⟩
    · exact fileC m1 ho1 (by keeps4_tac) (away4 (cs := []) hst hq ho1 hxr (by decide))
        (rec4 hst hq ho1 (nr_of_sep hsep hst g1 k1))
        (heap_keeps (A := fun y => y = st ∨ y = q) (by keepsB_tac) hcσ
          (fun h => h.elim (fun e => hso e.symm) (fun e => hqo e.symm)))
        (by cfields_close) (by cfields_close)
        (by simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte, ofNat_succ32]) (by jdisch)
        (by cfields_close)
    · rw [hri]
      exact custRecAt_mk (fs := Fields.set (Fields.set newRecFields ("Cbstm03b$FdCustfileRec", "fdCustId") (.ref xid))
          ("Cbstm03b$FdCustfileRec", "fdCustData") (.ref xdat))
        (heap_keeps (A := fun y => y = st ∨ y = q) (by keepsB_tac) hxnobj (fun h => h.elim hxn_s hxn_q))
        (by simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte])
        ⟨xid, rfl, heap_keeps (A := fun y => y = st ∨ y = q) (by keepsB_tac) hidσ (fun h => h.elim hid_s hid_q)⟩
        (by simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte])
        ⟨xdat, rfl, heap_keeps (A := fun y => y = st ∨ y = q) (by keepsB_tac) hdatσ (fun h => h.elim hdat_s hdat_q)⟩
    · rw [status_text]
      refine (heap_keeps (A := fun y => y = st ∨ y = q) (by keepsB_tac) hx00σ
        (fun h => h.elim hx00_s hx00_q)).trans ?_
      cstatus_close
  · refine sepC hS hsep hst (by keeps4_tac) (away4 hst hq ho1 hxr (by decide)) (by chsimp; try rfl)
      (by cfields_close) (by cfields_close) (fun x y hx hy => ?_)
    simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte] at hx hy
    rw [g1] at hy
    cases hx
    cases hy
    exact notRecOf_fresh m1 ho1
      (heap_keeps (A := fun y => y = st ∨ y = q) (by keepsB_tac) hcσ
        (fun h => h.elim (fun e => hso e.symm) (fun e => hqo e.symm)))
      (by cfields_close) hrecs
      ((heap_keeps (A := fun y => y = st ∨ y = q) (by keepsB_tac) hlσ
        (fun h => h.elim (fun e => hsl e.symm) (fun e => hql e.symm))).trans hl.symm)
      (Nat.le_of_lt (Nat.lt_of_le_of_lt hx00 hxn))
  · refine area_rc_fldt hA hVa hq (by keeps4_tac) (away4 (cs := []) hst hq ho1 hxr (by decide))
      (by chsimp; try rfl) (fun k h1 h2 => by rw [get_set_other h1, get_set_other h2]) get_set_same ⟨_, rfl, ?_⟩
      (by rw [get_set_other (by decide), get_set_same]) ⟨w, rfl, ?_⟩
    · rw [stBytes_text]
      refine (heap_keeps (A := fun y => y = st ∨ y = q) (by keepsB_tac) hx00σ
        (fun h => h.elim hx00_s hx00_q)).trans ?_
      cstatus_close
    · rw [hri, encode_cust, intoBuf_text (by rw [List.length_append, hridl, hrdatl]; decide), cp037Str_append]
      chsimp
      refine (‹_ = some (Obj.str (fixStr _ 1000))›).trans ?_
      simp only [argText, strOf, State.heap_alloc, State.next_alloc, ↓reduceIte, Option.getD_some, hidσ,
        hdat2 _ ‹GrowsK σ _›, hfx1, hfx2, if_true, eq_self_iff_true]

end EquivLean.Modernize.Cbstm03b.Java.CustP
